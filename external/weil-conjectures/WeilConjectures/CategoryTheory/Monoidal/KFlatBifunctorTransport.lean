/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Transporting K-flatness along functors compatible with a bifunctor

Let `G : A ⥤ A ⥤ A` be an additive bifunctor on an abelian category `A`, `D` an abelian
monoidal category and `R : A ⥤ D` an additive functor preserving the coproducts defining total
complexes, together with a natural isomorphism `τ : R (G X Y) ≅ R X ⊗ R Y`.

* `CategoryTheory.Functor.mapBifunctorTensorIso`: the induced isomorphism of complexes
  `R (G(K, L)) ≅ R K ⊗ R L` for the total complexes.
* `CategoryTheory.Functor.quasiIso_mapBifunctorMap_of_kFlat`: if `R` is exact and reflects
  isomorphisms and `R P` is K-flat, then the total `G`-complex with `P` (on either side) preserves
  quasi-isomorphisms.
* `CategoryTheory.Functor.acyclic_tensor_of_isEquivalence`: if `R` is an equivalence, the
  acyclicity test for `G(-, P)` transfers to the acyclicity test for `- ⊗ R P`.
* `CochainComplex.kFlat_of_acyclic_tensor`: in a braided monoidal abelian category, the
  one-sided acyclicity test implies K-flatness.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [BraidedCategory D]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) D]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- In a braided monoidal abelian category, a complex `P` such that `N ⊗ P` is acyclic for every
acyclic complex `N` is K-flat. -/
theorem kFlat_of_acyclic_tensor (P : CochainComplex D ℤ)
    (hP : ∀ N : CochainComplex D ℤ, N.Acyclic → (N ⊗ P).Acyclic) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨N, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have h := hP N hZ
  exact ⟨(HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic (P ⊗ N)).2
      (fun i ↦ (h i).of_iso (Monoidal.braiding N P)),
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic (N ⊗ P)).2 h⟩

end CochainComplex

namespace CategoryTheory.Functor

section Bifunctor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- For a strong monoidal functor `F`, the inverse tensorators form an isomorphism of bifunctors
`F (X ⊗ Y) ≅ F X ⊗ F Y`. -/
noncomputable def Monoidal.postcomposeCurriedTensorIso [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] :
    (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (Monoidal.μIso F X Y).symm)
    (fun g ↦ by simp)) (fun f ↦ by
      ext Y
      simp)

/-- Composition of comparisons of bifunctors: from `U (G X Y) ≅ G' (U X) (U Y)` and
`E (G' X Y) ≅ H (E X) (E Y)` one obtains `E (U (G X Y)) ≅ H (E (U X)) (E (U Y))`. -/
noncomputable def postcompose₂CompIso {G : A ⥤ A ⥤ A} {G' : B ⥤ B ⥤ B} {H : D ⥤ D ⥤ D}
    {U : A ⥤ B} {E : B ⥤ D}
    (e₁ : (Functor.postcompose₂.obj U).obj G ≅
      (((Functor.whiskeringLeft₂ B).obj U).obj U).obj G')
    (e₂ : (Functor.postcompose₂.obj E).obj G' ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj H) :
    (Functor.postcompose₂.obj (U ⋙ E)).obj G ≅
      (((Functor.whiskeringLeft₂ D).obj (U ⋙ E)).obj (U ⋙ E)).obj H :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ E.mapIso ((e₁.app X).app Y) ≪≫ (e₂.app (U.obj X)).app (U.obj Y))
    (fun g ↦ by
      have h₁ := (e₁.hom.app X).naturality g
      have h₂ := (e₂.hom.app (U.obj X)).naturality (U.map g)
      dsimp at h₁ h₂ ⊢
      rw [Category.assoc, ← h₂, ← E.map_comp_assoc, h₁, E.map_comp_assoc]))
    (fun f ↦ by
      ext Y
      have h₁ := NatTrans.congr_app (e₁.hom.naturality f) Y
      have h₂ := NatTrans.congr_app (e₂.hom.naturality (U.map f)) (U.obj Y)
      dsimp at h₁ h₂ ⊢
      rw [Category.assoc, ← h₂, ← E.map_comp_assoc, h₁, E.map_comp_assoc])

/-- Uncurried comparisons of bifunctors give comparisons of the flipped curried bifunctors:
from `U (T X Y) ≅ T' (U X) (U Y)` one obtains `U (T.flip X Y) ≅ T'.flip (U X) (U Y)`. -/
noncomputable def postcompose₂FlipIsoOfUncurry {T : A ⥤ A ⥤ A} {T' : B ⥤ B ⥤ B} {U : A ⥤ B}
    (e : Functor.uncurry.obj T ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj T') :
    (Functor.postcompose₂.obj U).obj T.flip ≅
      (((Functor.whiskeringLeft₂ B).obj U).obj U).obj T'.flip :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ e.app (Y, X)) (fun g ↦ by
    simpa using e.hom.naturality (X := (_, X)) (Y := (_, X)) (g, 𝟙 X))) (fun f ↦ by
      ext Y
      simpa using e.hom.naturality (X := (Y, _)) (Y := (Y, _)) (𝟙 Y, f))

/-- The flip of a bifunctor which is additive in its second variable is additive. -/
theorem flip_additive [Preadditive B] [Preadditive C] [Preadditive D] (F : B ⥤ C ⥤ D)
    [∀ X, (F.obj X).Additive] : F.flip.Additive where
  map_add {_ _ f g} := by
    ext X
    exact (F.obj X).map_add

/-- The flipped functors of a bifunctor which is additive in its first variable are additive. -/
theorem flip_obj_additive [Preadditive B] [Preadditive C] [Preadditive D] (F : B ⥤ C ⥤ D)
    [F.Additive] (Y : C) : (F.flip.obj Y).Additive where
  map_add {_ _ f g} := by
    simp [F.map_add]

/-- If `e : F ⋙ R₂ ≅ R₁ ⋙ G`, a property of complexes closed under isomorphisms holds for
`R₂ (F P)` as soon as it holds for `G (R₁ P)`. -/
theorem prop_mapHomologicalComplex_obj_of_iso [Preadditive A] [Preadditive B] [Preadditive C]
    [Preadditive D] {F : A ⥤ B} {R₁ : A ⥤ C} {R₂ : B ⥤ D} {G : C ⥤ D} [F.Additive]
    [R₁.Additive] [R₂.Additive] [G.Additive] (e : F ⋙ R₂ ≅ R₁ ⋙ G) {ι : Type*}
    (c : ComplexShape ι) (Q : ObjectProperty (HomologicalComplex D c))
    [Q.IsClosedUnderIsomorphisms] (P : HomologicalComplex A c)
    (h : Q ((G.mapHomologicalComplex c).obj ((R₁.mapHomologicalComplex c).obj P))) :
    Q ((R₂.mapHomologicalComplex c).obj ((F.mapHomologicalComplex c).obj P)) :=
  Q.prop_of_iso ((Functor.mapHomologicalComplexCompIso (Iso.refl (R₁ ⋙ G)) c).app P ≪≫
    (NatIso.mapHomologicalComplex e.symm c).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R₂)) c).app P).symm) h

end Bifunctor

variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {G : A ⥤ A ⥤ A} [G.Additive] [∀ X, (G.obj X).Additive]
  [∀ K L : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor K L G (.up ℤ)]
  {R : A ⥤ D} [R.Additive]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) R]

/-- The isomorphism `R (G(K, L)) ≅ R K ⊗ R L` of total complexes induced by a natural isomorphism
`R (G X Y) ≅ R X ⊗ R Y`. -/
noncomputable def mapBifunctorTensorIso
    (τ : (Functor.postcompose₂.obj R).obj G ≅
      (((Functor.whiskeringLeft₂ D).obj R).obj R).obj (curriedTensor D))
    (K L : CochainComplex A ℤ) :
    (R.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.mapBifunctor K L G (.up ℤ)) ≅
      (R.mapHomologicalComplex (.up ℤ)).obj K ⊗ (R.mapHomologicalComplex (.up ℤ)).obj L :=
  asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) K L)

/-- If `R` is exact and reflects isomorphisms, and `R P` is K-flat, then the total complex of
`G` with `P`, on either side, preserves quasi-isomorphisms. -/
theorem quasiIso_mapBifunctorMap_of_kFlat [R.PreservesHomology] [R.ReflectsIsomorphisms]
    (τ : (Functor.postcompose₂.obj R).obj G ≅
      (((Functor.whiskeringLeft₂ D).obj R).obj R).obj (curriedTensor D))
    (P : CochainComplex A ℤ)
    (hP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((R.mapHomologicalComplex (.up ℤ)).obj P))
    {Q Q' : CochainComplex A ℤ} (s : Q ⟶ Q') (hs : QuasiIso s) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P) s G (.up ℤ)) ∧
      QuasiIso (HomologicalComplex.mapBifunctorMap s (𝟙 P) G (.up ℤ)) := by
  have hRs : HomologicalComplex.quasiIso D (.up ℤ) ((R.mapHomologicalComplex (.up ℤ)).map s) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  constructor
  · rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ R,
      ← quasiIso_iff_comp_right _ (mapBifunctorTensorIso τ P Q').hom]
    have h := hP.whiskerLeft hRs
    rw [HomologicalComplex.mem_quasiIso_iff] at h
    have sq := HomologicalComplex.mapBifunctorComparison_naturality τ.hom (.up ℤ) (𝟙 P) s
    rw [Functor.map_id] at sq
    erw [sq]
    rw [quasiIso_iff_comp_left]
    exact h
  · rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ R,
      ← quasiIso_iff_comp_right _ (mapBifunctorTensorIso τ Q' P).hom]
    have h := hP.whiskerRight hRs
    rw [HomologicalComplex.mem_quasiIso_iff] at h
    have sq := HomologicalComplex.mapBifunctorComparison_naturality τ.hom (.up ℤ) s (𝟙 P)
    rw [Functor.map_id] at sq
    erw [sq]
    rw [quasiIso_iff_comp_left]
    exact h

/-- If `R` is an equivalence, the acyclicity test for the total complexes `G(-, P)` implies the
acyclicity test for `- ⊗ R P`. -/
theorem acyclic_tensor_of_isEquivalence [R.IsEquivalence]
    (τ : (Functor.postcompose₂.obj R).obj G ≅
      (((Functor.whiskeringLeft₂ D).obj R).obj R).obj (curriedTensor D))
    (P : CochainComplex A ℤ)
    (hP : ∀ N : CochainComplex A ℤ, N.Acyclic →
      (HomologicalComplex.mapBifunctor N P G (.up ℤ)).Acyclic)
    (N' : CochainComplex D ℤ) (hN' : N'.Acyclic) :
    (N' ⊗ (R.mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  let E := R.asEquivalence.mapHomologicalComplex (.up ℤ)
  have : R.asEquivalence.functor.Additive := inferInstanceAs R.Additive
  have : R.inv.Additive := R.asEquivalence.inverse_additive
  have hN : (E.inverse.obj N').Acyclic := hN'.map R.inv
  have h := (hP _ hN).map R
  intro i
  exact (h i).of_iso (mapBifunctorTensorIso τ _ P ≪≫ whiskerRightIso (E.counitIso.app N') _)

end CategoryTheory.Functor
