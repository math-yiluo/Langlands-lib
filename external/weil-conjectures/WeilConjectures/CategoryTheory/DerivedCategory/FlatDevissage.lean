/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Dévissage tools for natural transformations out of derived categories

Let `τ : F ⟶ G` be a natural transformation, compatible with the shifts, between triangulated
functors. This file collects tools to show that `τ` is an isomorphism at an object by reducing
to simpler objects.

* `DerivedCategory.isIso_homologyFunctor_map_app_obj₂_of_obj₁` and
  `DerivedCategory.isIso_homologyFunctor_map_app_obj₂_of_obj₃`: comparison of `Hᵠ(τ)` along a
  distinguished triangle whose third (resp. first) term has vanishing images in the relevant
  degrees.
* `DerivedCategory.isIso_app_of_isGE`: if `F` and `G` do not lower the cohomological degree and
  `τ` is an isomorphism at the objects of `C` placed in degree `0`, then `τ` is an isomorphism at
  every bounded below object.
* `DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop`: if `τ` is an
  isomorphism at the objects of `C` satisfying `P`, placed in degree `0`, then it is an
  isomorphism at every strictly bounded complex whose terms satisfy `P` (by the stupid truncations).
* `CochainComplex.kFlat_mapHomologicalComplex_obj_stupidTruncGE`: if a functor `G` preserving
  flat objects sends a complex `K` of flat objects to a K-flat complex, it also sends the stupid
  truncations `σ^{≥ n} K` to K-flat complexes.
* `DerivedCategory.isGE_Q_obj_tensor_of_kFlat`: the derived tensor product of a K-flat complex
  concentrated in degrees `≥ c` with an object concentrated in degrees `≥ d` is concentrated in
  degrees `≥ c + d`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Pretriangulated

universe w v u

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- A property of objects containing zero and closed under isomorphisms which holds for all the
terms of a complex holds for all the terms of its stupid truncations. -/
lemma prop_stupidTrunc_X (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] (hK : ∀ n, P (K.X n))
    (n : ι') : P ((K.stupidTrunc e).X n) := by
  by_cases h : ∃ i, e.f i = n
  · obtain ⟨i, hi⟩ := h
    exact P.prop_of_iso (K.stupidTruncXIso e hi).symm (hK _)
  · exact P.prop_of_isZero (K.isZero_stupidTrunc_X e n (by simpa using h))

end HomologicalComplex

namespace DerivedCategory

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]

section Homology

variable {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive] [Pretriangulated T]
  {F G : T ⥤ DerivedCategory D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G)

/-- Let `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a distinguished triangle such that the images of `X₃` under
`F` and `G` have vanishing homology in degrees `q - 1` and `q`. If `Hᵠ(τ)` is an isomorphism at
`X₁`, it is an isomorphism at `X₂`. -/
lemma isIso_homologyFunctor_map_app_obj₂_of_obj₁ (Tr : Triangle T) (hT : Tr ∈ distTriang T)
    (q : ℤ) (hF₀ : IsZero ((homologyFunctor D (q - 1)).obj (F.obj Tr.obj₃)))
    (hF₁ : IsZero ((homologyFunctor D q).obj (F.obj Tr.obj₃)))
    (hG₀ : IsZero ((homologyFunctor D (q - 1)).obj (G.obj Tr.obj₃)))
    (hG₁ : IsZero ((homologyFunctor D q).obj (G.obj Tr.obj₃)))
    (h : IsIso ((homologyFunctor D q).map (τ.app Tr.obj₁))) :
    IsIso ((homologyFunctor D q).map (τ.app Tr.obj₂)) := by
  have h₁ : IsIso ((homologyFunctor D q).map (F.map Tr.mor₁)) :=
    isIso_homologyMap_mor₁ _ (F.map_distinguished _ hT) (q - 1) q (by lia) hF₀ hF₁
  have h₂ : IsIso ((homologyFunctor D q).map (G.map Tr.mor₁)) :=
    isIso_homologyMap_mor₁ _ (G.map_distinguished _ hT) (q - 1) q (by lia) hG₀ hG₁
  have hc := (homologyFunctor D q).congr_map (τ.naturality Tr.mor₁)
  simp only [Functor.map_comp] at hc
  have : IsIso ((homologyFunctor D q).map (F.map Tr.mor₁) ≫
      (homologyFunctor D q).map (τ.app Tr.obj₂)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_left ((homologyFunctor D q).map (F.map Tr.mor₁)) _

/-- Let `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a distinguished triangle such that the images of `X₁` under
`F` and `G` have vanishing homology in degrees `q` and `q + 1`. If `Hᵠ(τ)` is an isomorphism at
`X₃`, it is an isomorphism at `X₂`. -/
lemma isIso_homologyFunctor_map_app_obj₂_of_obj₃ (Tr : Triangle T) (hT : Tr ∈ distTriang T)
    (q : ℤ) (hF₀ : IsZero ((homologyFunctor D q).obj (F.obj Tr.obj₁)))
    (hF₁ : IsZero ((homologyFunctor D (q + 1)).obj (F.obj Tr.obj₁)))
    (hG₀ : IsZero ((homologyFunctor D q).obj (G.obj Tr.obj₁)))
    (hG₁ : IsZero ((homologyFunctor D (q + 1)).obj (G.obj Tr.obj₁)))
    (h : IsIso ((homologyFunctor D q).map (τ.app Tr.obj₃))) :
    IsIso ((homologyFunctor D q).map (τ.app Tr.obj₂)) := by
  have h₁ : IsIso ((homologyFunctor D q).map (F.map Tr.mor₂)) :=
    isIso_homologyMap_mor₂ _ (F.map_distinguished _ hT) q (q + 1) rfl hF₀ hF₁
  have h₂ : IsIso ((homologyFunctor D q).map (G.map Tr.mor₂)) :=
    isIso_homologyMap_mor₂ _ (G.map_distinguished _ hT) q (q + 1) rfl hG₀ hG₁
  have hc := (homologyFunctor D q).congr_map (τ.naturality Tr.mor₂)
  simp only [Functor.map_comp] at hc
  have : IsIso ((homologyFunctor D q).map (τ.app Tr.obj₂) ≫
      (homologyFunctor D q).map (G.map Tr.mor₂)) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((homologyFunctor D q).map (G.map Tr.mor₂))

end Homology

section BoundedBelow

variable {F G : DerivedCategory C ⥤ DerivedCategory D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- If `F` and `G` do not lower the cohomological degree and `τ` is an isomorphism at the objects
of `C` placed in degree `0`, then `τ` is an isomorphism at every bounded below object: in a fixed
degree `q`, both sides only depend on the truncation `τ^{≤ q} X`, which is bounded. -/
lemma isIso_app_of_isGE
    (hF : ∀ (X : DerivedCategory C) (n : ℤ), X.IsGE n → (F.obj X).IsGE n)
    (hG : ∀ (X : DerivedCategory C) (n : ℤ), X.IsGE n → (G.obj X).IsGE n)
    (h : ∀ Y : C, IsIso (τ.app ((singleFunctor C 0).obj Y)))
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] : IsIso (τ.app X) := by
  rw [isIso_iff]
  intro q
  by_cases hq : q < n
  · have := hF X n inferInstance
    have := hG X n inferInstance
    exact ⟨⟨0, (isZero_of_isGE _ n q hq).eq_of_src _ _, (isZero_of_isGE _ n q hq).eq_of_src _ _⟩⟩
  · have hT := TStructure.t.triangleLTGE_distinguished (q + 1) X
    have h₃F := hF ((TStructure.t.truncGE (q + 1)).obj X) (q + 1) inferInstance
    have h₃G := hG ((TStructure.t.truncGE (q + 1)).obj X) (q + 1) inferInstance
    refine isIso_homologyFunctor_map_app_obj₂_of_obj₁ τ _ hT q
      (isZero_of_isGE _ (q + 1) _ (by lia) (hX := h₃F))
      (isZero_of_isGE _ (q + 1) _ (by lia) (hX := h₃F))
      (isZero_of_isGE _ (q + 1) _ (by lia) (hX := h₃G))
      (isZero_of_isGE _ (q + 1) _ (by lia) (hX := h₃G)) ?_
    have : IsIso (τ.app ((TStructure.t.triangleLTGE (q + 1)).obj X).obj₁) := by
      refine prop_of_bounded τ.isoLocus ⊤ (fun Y _ ↦ h Y) _ ⟨⟨n, ?_⟩, ⟨q, ?_⟩⟩
        (fun _ ↦ trivial)
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT (q + 1)).obj X) n)
      · exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncLT (q + 1)).obj X) q)
    infer_instance

end BoundedBelow

section Bounded

variable {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive] [Pretriangulated T]
  {F G : DerivedCategory C ⥤ T} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- If `τ` is an isomorphism at the objects of `C` satisfying `P`, placed in degree `0`, then it
is an isomorphism at every strictly bounded complex whose terms satisfy `P`: by induction along
the stupid truncations (`HomotopyCategory.mem_subcategory_of_strictly_bounded`). -/
lemma isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop (P : ObjectProperty C)
    (hP : ∀ Y, P Y → IsIso (τ.app ((singleFunctor C 0).obj Y)))
    (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, P (K.X n)) : IsIso (τ.app (Q.obj K)) := by
  have hK' := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (Functor.whiskerLeft Qh τ).isoLocus K a b fun n _ _ ↦
      (NatTrans.isIso_app_iff_of_iso τ ((singleFunctorIsoCompQh C 0).app (K.X n))).1
        (hP _ (hK n))
  rw [NatTrans.isoLocus_iff, Functor.whiskerLeft_app] at hK'
  exact (NatTrans.isIso_app_iff_of_iso τ ((quotientCompQhIso C).app K)).1 hK'

end Bounded

end DerivedCategory

section Flat

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

namespace CochainComplex

variable {D : Type*} [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]

omit [Abelian.HasFunctorialFlatResolution C] in
/-- Let `G` be an additive functor preserving flat objects and `K` a complex of flat objects such
that `G(K)` is K-flat. Then `G(σ^{≥ n + 1} K)` is K-flat: it is the fiber of the degreewise split
epimorphism `G(K) ⟶ G(σ^{≤ n} K)`, whose target is a bounded above complex of flat objects. -/
lemma kFlat_mapHomologicalComplex_obj_stupidTruncGE (G : C ⥤ D) [G.Additive] [G.PreservesFlat]
    (K : CochainComplex C ℤ) (hK : ∀ i, ObjectProperty.flat (K.X i))
    (hGK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((G.mapHomologicalComplex _).obj K))
    (n : ℤ) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((G.mapHomologicalComplex _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1)))) := by
  have ac := ComplexShape.Embedding.embeddingUpInt_areComplementary n (n + 1) rfl
  have σ (i : ℤ) : (((K.shortComplexStupidTrunc ac).map (G.mapHomologicalComplex _)).map
      (HomologicalComplex.eval D _ i)).Splitting :=
    ((K.shortComplexStupidTruncSplitting ac i).map G).ofIso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  have hT := HomotopyCategory.trianglehOfDegreewiseSplit_distinguished _ σ
  have h₂ : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((HomotopyCategory.quotient D (.up ℤ)).obj ((G.mapHomologicalComplex _).obj K)) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hGK
  have : IsStrictlyLE ((G.mapHomologicalComplex _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntLE n))) n :=
    (isStrictlyLE_iff _ n).2 fun i hi ↦ G.map_isZero (isZero_of_isStrictlyLE _ n i hi)
  have h₃ : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((HomotopyCategory.quotient D (.up ℤ)).obj ((G.mapHomologicalComplex _).obj
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE n)))) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 (kFlat_of_isStrictlyLE_of_flat _ n
      fun i ↦ Functor.PreservesFlat.flat_obj (F := G)
        (HomologicalComplex.prop_stupidTrunc_X _ K _ hK i))
  have h₁ := (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₁ _ hT h₂ h₃
  exact (HomotopyCategory.kFlat_quotient_obj_iff _).1 h₁

omit [Abelian.HasFunctorialFlatResolution C] in
/-- If `K` is a K-flat complex of flat objects, its stupid truncations `σ^{≥ n + 1} K` are
K-flat. -/
lemma kFlat_stupidTruncGE (K : CochainComplex C ℤ) (hK : ∀ i, ObjectProperty.flat (K.X i))
    (hKk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) (n : ℤ) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1))) := by
  have : (𝟭 C).PreservesFlat := ⟨id⟩
  have h := kFlat_mapHomologicalComplex_obj_stupidTruncGE (𝟭 C) K hK
    (ObjectProperty.prop_of_iso _ ((Functor.mapHomologicalComplexIdIso C _).app K).symm hKk) n
  exact ObjectProperty.prop_of_iso _ ((Functor.mapHomologicalComplexIdIso C _).app _) h

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

/-- The derived tensor product of a K-flat complex concentrated in degrees `≥ c` with an object
concentrated in degrees `≥ d` is concentrated in degrees `≥ c + d`: it is computed by the tensor
product of complexes. -/
lemma isGE_Q_obj_tensor_of_kFlat (R : CochainComplex C ℤ)
    (hR : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat R) (c : ℤ) [R.IsStrictlyGE c]
    (Y : DerivedCategory C) (d : ℤ) [Y.IsGE d] : (Q.obj R ⊗ Y).IsGE (c + d) := by
  obtain ⟨L, _, ⟨e⟩⟩ := Y.exists_iso_Q_obj_of_isGE d
  have := CochainComplex.isStrictlyGE_tensorObj R L c d
  exact TStructure.t.isGE_of_iso
    (whiskerLeftIso (Q.obj R) e ≪≫ QObjTensorQObjIsoOfKFlatLeft R L hR).symm _

end DerivedCategory

end Flat
