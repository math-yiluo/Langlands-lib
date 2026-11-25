/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Closure of the affine projection-mate locus

Source: Stacks Project, Tag 08EU.
(blueprint: lem-pc-qcqs-projection-mate-affine-locus).
-/

@[expose] public section

universe u w wA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem homological_triangle_comparison
    {C B : Type*} [Category C] [Category B] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [Abelian B]
    {F G : C ⥤ B} [F.IsHomological] [G.IsHomological] (τ : F ⟶ G)
    (T : Pretriangulated.Triangle C) (hT : T ∈ Pretriangulated.distinguishedTriangles)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₂)]
    [IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (τ.app T.obj₃) := by
  let S (H : C ⥤ B) := ComposableArrows.mk₄ (H.map T.mor₁) (H.map T.mor₂)
    (H.map T.mor₃) (H.map (-T.mor₁⟦(1 : ℤ)⟧'))
  have exactS (H : C ⥤ B) [H.IsHomological] : (S H).Exact := by
    refine ComposableArrows.exact_of_δ₀ ?_ (ComposableArrows.exact_of_δ₀ ?_ ?_)
    · exact (H.map_distinguished_exact T hT).exact_toComposableArrows
    · exact (H.map_distinguished_exact T.rotate
        ((Pretriangulated.rotate_distinguished_triangle T).1 hT)).exact_toComposableArrows
    · exact (H.map_distinguished_exact T.rotate.rotate
        ((Pretriangulated.rotate_distinguished_triangle _).1
          ((Pretriangulated.rotate_distinguished_triangle T).1 hT))).exact_toComposableArrows
  let φ : S F ⟶ S G := ComposableArrows.homMk₄
    (τ.app _) (τ.app _) (τ.app _) (τ.app _) (τ.app _)
    (τ.naturality _) (τ.naturality _) (τ.naturality _) (τ.naturality _)
  apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (exactS F) (exactS G) φ
  all_goals dsimp [φ]; infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem triangulated_triangle_comparison
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G)
    (T : Pretriangulated.Triangle C) (hT : T ∈ Pretriangulated.distinguishedTriangles)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₂)]
    [IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (τ.app T.obj₃) := by
  apply isIso_of_yoneda_map_bijective
  intro Z
  let H := preadditiveCoyoneda.obj (Opposite.op Z)
  have h (K : C) [IsIso (τ.app K)] :
      IsIso ((Functor.whiskerRight τ H).app K) := by
    change IsIso (H.map (τ.app K))
    infer_instance
  have := h T.obj₁
  have := h T.obj₂
  have := h (T.obj₁⟦(1 : ℤ)⟧)
  have := h (T.obj₂⟦(1 : ℤ)⟧)
  have : IsIso (H.map (τ.app T.obj₃)) :=
    homological_triangle_comparison (Functor.whiskerRight τ H) T hT
  have : IsIso ((forget AddCommGrpCat).map (H.map (τ.app T.obj₃))) := inferInstance
  exact (isIso_iff_bijective _).1 this

set_option backward.isDefEq.respectTransparency false in
private theorem allshift_triangle
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (α : F ⟶ G)
    (T : Pretriangulated.Triangle C) (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧)) := by
  intro n
  have hshift (K : C) (hK : ∀ m : ℤ, IsIso (α.app (K⟦m⟧))) :
      IsIso (α.app ((K⟦n⟧)⟦(1 : ℤ)⟧)) := by
    exact (NatTrans.isIso_app_iff_of_iso α
      ((shiftFunctorAdd C n (1 : ℤ)).app K)).1 (hK (n + 1))
  have : IsIso (α.app (T⟦n⟧).obj₁) := h₁ n
  have : IsIso (α.app (T⟦n⟧).obj₂) := h₂ n
  have : IsIso (α.app ((T⟦n⟧).obj₁⟦(1 : ℤ)⟧)) := hshift T.obj₁ h₁
  have : IsIso (α.app ((T⟦n⟧).obj₂⟦(1 : ℤ)⟧)) := hshift T.obj₂ h₂
  exact triangulated_triangle_comparison α (T⟦n⟧)
    (Pretriangulated.Triangle.shift_distinguished T hT n)

private theorem allshift_coproduct
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).IsEquivalence]
    {F G : C ⥤ D} (α : F ⟶ G) {I : Type u}
    [PreservesColimitsOfShape (Discrete I) F] [PreservesColimitsOfShape (Discrete I) G]
    (K : I → C) (S : C) (ι : ∀ i, K i ⟶ S) (hc : IsColimit (Cofan.mk S ι))
    (h : ∀ i (n : ℤ), IsIso (α.app ((K i)⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (S⟦n⟧)) := by
  intro n
  let Kn := Discrete.functor K ⋙ shiftFunctor C n
  have happ (j : Discrete I) : IsIso ((Functor.whiskerLeft Kn α).app j) := h j.as n
  have : IsIso (Functor.whiskerLeft Kn α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit Kn α
    ((shiftFunctor C n).mapCocone (Cofan.mk S ι)) (isColimitOfPreserves _ hc)

private theorem pullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (_h : (derivedPullback f).CommShift ℤ), (derivedPullback f).IsTriangulated := by
  obtain ⟨I, hI, hmap, hadd, hlim, hcolim, hres, E, hE, hEmap, hEadd,
    ε, hleft, htri, hε⟩ := derivedPullback_spec f
  exact htri

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_exact (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    ∃ (_h : (tensorRight E).CommShift ℤ), (tensorRight E).IsTriangulated := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M N : GradedObject ℤ C) : M.HasTensor N := inferInstance
  have (M N P R : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt M N P R := inferInstance
  have (M N P : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor M N P := inferInstance
  have (M N P : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ M N P := inferInstance
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.IsLeftDerivabilityStructure := inferInstance
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso E
  let := DerivedCategory.commShiftTensorRightQhObj P hP
  have := DerivedCategory.isTriangulated_tensorRightQhObj P hP
  let eF := (curriedTensor (DerivedCategory C)).flip.mapIso eP
  let := Functor.CommShift.ofIso eF ℤ
  have := Functor.CommShift.ofIso_compatibility eF ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso eF⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def suppliedMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (L : schemeDerivedCategory X) :
    tensorRight ((schemeDerivedDirectImage f).obj L) ⟶
      (derivedPullback f ⋙ tensorRight L) ⋙ schemeDerivedDirectImage f where
  app M := p.homEquiv _ _
    (t.hom.app (M, (schemeDerivedDirectImage f).obj L) ≫
      (𝟙 ((derivedPullback f).obj M) ⊗ₘ p.counit.app L))
  naturality {M N} a := by
    apply p.homEquiv_naturality_left_square
    dsimp
    have h := t.hom.naturality (show (M, (schemeDerivedDirectImage f).obj L) ⟶
      (N, (schemeDerivedDirectImage f).obj L) from (a, 𝟙 _))
    dsimp at h
    simp only [tensorHom_id, Category.assoc] at h ⊢
    rw [← Category.assoc, h, Category.assoc]
    congr 1
    rw [(derivedPullback f).map_id]
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]

variable (A : Type u) [CommRing A]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
  (X : Scheme.{u})
  [CompactSpace X] [QuasiSeparatedSpace X]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
  (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
  (t : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback f ≅
    (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
  (L : schemeDerivedQCohCategory X)
  (e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)))

-- Keep the existing compactness and quasi-separatedness binders in the public signature.
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The all-shifts isomorphism locus of the supplied projection mate is closed
under coproducts, distinguished triangles, and retracts.

Proof: the mate is natural in M by naturality of t and the counit and of the
adjunction Hom equivalence. The two functors in M are exact. On quasi-coherent
objects they preserve coproducts: e is an equivalence, pullback is a left
adjoint, tensor preserves coproducts, and qcqs direct image preserves
quasi-coherent coproducts. The quasi-coherent inclusion preserves these sums.
Shifts preserve coproducts, so a component on a sum is a sum of invertible
components. For a distinguished triangle use every shift of the triangle.
Apply Hom(T,-) to the two image sequences, for each ambient T. Naturality at
the three maps, including the connecting map, gives a diagram of exact
sequences. The five lemma makes the third component invertible when the
first two are invertible; use Yoneda and then every shift. No compatibility
of t with a chosen shift comparison is required: the sequences have vertices
F(K[n]) and the arrows obtained by applying F to the shifted triangle maps.
Naturality transports an isomorphism component along an object isomorphism
and along a retract. The predicate quantifies over all object isomorphisms,
so it is invariant under isomorphism by composition. The zero object and
empty coproduct are included.
Source: Stacks Project, Tag 08EU.
(blueprint: lem-pc-qcqs-projection-mate-affine-locus). -/
theorem qcqsProjectionMate_affineLocus_closed
    (htri : ∃ (_h : (e.functor ⋙
      (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
      (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated) :
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦
    ∀ (M : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ),
      Nonempty ((e.functor.obj (K⟦n⟧)).obj ≅ M.obj) →
      IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
          (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
            (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)));
    (∀ {I : Type u} (F : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, F i ⟶ S),
      IsColimit (Cofan.mk S ι) → (∀ i, P (F i)) → P S) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
    (∀ {K N : DerivedCategory (ModuleCat.{u} A)}, Retract K N → P N → P K) := by
  classical
  let E := e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι
  let τ := suppliedMate f p t L.obj
  let α : (E ⋙ tensorRight ((schemeDerivedDirectImage f).obj L.obj)) ⟶
      E ⋙ ((derivedPullback f ⋙ tensorRight L.obj) ⋙ schemeDerivedDirectImage f) :=
    Functor.whiskerLeft E τ
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K ↦ ∀ n : ℤ, IsIso (α.app (K⟦n⟧))
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦
    ∀ (M : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ),
      Nonempty ((e.functor.obj (K⟦n⟧)).obj ≅ M.obj) →
      IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
          (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
            (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))
  change (∀ {I : Type u} (F : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, F i ⟶ S),
      IsColimit (Cofan.mk S ι) → (∀ i, P (F i)) → P S) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
    (∀ {K N : DerivedCategory (ModuleCat.{u} A)}, Retract K N → P N → P K)
  have hP (K : DerivedCategory (ModuleCat.{u} A)) : P K ↔ Q K := by
    constructor
    · intro h n
      exact h (e.functor.obj (K⟦n⟧)) n ⟨Iso.refl _⟩
    · intro h M n hM
      obtain ⟨i⟩ := hM
      exact (NatTrans.isIso_app_iff_of_iso τ i).1 (h n)
  obtain ⟨sE, hE⟩ := htri
  let : E.CommShift ℤ := sE
  have : E.IsTriangulated := hE
  obtain ⟨sF, hF⟩ := pullback_exact f
  let := sF
  have := hF
  let := p.rightAdjointCommShift ℤ
  have := p.commShift_of_leftAdjoint ℤ
  have := p.isTriangulated_rightAdjoint
  obtain ⟨sY, hY⟩ := tensor_exact (Spec (.of A)) ((schemeDerivedDirectImage f).obj L.obj)
  let := sY
  have := hY
  obtain ⟨sX, hX⟩ := tensor_exact X L.obj
  let := sX
  have := hX
  refine ⟨?_, ?_, ?_⟩
  · intro I F S ι hc h
    apply (hP S).2
    have := derivedAmbientHasCoproducts (Spec (.of A))
    have := schemeDerivedQCohClosedUnderCoproducts (Spec (.of A)) I
    let : (derivedPullback f).IsLeftAdjoint := p.isLeftAdjoint
    have := derivedTensorRight_preservesCoproducts (Spec (.of A))
      ((schemeDerivedDirectImage f).obj L.obj) I
    have := derivedTensorRight_preservesCoproducts X L.obj I
    have : PreservesColimitsOfShape (Discrete I) E := by
      dsimp only [E]
      infer_instance
    have : PreservesColimitsOfShape (Discrete I)
        (E ⋙ ((derivedPullback f ⋙ tensorRight L.obj) ⋙ schemeDerivedDirectImage f)) := by
      constructor
      intro D
      let H := D ⋙ (E ⋙ (derivedPullback f ⋙ tensorRight L.obj))
      let V (i : I) : schemeDerivedQCohCategory X :=
        ⟨H.obj ⟨i⟩, canonical_derivedTensor_preserve_QCoh X _ L.obj
          ((derivedPullback_tensor_preserve_QCoh f).1 _
            (e.functor.obj (D.obj ⟨i⟩)).property) L.property⟩
      have : PreservesColimit (Discrete.functor (fun i ↦ (V i).obj))
          (schemeDerivedDirectImage f) := derivedDirectImagePreservesDirectSums f I V
      have : PreservesColimit (Discrete.functor (H.obj ∘ Discrete.mk))
          (schemeDerivedDirectImage f) := by
        change PreservesColimit (Discrete.functor (fun i ↦ (V i).obj)) _
        infer_instance
      have : PreservesColimit H (schemeDerivedDirectImage f) :=
        preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := H)).symm
      change PreservesColimit D
        ((E ⋙ (derivedPullback f ⋙ tensorRight L.obj)) ⋙ schemeDerivedDirectImage f)
      infer_instance
    exact allshift_coproduct α F S ι hc (fun i ↦ (hP (F i)).1 (h i))
  · intro T hT h₁ h₂
    apply (hP T.obj₃).2
    exact allshift_triangle α T hT ((hP T.obj₁).1 h₁) ((hP T.obj₂).1 h₂)
  · intro K N r h
    apply (hP K).2
    intro n
    have hn : IsIso (α.app (N⟦n⟧)) := (hP N).1 h n
    exact (MorphismProperty.isomorphisms _).of_retract
      (α.retractArrowApp (r.map (shiftFunctor _ n))) hn

end AlgebraicGeometry
