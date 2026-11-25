/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralData
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Flatness detection for finite clopen pro-etale partitions.

Tensoring already preserves finite colimits. Zero insertion, its adjunction with
restriction, and the tensor comparison transport finite-limit preservation to each
component. The gluing equivalence detects the converse componentwise. Reindexing
the finite partition by `Fin n` keeps the prescribed module universe unchanged.

## References

* Stacks Project, Tag 03ER (3)
* Tag 03ER (3)
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

/-- Coordinate restrictions jointly detect preservation of finite limits. -/
private theorem jointlyPreservesFiniteLimits
    {A C : Type*} [Category A] [Category C] {K : Type*}
    {D : K → Type*} [∀ k, Category (D k)]
    (r : C ⥤ ∀ k, D k) [r.IsEquivalence] (T : A ⥤ C)
    (h : ∀ k, PreservesFiniteLimits (T ⋙ r ⋙ Pi.eval D k)) :
    PreservesFiniteLimits T := by
  have : PreservesFiniteLimits (T ⋙ r) := by
    constructor
    intro J _ _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨?_⟩
    have (k : K) : PreservesFiniteLimits (T ⋙ r ⋙ Pi.eval D k) := h k
    refine { lift := fun s k ↦ (isLimitOfPreserves
        (T ⋙ r ⋙ Pi.eval D k) hc).lift ((Pi.eval D k).mapCone s)
             fac := ?_, uniq := ?_ }
    · intro s x
      funext k
      exact (isLimitOfPreserves (T ⋙ r ⋙ Pi.eval D k) hc).fac _ x
    · intro s m hm
      funext k
      exact (isLimitOfPreserves (T ⋙ r ⋙ Pi.eval D k) hc).uniq
        ((Pi.eval D k).mapCone s) (m k) (fun x ↦ congrFun (hm x) k)
  exact preservesFiniteLimits_of_reflects_of_preserves T r

/-- Clopen restriction preserves finite limits since limits of module sheaves are
computed on the underlying additive presheaves. -/
private theorem restrictionPreservesFiniteLimits {X Y : Scheme.{t}}
    (j : Y ⟶ X) [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (clopenModuleRestriction.{t, u, max u (t + 1)} j R) := by
  let Ri := (clopenRingRestriction j).obj R
  let V := SheafOfModules.forget.{max u (t + 1)} Ri ⋙ PresheafOfModules.toPresheaf Ri.obj
  have : PreservesFiniteLimits
      (clopenModuleRestriction.{t, u, max u (t + 1)} j R ⋙ V) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{max u (t + 1)} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft Y.ProEtᵒᵖ X.ProEtᵒᵖ AddCommGrpCat.{max u (t + 1)}).obj
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ V

/-- Tensoring already preserves finite colimits; the explicit site tensor agrees
with the monoidal tensor. Thus flatness tests only preservation of finite limits. -/
private theorem flat_iff_tensorRight_limits {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F : ClopenData.clopenTensorModules.{t, u} R) :
    SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
      PreservesFiniteLimits (tensorRight F) := by
  constructor
  · intro h
    have h' : exactFunctor _ _ (tensorRight F) :=
      (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R F) h
    exact h'.1
  · intro h
    have : PreservesFiniteLimits (tensorRight F) := h
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R F).symm
      ⟨h, (show PreservesFiniteColimits (tensorRight F) from inferInstance)⟩

private theorem clopen_flat_detection_small
    (X : Scheme.{t}) (I : Type) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F : ClopenData.clopenTensorModules.{t, u} R) :
    SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
      ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
        (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
        ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F) := by
  let R' := (sheafCompose (topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  obtain ⟨G, η, ε, _, _, _, _, _, _, _, _, _, _, ⟨e, hei, heoff, _⟩, _⟩ :=
    clopen_ringed_module_gluing.{t, max u (t + 1), u, 0,
      max u (t + 1), max u (t + 1), 0, 0} X I Y j hd hc R'
      (by
        intro U a b
        exact mul_comm (show R.obj.obj U from a) b)
  let E := CategoryTheory.Equivalence.mk (clopenRestriction j R') G η ε
  have : (clopenRestriction j R').IsEquivalence := E.isEquivalence_functor
  have hr (i : I) : PreservesFiniteLimits
      (ClopenData.clopenTensorRestriction.{t, u} (j i) R) :=
    restrictionPreservesFiniteLimits (j i) R'
  have hs := clopen_structural_data X I Y j hd hc R
  have he (i : I) : PreservesLimitsOfSize.{0, 0} (e i) := by
    obtain ⟨adj⟩ := hs.2.2 i (e i) (hei i) (fun k h ↦ heoff k i h)
    exact adj.rightAdjoint_preservesLimits
  have ht (i : I) : (ClopenData.clopenTensorRestriction.{t, u} (j i) R).Braided :=
    (hs.1 i).choose
  have cmp (i : I) :
      ClopenData.clopenTensorRestriction.{t, u} (j i) R ⋙
        tensorRight ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F) ≅
      tensorRight F ⋙ ClopenData.clopenTensorRestriction.{t, u} (j i) R := by
    let := ht i
    exact Functor.Monoidal.commTensorRight _ F
  constructor
  · intro h i
    have : PreservesFiniteLimits (tensorRight F) :=
      (flat_iff_tensorRight_limits R F).mp h
    apply (flat_iff_tensorRight_limits _ _).mpr
    have : PreservesFiniteLimits (e i ⋙ tensorRight F ⋙
        ClopenData.clopenTensorRestriction.{t, u} (j i) R) :=
      comp_preservesFiniteLimits _ _
    let c : tensorRight ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F) ≅
        e i ⋙ tensorRight F ⋙ ClopenData.clopenTensorRestriction.{t, u} (j i) R :=
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (hei i).some.symm _ ≪≫
          Functor.isoWhiskerLeft (e i) (cmp i)
    exact preservesFiniteLimits_of_natIso c.symm
  · intro h
    apply (flat_iff_tensorRight_limits R F).mpr
    apply jointlyPreservesFiniteLimits (clopenRestriction j R') (tensorRight F)
    intro i
    have : PreservesFiniteLimits
        (tensorRight ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F)) :=
      (flat_iff_tensorRight_limits _ _).mp (h i)
    have : PreservesFiniteLimits (ClopenData.clopenTensorRestriction.{t, u} (j i) R ⋙
        tensorRight ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F)) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (cmp i)

/-- Flatness is detected componentwise by restriction along a finite disjoint
open-and-closed covering. The tensor comparison and zero-insertion adjunction
transport finite-limit preservation to each component. Conversely, the gluing
equivalence detects finite limits componentwise. Tensoring always preserves finite
colimits. -/
theorem clopen_flat_detection
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ F : ClopenData.clopenTensorModules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
          ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F) := by
  classical
  let := Fintype.ofFinite I
  let a := (Fintype.equivFin I).symm
  have hd : Pairwise (fun i k ↦
      Disjoint (Set.range (j (a i))) (Set.range (j (a k)))) :=
    fun _ _ h ↦ hdisjoint (a.injective.ne h)
  have hc : ∀ x : X, ∃ i, x ∈ Set.range (j (a i)) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨k, rfl⟩ := a.surjective i
    exact ⟨k, hi⟩
  intro F
  have h := clopen_flat_detection_small X _ (fun i ↦ Y (a i))
    (fun i ↦ j (a i)) hd hc R F
  refine h.trans ⟨?_, ?_⟩
  · intro hh i
    obtain ⟨k, rfl⟩ := a.surjective i
    exact hh k
  · intro hh i
    exact hh (a i)

end AlgebraicGeometry.Scheme.ProEt
