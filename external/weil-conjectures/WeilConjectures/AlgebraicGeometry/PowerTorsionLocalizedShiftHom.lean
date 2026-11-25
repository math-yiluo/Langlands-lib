/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.RingHomExtensionDefs
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Flat.Localization

/-! # Derived orthogonality of power-torsion cohomology and localized coefficients -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable abbrev pointEval (A : CommRingCat.{u}) :
    RingSiteModules A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)) point

private noncomputable def pointConstant (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ RingSiteModules A where
  obj M := ⟨{ obj := fun _ ↦ M
              map := fun _ ↦ ModuleCat.ofHom LinearMap.id }, Presheaf.isSheaf_bot _⟩
  map f := ⟨{ app := fun _ ↦ f }⟩

private noncomputable def pointUnitIso {A : CommRingCat.{u}}
    (M : RingSiteModules A) : M ≅ (pointConstant A).obj ((pointEval A).obj M) := by
  let e : M.val ≅ ((pointConstant A).obj ((pointEval A).obj M)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V g
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
        ext x
        simp [pointConstant, pointEval]
        rfl)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e

private noncomputable def pointEquivalence (A : CommRingCat.{u}) :
    RingSiteModules A ≌ ModuleCat.{u} A where
  functor := pointEval A
  inverse := pointConstant A
  unitIso := NatIso.ofComponents pointUnitIso (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private noncomputable local instance pointEval_isEquivalence (A : CommRingCat.{u}) :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private noncomputable local instance pointConstant_isEquivalence (A : CommRingCat.{u}) :
    (pointConstant A).IsEquivalence := (pointEquivalence A).isEquivalence_inverse

private local instance pointConstant_additive (A : CommRingCat.{u}) :
    (pointConstant A).Additive where
  map_add := by intros; rfl

private local instance pointEval_additive (A : CommRingCat.{u}) :
    (pointEval A).Additive where
  map_add := by intros; rfl

private theorem localization_isZero (A : CommRingCat.{u}) (s : A)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization (Submonoid.powers s) B]
    (N : ModuleCat.{u} A) (hN : ∀ x : N, ∃ k : ℕ, s ^ k • x = 0) :
    IsZero ((ModuleCat.extendScalars (algebraMap A B)).obj N) := by
  let φ := algebraMap A B
  have halg : φ.toAlgebra = inferInstanceAs (Algebra A B) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  have hloc : IsLocalization (Submonoid.powers s) B := inferInstance
  let : Algebra A B := φ.toAlgebra
  let : IsLocalization (Submonoid.powers s) B := by
    change @IsLocalization A _ (Submonoid.powers s) B _ φ.toAlgebra
    rw [halg]
    exact hloc
  let : IsLocalizedModule (Submonoid.powers s) (TensorProduct.mk A B N 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (Submonoid.powers s) B
  let : Subsingleton (B ⊗[A] N) :=
    (IsLocalizedModule.subsingleton_iff (Submonoid.powers s)
      (TensorProduct.mk A B N 1)).2 (fun x ↦ by
        obtain ⟨k, hk⟩ := hN x
        exact ⟨s ^ k, ⟨k, rfl⟩, hk⟩)
  change IsZero (ModuleCat.of B (B ⊗[A] N))
  exact ModuleCat.isZero_of_subsingleton _

/-- A complex with element-power-torsion cohomology has no maps, in any shift,
to a module on which that element acts bijectively. This does not assume a Cech model.
Source: Stacks Project, dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint,
the exact localization/restriction adjunction used in the proof.
(auxiliary; not a blueprint node)

Proof: evaluate at the unique object to work with ordinary A-modules. Extension
of scalars to A[1/s] is exact by flatness and hence its termwise functor computes
the functor on unbounded derived categories. It commutes with cohomology. Every
localized class vanishes by the given power annihilator, so the localized source
is acyclic and its derived object is zero. Bijectivity of multiplication by s on
M extends its A-action uniquely to A[1/s], with the inverse of s acting by the
inverse linear automorphism. Restriction of scalars is exact. Localize the actual
extension/restriction adjunction to the derived categories. Its Hom bijection
identifies every displayed morphism with a map from a shift of the zero localized
source. That map is zero, and the adjunction carries zero to zero. The evaluation
equivalence transports this conclusion back to module sheaves. No boundedness,
finite generation, uniform annihilating exponent or nonzero element is required.
-/
theorem power_torsion_localized_shift_hom
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (T : CochainComplex (RingSiteModules A) ℤ) (s : A)
    (hT : ∀ (i : ℤ) (x : (T.homology i).val.obj (op ⟨PUnit.unit⟩)),
      ∃ k : ℕ, s ^ k • x = 0)
    (M : RingSiteModules A)
    (hM : Function.Bijective
      (fun x : M.val.obj (op ⟨PUnit.unit⟩) ↦ s • x))
    (n : ℤ)
    (f : (DerivedCategory.Q.obj T)⟦n⟧ ⟶
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj M)) :
    f = 0 := by
  classical
  let B := Localization.Away s
  let φ := algebraMap A B
  let L := ModuleCat.extendScalars φ
  let U := ModuleCat.restrictScalars φ
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} B) :=
    HasDerivedCategory.standard (ModuleCat.{u} B)
  let : PreservesFiniteLimits L :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers s)))
  let : L.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj φ).isLeftAdjoint
  let : L.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  let : PreservesFiniteLimits (pointEval A) := inferInstance
  let E := pointEval A ⋙ L
  let R := U ⋙ pointConstant A
  let : PreservesFiniteLimits E := comp_preservesFiniteLimits (pointEval A) L
  let : PreservesFiniteColimits E := comp_preservesFiniteColimits (pointEval A) L
  let : PreservesFiniteLimits R := comp_preservesFiniteLimits U (pointConstant A)
  let : PreservesFiniteColimits R := comp_preservesFiniteColimits U (pointConstant A)
  let adj : E ⊣ R := (pointEquivalence A).toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)
  let D := E.mapDerivedCategory
  have hz : IsZero (D.obj (DerivedCategory.Q.obj T)) := by
    have hc : IsZero (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj T)) := by
      apply (DerivedCategory.isZero_iff _).2
      intro i
      have hh : IsZero (E.obj (T.homology i)) :=
        localization_isZero A s B ((pointEval A).obj (T.homology i)) (hT i)
      have hh' := hh.of_iso ((E.mapHomologicalComplexHomologyIso (.up ℤ) i).app T)
      exact hh'.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app _)
    exact hc.of_iso (E.mapDerivedCategoryFactors.app T)
  have hzn : IsZero (D.obj ((DerivedCategory.Q.obj T)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso ((D.commShiftIso n).app _)
  let M₀ : ModuleCat.{u} A := (pointEval A).obj M
  have hid : IsLocalizedModule (Submonoid.powers s) (LinearMap.id : M₀ →ₗ[A] M₀) := by
    constructor
    · intro t
      obtain ⟨k, hk⟩ := t.property
      change IsUnit (algebraMap A (Module.End A M₀) (t : A))
      rw [← hk, map_pow]
      apply IsUnit.pow
      apply (Module.End.isUnit_iff _).mpr
      exact hM
    · intro x
      exact ⟨(x, 1), one_smul _ _⟩
    · intro x y h
      exact ⟨1, congrArg (fun z ↦ (1 : Submonoid.powers s) • z) h⟩
  let := hid
  let : Module B M₀ := IsLocalizedModule.module (Submonoid.powers s) LinearMap.id
  let : IsScalarTower A B M₀ :=
    IsLocalizedModule.isScalarTower_module (Submonoid.powers s) LinearMap.id
  have hsmul (r : A) (x : M₀) : (algebraMap A B r) • x = r • x :=
    IsScalarTower.algebraMap_smul B r x
  let N : ModuleCat.{u} B := ModuleCat.of B M₀
  let j : U.obj N ≅ M₀ :=
    { hom := ModuleCat.ofHom (X := U.obj N) (Y := M₀)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ hsmul r x }
      inv := ModuleCat.ofHom (X := M₀) (Y := U.obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ (hsmul r x).symm } }
  let jM : M ≅ R.obj N := pointUnitIso M ≪≫ (pointConstant A).mapIso j.symm
  let S := HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0
  let eTarget : DerivedCategory.Q.obj
      ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj M) ≅
      R.mapDerivedCategory.obj (DerivedCategory.Q.obj (S.obj N)) :=
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).mapIso jM) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app N).symm ≪≫
    (R.mapDerivedCategoryFactors.app (S.obj N)).symm
  have hzero : f ≫ eTarget.hom = 0 := by
    let d := adj.mapExactDerivedCategory
    obtain ⟨g, hg⟩ := (d.homEquiv _ _).surjective (f ≫ eTarget.hom)
    have hg0 : g = 0 := hzn.eq_of_src _ _
    rw [← hg, hg0, Adjunction.homEquiv_unit]
    simp
  exact (cancel_mono eTarget.hom).mp (by simpa using hzero)

end AlgebraicGeometry
