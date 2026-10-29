import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Homotopy and scalar extension of perfect representatives -/

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

lemma isKProjective_of_isStrictlyPerfect
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K) :
    K.IsKProjective := by
  obtain ⟨a, b, ha, hb⟩ := hK.1
  have : K.IsStrictlyLE b := hb
  have (i : ℤ) : Module.Projective R (K.X i) := (hK.2 i).2
  exact CochainComplex.isKProjective_of_projective K b

/-- A homotopy equivalence gives an actual isomorphism in the derived category. -/
def derivedIsoOfHomotopyEquiv
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv K L) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L :=
  asIso (DerivedCategory.Q.map e.hom)

/-- Lift an isomorphism between bounded projective representatives to a homotopy equivalence. -/
def homotopyEquivOfDerivedIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    HomotopyEquiv K L := by
  apply Classical.choice
  change Nonempty (HomotopyEquiv K L)
  have := isKProjective_of_isStrictlyPerfect hK
  have := isKProjective_of_isStrictlyPerfect hL
  let e' :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app L).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K _).surjective e'.hom
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective L _).surjective e'.inv
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := f
      inv := g
      hom_inv_id := (CochainComplex.IsKProjective.Qh_map_bijective K _).injective
        (by simp [hf, hg])
      inv_hom_id := (CochainComplex.IsKProjective.Qh_map_bijective L _).injective
        (by simp [hf, hg]) }⟩

/-- Scalar extension is additive on module homomorphisms. -/
instance extendScalars_additive {S : Type u} [CommRing S] (φ : R →+* S) :
    (ModuleCat.extendScalars φ).Additive where
  map_add := by
    intro X Y f g
    let := φ.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (1 : S) ⊗ₜ[R, φ] (f.hom m + g.hom m) =
      (1 : S) ⊗ₜ[R, φ] f.hom m + (1 : S) ⊗ₜ[R, φ] g.hom m
    exact TensorProduct.tmul_add _ _ _

/-- Ordinary scalar extension preserves an actual homotopy equivalence. -/
def baseChangeHomotopyEquiv {S : Type u} [CommRing S] (φ : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((baseChange φ).obj K) ((baseChange φ).obj L) :=
  (ModuleCat.extendScalars φ).mapHomotopyEquiv e

/-- Scalar extensions of two strictly perfect representatives of one derived
object have isomorphic images in the actual target derived category. -/
def baseChangeDerivedIso {S : Type u} [CommRing S] (φ : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj ((baseChange φ).obj K) ≅
      DerivedCategory.Q.obj ((baseChange φ).obj L) :=
  derivedIsoOfHomotopyEquiv (baseChangeHomotopyEquiv φ (homotopyEquivOfDerivedIso hK hL e))

end Langlands.Cohomology.ModuleComplex
