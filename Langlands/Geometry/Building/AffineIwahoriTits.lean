import Langlands.Geometry.Building.AffineChamberReflections
import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.Group.TitsSystemRestricted

/-!
# The actual affine Iwahori–Tits datum

The ambient group is `P.zeroSubgroup`, with the generated full parahoric and actual
normalizer restricted to it. The Weyl group is literally `P.affinePart`. Its comparison
with the geometric affine Weyl group, the Tits axioms and saturation are assertions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The restriction of the generated full parahoric to `G(F)^0`. Equality with the full
parahoric after inclusion requires the separately stated containment. -/
def parahoricInZero (Ω : Set P.Apartment) : Subgroup P.zeroSubgroup :=
  (P.parahoric Ω).subgroupOf P.zeroSubgroup

/-- The actual `N(F) ∩ G(F)^0`, now as a subgroup of the ambient group `G(F)^0`. -/
def normalizerInZero : Subgroup P.zeroSubgroup :=
  (normalizerPoints P.i).subgroupOf P.zeroSubgroup

/-- Swap the two subtype conditions: both sides consist of the same rational points
belonging to `N(F)` and `G(F)^0`. This introduces no comparison assertion. -/
def normalizerInZeroEquiv : P.normalizerInZero ≃* P.normalizerZeroComponent where
  toFun n := ⟨⟨n.1.1, n.2⟩, n.1.2⟩
  invFun n := ⟨⟨n.1.1, n.2⟩, n.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Restriction followed by the inclusion into `G(F)` recovers the generated full
parahoric when its containment in `G(F)^0` has been supplied. -/
theorem parahoricInZero_map (Ω : Set P.Apartment) (hΩ : P.parahoric Ω ≤ P.zeroSubgroup) :
    (P.parahoricInZero Ω).map P.zeroSubgroup.subtype = P.parahoric Ω :=
  Subgroup.map_subgroupOf_eq_of_le hΩ

variable [P.normalizerZero.Normal]

/-- The literal restriction of `QuotientGroup.mk' P.normalizerZero`, with its codomain
restricted to the actual affine part. -/
def affineTitsProjection : P.normalizerInZero →* P.affinePart :=
  P.affinePartMk.comp P.normalizerInZeroEquiv.toMonoidHom

/-- The projection agrees with the full normalizer quotient on every representative. -/
theorem affineTitsProjection_coe (n : P.normalizerInZero) :
    (P.affineTitsProjection n : P.IwahoriWeylGroup) =
      QuotientGroup.mk' P.normalizerZero
        (P.normalizerInZeroEquiv n : normalizerPoints P.i) :=
  rfl

/-- The same comparison, expressed for every element of the previously defined
`normalizerZeroComponent`. -/
theorem affineTitsProjection_equiv_symm (n : P.normalizerZeroComponent) :
    P.affineTitsProjection (P.normalizerInZeroEquiv.symm n) = P.affinePartMk n :=
  rfl

/-- The multiplicative affine-Weyl comparison realizes the actual apartment action on
every normalizer representative (KP Theorem 7.5.3(2)). -/
def IsAffineWeylComparison
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots) : Prop :=
  ∀ n : P.normalizerZeroComponent,
    (e (P.affinePartMk n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
      P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i)

/-- The geometric chamber-simple reflections, transported into the actual affine part.
The comparison's compatibility with the apartment action is a separate assertion. -/
def chamberSimpleInAffinePart
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (C : Set P.Apartment) : Set P.affinePart :=
  e ⁻¹' AffineRootSystem.chamberSimpleReflections P.affineRoots C

/-- KP Theorem 7.5.3(1),(2), for the `G(F)^0` branch and the given comparison `e`.
The Borel subgroup is the restriction of the generated full `P.parahoric C`. -/
structure AffineIwahoriTitsWith (C : Set P.Apartment)
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots) : Prop where
  parahoric_le_zero : P.parahoric C ≤ P.zeroSubgroup
  action_compatible : P.IsAffineWeylComparison e
  tits : Langlands.Group.IsTitsSystem (P.parahoricInZero C) P.normalizerInZero
    P.affineTitsProjection (P.chamberSimpleInAffinePart e C)
  saturated : Langlands.Group.TitsSystem.IsSaturated (P.parahoricInZero C) P.normalizerInZero

/-- The actual intersection-of-conjugates formula, not merely the name "saturated". -/
theorem AffineIwahoriTitsWith.saturation_formula {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (h : P.AffineIwahoriTitsWith C e) :
    (⨅ n : P.normalizerInZero,
      (P.parahoricInZero C).map (MulAut.conj (n : P.zeroSubgroup)).toMonoidHom) =
        P.parahoricInZero C ⊓ P.normalizerInZero :=
  h.saturated

/-- Existence of an actual affine Iwahori–Tits system for the chosen chamber, including
the multiplication-preserving geometric comparison. Normality remains an instance
argument at this fixed-data level. -/
def AffineIwahoriTits (C : Set P.Apartment) : Prop :=
  ∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
    P.AffineIwahoriTitsWith C e

end Langlands.Geometry.Building.ParahoricBuildingData
