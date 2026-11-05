import Langlands.Geometry.Building.AffineIwahoriTits
import Langlands.Geometry.Building.IwahoriWeylQuotientLemmas

/-!
# The actual affine Tits projection and its kernel

The quotient projection is surjective, and its kernel is the image of `Z(F)^0`
inside `G(F)^0`. This kernel belongs to every restricted parahoric. Equality
with the parahoric-normalizer intersection remains a geometric assertion.
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

/-- The actual image of `Z(F)^0` as a subgroup of `G(F)^0`. -/
def centralizerZeroInZero : Subgroup P.zeroSubgroup :=
  (P.centralizerZero.map (rationalPoints.map P.centralizer.j)).subgroupOf P.zeroSubgroup

/-- Inclusion into `G(F)` recovers the full image of `Z(F)^0`. -/
theorem centralizerZeroInZero_map :
    P.centralizerZeroInZero.map P.zeroSubgroup.subtype =
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  Subgroup.map_subgroupOf_eq_of_le P.zeroDatum.map_centralizerZero_le_zeroSubgroup

theorem centralizerZeroInZero_le_normalizerInZero :
    P.centralizerZeroInZero ≤ P.normalizerInZero := by
  rintro n ⟨z, hz, hn⟩
  change (n : rationalPoints G) ∈ normalizerPoints P.i
  change rationalPoints.map P.centralizer.j z = (n : rationalPoints G) at hn
  rw [← hn]
  exact centralizerPoints_le_normalizerPoints P.i
    (map_mem_centralizerPoints P.centralizer.isRepresentedBy z)

theorem centralizerZeroInZero_le_parahoricInZero (Ω : Set P.Apartment) :
    P.centralizerZeroInZero ≤ P.parahoricInZero Ω :=
  fun _ hn => P.map_centralizerZero_le_parahoric Ω hn

variable [P.normalizerZero.Normal]

/-- The literal affine Tits projection is surjective. -/
theorem affineTitsProjection_surjective : Function.Surjective P.affineTitsProjection :=
  P.affinePartMk_surjective.comp P.normalizerInZeroEquiv.surjective

/-- A representative is killed precisely when its ambient rational point lies in
the actual image of `Z(F)^0`. -/
theorem affineTitsProjection_eq_one_iff (n : P.normalizerInZero) :
    P.affineTitsProjection n = 1 ↔
      (n : P.zeroSubgroup) ∈ P.centralizerZeroInZero := by
  change P.affinePartMk (P.normalizerInZeroEquiv n) = 1 ↔ _
  rw [P.affinePartMk_eq_one_iff, P.mem_normalizerZero_iff]
  rfl

/-- The kernel is the same actual centralizer-zero subgroup, restricted to the
actual normalizer inside `G(F)^0`. -/
theorem affineTitsProjection_ker :
    P.affineTitsProjection.ker =
      P.centralizerZeroInZero.subgroupOf P.normalizerInZero := by
  ext n
  exact P.affineTitsProjection_eq_one_iff n

/-- Every restricted parahoric contains the projection kernel. -/
theorem affineTitsProjection_ker_le_parahoricInZero (Ω : Set P.Apartment) :
    P.affineTitsProjection.ker ≤
      (P.parahoricInZero Ω).subgroupOf P.normalizerInZero := by
  intro n hn
  exact P.centralizerZeroInZero_le_parahoricInZero Ω
    ((P.affineTitsProjection_eq_one_iff n).mp hn)

/-- The remaining kernel equality for the Tits system is exactly the assertion
that the restricted parahoric-normalizer intersection is the centralizer-zero image. -/
theorem affineTitsProjection_ker_eq_iff (Ω : Set P.Apartment) :
    P.affineTitsProjection.ker =
        (P.parahoricInZero Ω).subgroupOf P.normalizerInZero ↔
      P.parahoricInZero Ω ⊓ P.normalizerInZero = P.centralizerZeroInZero := by
  rw [P.affineTitsProjection_ker, Subgroup.subgroupOf_inj,
    inf_eq_left.mpr P.centralizerZeroInZero_le_normalizerInZero]
  exact eq_comm

/-- Representative compatibility for the literal Tits projection. -/
theorem IsAffineWeylComparison.affineTitsProjection
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (he : P.IsAffineWeylComparison e) (n : P.normalizerInZero) :
    (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
      P.apartment.normalizerAffineEquiv
        (P.normalizerInZeroEquiv n : normalizerPoints P.i) :=
  he (P.normalizerInZeroEquiv n)

/-- Compatibility on every actual normalizer representative uniquely prescribes
the multiplicative comparison with the geometric affine Weyl group. -/
theorem IsAffineWeylComparison.unique
    {e e' : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (he : P.IsAffineWeylComparison e) (he' : P.IsAffineWeylComparison e') :
    e = e' := by
  apply MulEquiv.ext
  intro w
  obtain ⟨n, rfl⟩ := P.affinePartMk_surjective w
  exact Subtype.ext ((he n).trans (he' n).symm)

end Langlands.Geometry.Building.ParahoricBuildingData
