import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateSlice
import Langlands.Representation.Plancherel.RationalUnitaryPoleFactorization

/-! # Unit-circle pole factors of one-coordinate Laurent denominators -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance coordinateDenominatorPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option quotPrecheck false in
local notation "X" => unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)

variable {n : ℕ}
  (B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage G)))

private theorem firstCoordinatePullback_T_one :
    rationalUnramifiedFirstCoordinatePullback G B (LaurentPolynomial.T 1) =
      rationalUnramifiedLatticeMonomial G (B 0) := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (B 0).toMul
  have hv : Additive.ofMul (rationalValuationImageProjection G g) = B 0 :=
    congrArg Additive.ofMul hg
  apply Subtype.ext
  funext z
  rw [rationalUnramifiedFirstCoordinatePullback_eval, LaurentPolynomial.eval₂_T, zpow_one]
  calc
    ((rationalUnramifiedBasisUnitCoordinates G B z 0 : ℂˣ) : ℂ) = (z.val g : ℂ) := by
      change ((rationalCanonicalImageUnramifiedContinuousEquiv G).symm z (B 0).toMul : ℂ) = _
      rw [← hg, rationalCanonicalImageUnramifiedContinuousEquiv_symm_projection]
    _ = (rationalUnramifiedLatticeMonomial G (B 0)).val z := by
      rw [← hv, rationalUnramifiedLatticeMonomial_eval_projection]

namespace RationalUnitaryPoleFactorization

/-- Pulling a nonzero Laurent polynomial back along the first basis
coordinate gives a denominator with unitary pole factors. -/
def ofFirstCoordinateLaurent (hG : GroupScheme.IsConnectedReductive G)
    (b : LaurentPolynomial ℂ) (hb : b ≠ 0) :
    RationalUnitaryPoleFactorization G (rationalUnramifiedFirstCoordinatePullback G B b) :=
  Classical.choice (by
    obtain ⟨k, p, hp⟩ := LaurentPolynomial.exists_T_pow b
    have hLaurent : b = Polynomial.toLaurent p * LaurentPolynomial.T (-(k : ℤ)) := by
      rw [hp, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one]
    have hp₀ : p ≠ 0 := fun hz => hb (by rw [hLaurent, hz, map_zero, zero_mul])
    let pull := rationalUnramifiedFirstCoordinatePullback G B
    let e := pull.comp (Polynomial.toLaurent : Polynomial ℂ →+* LaurentPolynomial ℂ)
    let rootFactors := p.roots.toList.map (fun a => (B 0, a))
    let factor (t : Λ × ℂ) := rationalUnramifiedLatticeMonomial G t.1 - algebraMap ℂ R t.2
    let d := pull (LaurentPolynomial.C p.leadingCoeff * LaurentPolynomial.T (-(k : ℤ)))
    have hd (z : Xu) : d.val (unitaryToUnramified G z) ≠ 0 := by
      simp only [d, pull, rationalUnramifiedFirstCoordinatePullback_eval]
      rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply]
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp₀) (Units.ne_zero _)
    have hrootList :
        p = Polynomial.C p.leadingCoeff *
          (p.roots.toList.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      calc
        p = Polynomial.C p.leadingCoeff *
            (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod :=
          (IsAlgClosed.splits p).eq_prod_roots
        _ = _ := by rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    have hC (a : ℂ) : pull (LaurentPolynomial.C a) = algebraMap ℂ R a := by
      simp [pull, rationalUnramifiedFirstCoordinatePullback]
    have hmap (a : ℂ) : e (Polynomial.X - Polynomial.C a) = factor (B 0, a) := by
      simp only [e, RingHom.comp_apply, map_sub, Polynomial.toLaurent_X,
        Polynomial.toLaurent_C, hC, factor]
      rw [firstCoordinatePullback_T_one G B]
    have hprod :
        e (p.roots.toList.map (fun a => Polynomial.X - Polynomial.C a)).prod =
          (rootFactors.map factor).prod := by
      simp only [rootFactors, map_list_prod, List.map_map]
      exact congrArg List.prod (List.map_congr_left fun a _ => hmap a)
    have hep : e p = pull (LaurentPolynomial.C p.leadingCoeff) * (rootFactors.map factor).prod :=
      (congrArg e hrootList).trans (by rw [map_mul, hprod]; simp [e])
    have heq : pull b = (rootFactors.map factor).prod * d := by
      calc
        pull b = e p * pull (LaurentPolynomial.T (-(k : ℤ))) :=
          (congrArg pull hLaurent).trans (map_mul pull _ _)
        _ = (rootFactors.map factor).prod * d := by
          rw [hep, show d = _ from map_mul pull _ _]
          ac_rfl
    refine ⟨?_⟩
    rw [heq]
    exact ofMonomialDifferences G hG rootFactors (fun t ht => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
      exact B.ne_zero 0) d hd)

/-- The scalar denominator on a first-coordinate slice factors as soon as
it is nonzero at one ambient character. -/
def ofSlice (hG : GroupScheme.IsConnectedReductive G)
    (c : Fin n → ℂˣ) (b : R) (z : X)
    (hb : (rationalUnramifiedSliceRegular G B c b).val z ≠ 0) :
    RationalUnitaryPoleFactorization G (rationalUnramifiedSliceRegular G B c b) :=
  ofFirstCoordinateLaurent G B hG (rationalUnramifiedSliceLaurent G B c b) (fun h =>
    hb (by simp [rationalUnramifiedSliceRegular, h]))

end RationalUnitaryPoleFactorization
end Langlands.Plancherel
