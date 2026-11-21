import Langlands.GroupScheme.CliffordSpin.Connectedness
import Langlands.GroupScheme.CliffordSpin.GaloisBoundary
import Langlands.GroupScheme.CentralIsogeny.GeometricKernelComparison
import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract

/-! # Hasse kernel of simply connected scalar spin covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem natCard_muTwo_affinePoints
    (F K : Type u) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Nat.card (affinePoints (mu (Spec (CommRingCat.of F)) 2).toGrp (CommAlgCat.of F K)) = 2 := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  exact (Nat.card_congr (mu.affinePointsEquiv 2 (Spec.algebraMap F K)).toEquiv).trans
    ((IsPrimitiveRoot.neg_one (R := K) 0 (by decide)).card_rootsOfUnity)

namespace CliffordSpin

variable {F K : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  [Field K] [Algebra F K] [IsAlgClosed K] (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "P" => groupScheme Q (Pi.basisFun F (Fin n))
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "π" => projection q

/-- A simply connected central cover of the scalar norm-one group with geometric
kernel of order two is the actual Clifford lift group over the ground field. -/
theorem exists_iso_of_simplyConnected_scalarCover (hq : (τ).IsNondegenerateQuadratic q)
    (hn : 2 ≤ n) (hSO : IsSemisimple (SO))
    {G : GroupScheme (Spec (CommRingCat.of F))} (p : G ⟶ SO) (hG : IsSimplyConnected G)
    (hp : IsCentralIsogeny p) (hker : Nat.card (affinePoints (kernel p) (CommAlgCat.of F K)) = 2) :
    ∃ e : G ≅ P, e.hom ≫ (π) = p := by
  let hπ := isCentralIsogeny_projection q hq
  let e := hπ.kernelRootsEquiv 2 (kernelIso q hq) K
  have hcount : Nat.card (affinePoints (kernel (π)) (CommAlgCat.of F K)) = 2 :=
    (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (mu.affinePointsEquiv 2 (Spec.algebraMap F K)).toEquiv).symm.trans
        (natCard_muTwo_affinePoints F K))
  exact exists_iso_centralCover_of_geometricKernel_card_eq p (π) hG
    (isSemisimple_groupScheme q hq hn hSO) hSO hp hπ (hker.trans hcount.symm) (by rw [hcount]; decide)

end CliffordSpin

/-- A simply connected central double cover of a semisimple scalar norm-one isometry
group in dimension at least four has trivial Hasse kernel over a number field. -/
def NumberFieldScalarSpinCoverHasseStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F] [Field K] [Algebra F K] [IsAlgClosed K]
    (n : ℕ) [NeZero n] (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q → 4 ≤ n →
    IsSemisimple ((FirstKindInvolution.scalar F).normOneIsometryGroup q) →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F)))
      (p : G ⟶ (FirstKindInvolution.scalar F).normOneIsometryGroup q),
      IsSimplyConnected G → IsCentralIsogeny p →
      Nat.card (affinePoints (kernel p) (CommAlgCat.of F K)) = 2 →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The Clifford isomorphism transports the verified Hasse kernel to the given cover. -/
theorem numberFieldScalarSpinCoverHasse : NumberFieldScalarSpinCoverHasseStatement.{u} := by
  intro F K _ _ _ _ _ n _ q hq hn hSO G p hG hp hker L _ _ _ _ ξ hξ
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨e, _⟩ := CliffordSpin.exists_iso_of_simplyConnected_scalarCover q hq (by omega) hSO p hG hp hker
  exact Cocycle.IsTrivial.of_map_retract e.hom e.inv e.hom_inv_id
    (CliffordSpin.scalarCliffordSpinGaloisHasseKernel F n q hq hn L (ξ.map e.hom) (hξ.map e.hom))

end Langlands.GroupScheme
