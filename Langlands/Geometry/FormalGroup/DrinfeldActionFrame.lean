import Langlands.Geometry.FormalGroup.DrinfeldActionExponent
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrame
import Langlands.Geometry.FormalGroup.DrinfeldSignedFrameFrobenius

/-! # Products of the fixed-frame comparisons in Drinfeld's action -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open ValuativeRel CentralSimple ModuleLaw

variable {K D κ S : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] [CommRing S] [Algebra 𝒪[K] S]
variable {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (c : Φ.val.MatrixCoordinates)
variable {a b z : κ →ₐ[𝒪[K]] S}

/-- The fixed-frame comparison consists of signed Frobenius followed by the inverse matrix. -/
def actionFrameQuasiIsogeny (g : GL (Fin (reducedDegree K D)) K × Dˣ)
    (e : shift (DrinfeldAction.exponent K D g) b = a) :
    OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b) :=
  (signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D g) e).trans
    ((c.quasiIsogeny g.1⁻¹).map b)

private theorem signedFrameFrobenius_eq_of_exponent_eq {n m : ℤ} (h : n = m)
    (en : shift n b = a) (em : shift m b = a) :
    signedFrameFrobenius Φ p hcard hFrob n en = signedFrameFrobenius Φ p hcard hFrob m em := by
  subst m
  rfl

/-- The unit of the acting group gives the identity at the fixed residue map. -/
theorem actionFrameQuasiIsogeny_one (e : shift (DrinfeldAction.exponent K D 1) b = b) :
    actionFrameQuasiIsogeny Φ p hcard hFrob c 1 e =
      OrderAction.QuasiIsogeny.refl (Φ.val.order.map b) := by
  rw [actionFrameQuasiIsogeny, signedFrameFrobenius_eq_of_exponent_eq Φ p hcard hFrob
    (DrinfeldAction.exponent_one K D) e (shift_zero b), signedFrameFrobenius_zero]
  simp

set_option maxHeartbeats 1000000 in
/-- On the successive shifted coefficients, the two actual source comparisons compose
to the source comparison for the group product. -/
theorem actionFrameQuasiIsogeny_mul (g h : GL (Fin (reducedDegree K D)) K × Dˣ)
    (eg : shift (DrinfeldAction.exponent K D g) b = a)
    (eh : shift (DrinfeldAction.exponent K D h) z = b)
    (egh : shift (DrinfeldAction.exponent K D (g * h)) z = a) :
    (actionFrameQuasiIsogeny Φ p hcard hFrob c g eg).trans
      (actionFrameQuasiIsogeny Φ p hcard hFrob c h eh) =
      actionFrameQuasiIsogeny Φ p hcard hFrob c (g * h) egh := by
  let fg := signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D g) eg
  let fh := signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D h) eh
  let fgh := signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D (g * h)) egh
  let mg := (c.quasiIsogeny g.1⁻¹).map b
  let mg' := (c.quasiIsogeny g.1⁻¹).map z
  let mh := (c.quasiIsogeny h.1⁻¹).map z
  let mgh := (c.quasiIsogeny (g * h).1⁻¹).map z
  have hnat : mg.trans fh = fh.trans mg' :=
    (signedFrameFrobenius_natural Φ p hcard hFrob
      (DrinfeldAction.exponent K D h) eh (c.quasiIsogeny g.1⁻¹)).symm
  have hf : fg.trans fh = fgh :=
    (signedFrameFrobenius_trans Φ p hcard hFrob _ _ eg eh).trans
      (signedFrameFrobenius_eq_of_exponent_eq Φ p hcard hFrob
        (DrinfeldAction.exponent_mul K D g h).symm (shift_trans eg eh) egh)
  have hm : mg'.trans mh = mgh := by
    change ((c.quasiIsogeny g.1⁻¹).map z).trans ((c.quasiIsogeny h.1⁻¹).map z) =
      (c.quasiIsogeny (g.1 * h.1)⁻¹).map z
    rw [mul_inv_rev, c.quasiIsogeny_mul, OrderAction.QuasiIsogeny.map_trans]
  change (fg.trans mg).trans (fh.trans mh) = fgh.trans mgh
  rw [OrderAction.QuasiIsogeny.trans_assoc fg, ← OrderAction.QuasiIsogeny.trans_assoc mg,
    hnat, OrderAction.QuasiIsogeny.trans_assoc fh, ← OrderAction.QuasiIsogeny.trans_assoc fg fh,
    hf, hm]

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue
