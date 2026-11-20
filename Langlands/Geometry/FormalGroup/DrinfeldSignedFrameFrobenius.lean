import Langlands.Geometry.FormalGroup.DrinfeldShiftedFrameFrobenius
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Signed relative Frobenius between actual Drinfeld frames -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open ValuativeRel ModuleLaw

variable {K D κ S : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] [CommRing S] [Algebra 𝒪[K] S]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable {a b c : κ →ₐ[𝒪[K]] S}

omit [ExpChar κ p] in
/-- Two actual shifts compose in the source-to-target direction. -/
theorem shift_trans {n m : ℤ} (e : shift n b = a) (e' : shift m c = b) :
    shift (n + m) c = a := by
  rw [add_comm n m, ← shift_shift, e', e]

omit [ExpChar κ p] in
/-- An opposite shift recovers the original coefficients. -/
theorem shift_reverse {n : ℤ} (e : shift n b = a) : shift (-n) a = b := by
  rw [← e, shift_shift, add_neg_cancel, shift_zero]

omit [ExpChar κ p] in
private def frobeniusSourceIso (n : ℤ) (hn : 0 ≤ n) (e : shift n b = a) :
    OrderAction.Iso (Φ.val.order.map a) (Φ.val.order.map (shift (n.toNat : ℤ) b)) :=
  Φ.val.order.mapReAlgebraIso _ _ rfl _ _ (congrArg AlgHom.toRingHom
    (by rw [Int.toNat_of_nonneg hn, e]))

omit [ExpChar κ p] in
private theorem frobeniusSourceIso_hom_coordinates (n : ℤ) (hn : 0 ≤ n) (e : shift n b = a) :
    (frobeniusSourceIso Φ n hn e).hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  OrderAction.mapReAlgebraIso_hom_coordinates _ _ _ _ _ _ _

/-- The nonnegative comparison after identifying the shifted and supplied source maps. -/
def nonnegativeFrameFrobenius (n : ℤ) (hn : 0 ≤ n) (e : shift n b = a) :
    OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b) :=
  (OrderAction.QuasiIsogeny.ofIso (frobeniusSourceIso Φ n hn e)).trans
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n.toNat (hFrob n.toNat) b)

private theorem nonnegativeFrameFrobenius_hom (n : ℤ) (hn : 0 ≤ n) (e : shift n b = a) :
    (nonnegativeFrameFrobenius Φ p hcard hFrob n hn e).hom = OrderAction.RationalHom.ofHom
      ((shiftedFrameFrobeniusHom p hcard Φ.val.order n.toNat b).comp
        (frobeniusSourceIso Φ n hn e).hom) := by
  change (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n.toNat (hFrob n.toNat) b).hom.comp
    (OrderAction.RationalHom.ofHom (frobeniusSourceIso Φ n hn e).hom) = _
  rw [shiftedFrameFrobeniusQuasiIsogeny_hom, OrderAction.RationalHom.ofHom_comp]

private theorem nonnegativeFrameFrobenius_coordinates (n : ℤ) (hn : 0 ≤ n)
    (e : shift n b = a) (d : κ →+* S) :
    ((shiftedFrameFrobeniusHom p hcard Φ.val.order n.toNat b).comp
      (frobeniusSourceIso Φ n hn e).hom).val.toHom.toCoordinateMap =
      (CoordinateMap.frobeniusPow (R := κ) p (f * n.toNat)).map d := by
  change (shiftedFrameFrobeniusHom p hcard Φ.val.order n.toNat b).val.toHom.toCoordinateMap.comp
    (frobeniusSourceIso Φ n hn e).hom.val.toHom.toCoordinateMap = _
  rw [frobeniusSourceIso_hom_coordinates Φ, CoordinateMap.comp_id,
    shiftedFrameFrobeniusHom_coordinates p hcard _ _ b d]

private theorem nonnegativeFrameFrobenius_congr {n m : ℤ} (e₀ : n = m)
    (hn : 0 ≤ n) (hm : 0 ≤ m) (e : shift n b = a) (e' : shift m b = a) :
    nonnegativeFrameFrobenius Φ p hcard hFrob n hn e =
      nonnegativeFrameFrobenius Φ p hcard hFrob m hm e' := by
  subst m
  rfl

/-- The positive tensor comparisons compose as actual relative Frobenius maps. -/
theorem nonnegativeFrameFrobenius_trans (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (e : shift n b = a) (e' : shift m c = b) :
    (nonnegativeFrameFrobenius Φ p hcard hFrob n hn e).trans
      (nonnegativeFrameFrobenius Φ p hcard hFrob m hm e') =
    nonnegativeFrameFrobenius Φ p hcard hFrob (n + m) (add_nonneg hn hm) (shift_trans e e') := by
  apply OrderAction.QuasiIsogeny.ext
  change (nonnegativeFrameFrobenius Φ p hcard hFrob m hm e').hom.comp
      (nonnegativeFrameFrobenius Φ p hcard hFrob n hn e).hom =
    (nonnegativeFrameFrobenius Φ p hcard hFrob (n + m) (add_nonneg hn hm) (shift_trans e e')).hom
  rw [nonnegativeFrameFrobenius_hom, nonnegativeFrameFrobenius_hom,
    nonnegativeFrameFrobenius_hom, ← OrderAction.RationalHom.ofHom_comp]
  apply congrArg (OrderAction.RationalHom.ofHom (F := K))
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (((shiftedFrameFrobeniusHom p hcard Φ.val.order m.toNat c).comp
      (frobeniusSourceIso Φ m hm e').hom).val.toHom.toCoordinateMap).comp
    (((shiftedFrameFrobeniusHom p hcard Φ.val.order n.toNat b).comp
      (frobeniusSourceIso Φ n hn e).hom).val.toHom.toCoordinateMap) = _
  have hadd : (n + m).toNat = n.toNat + m.toNat := by omega
  rw [nonnegativeFrameFrobenius_coordinates Φ p hcard m hm e' c.toRingHom,
    nonnegativeFrameFrobenius_coordinates Φ p hcard n hn e c.toRingHom,
    nonnegativeFrameFrobenius_coordinates Φ p hcard (n + m) (add_nonneg hn hm)
      (shift_trans e e') c.toRingHom, hadd, Nat.mul_add, ← CoordinateMap.map_comp,
    CoordinateMap.frobeniusPow_add]

/-- The signed comparison is positive relative Frobenius in the forward direction
or its actual whole rational inverse in the reverse direction. -/
def signedFrameFrobenius (n : ℤ) (e : shift n b = a) :
    OrderAction.QuasiIsogeny K (Φ.val.order.map a) (Φ.val.order.map b) :=
  if hn : 0 ≤ n then nonnegativeFrameFrobenius Φ p hcard hFrob n hn e
  else (nonnegativeFrameFrobenius Φ p hcard hFrob (-n) (by omega) (shift_reverse e)).symm

/-- In nonnegative degree the signed comparison is exactly the positive comparison. -/
theorem signedFrameFrobenius_of_nonneg (n : ℤ) (hn : 0 ≤ n) (e : shift n b = a) :
    signedFrameFrobenius Φ p hcard hFrob n e =
      nonnegativeFrameFrobenius Φ p hcard hFrob n hn e := by
  rw [signedFrameFrobenius, dite_eq_left hn]

/-- On the actual inverse-shifted coefficients, a nonnegative signed comparison
is exactly the original positive relative comparison. -/
theorem signedFrameFrobenius_natCast (n : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    signedFrameFrobenius Φ p hcard hFrob (n : ℤ) (rfl : shift (n : ℤ) ψ = _) =
      shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n (hFrob n) ψ := by
  rw [signedFrameFrobenius_of_nonneg Φ p hcard hFrob (n : ℤ) (Int.natCast_nonneg n)]
  change (OrderAction.QuasiIsogeny.refl _).trans _ = _
  exact OrderAction.QuasiIsogeny.refl_trans _

private theorem signedFrameFrobenius_congr {n m : ℤ} (h : n = m)
    (e : shift n b = a) (e' : shift m b = a) :
    signedFrameFrobenius Φ p hcard hFrob n e = signedFrameFrobenius Φ p hcard hFrob m e' := by
  subst m
  rfl

private theorem nonnegativeFrameFrobenius_trans_signed (k n : ℤ)
    (hk : 0 ≤ k) (hkn : 0 ≤ k + n) (e : shift k b = a) (e' : shift n c = b) :
    (nonnegativeFrameFrobenius Φ p hcard hFrob k hk e).trans
      (signedFrameFrobenius Φ p hcard hFrob n e') =
    nonnegativeFrameFrobenius Φ p hcard hFrob (k + n) hkn (shift_trans e e') := by
  by_cases hn : 0 ≤ n
  · rw [signedFrameFrobenius_of_nonneg Φ p hcard hFrob n hn e']
    exact nonnegativeFrameFrobenius_trans Φ p hcard hFrob k n hk hn e e'
  · have hneg : 0 ≤ -n := by omega
    rw [signedFrameFrobenius, dite_eq_right hn]
    apply OrderAction.QuasiIsogeny.trans_right_cancel _ _
      (nonnegativeFrameFrobenius Φ p hcard hFrob (-n) hneg (shift_reverse e'))
    rw [OrderAction.QuasiIsogeny.trans_assoc, OrderAction.QuasiIsogeny.symm_trans_self,
      OrderAction.QuasiIsogeny.trans_refl,
      nonnegativeFrameFrobenius_trans Φ p hcard hFrob (k + n) (-n) hkn hneg
        (shift_trans e e') (shift_reverse e')]
    apply nonnegativeFrameFrobenius_congr
    omega

/-- The actual signed Frobenius comparisons compose for every pair of signed exponents. -/
theorem signedFrameFrobenius_trans (n m : ℤ) (e : shift n b = a) (e' : shift m c = b) :
    (signedFrameFrobenius Φ p hcard hFrob n e).trans
      (signedFrameFrobenius Φ p hcard hFrob m e') =
    signedFrameFrobenius Φ p hcard hFrob (n + m) (shift_trans e e') := by
  let k := max (max 0 (-n)) (-(n + m))
  have hk : 0 ≤ k := (le_max_left 0 (-n)).trans (le_max_left _ _)
  have hkn : 0 ≤ k + n := by
    have h : -n ≤ k := (le_max_right 0 (-n)).trans (le_max_left _ _)
    omega
  have hknm : 0 ≤ k + (n + m) := by
    have h : -(n + m) ≤ k := le_max_right _ _
    omega
  have hknm' : 0 ≤ (k + n) + m := by omega
  let d := shift k a
  have ed : shift k a = d := rfl
  apply OrderAction.QuasiIsogeny.trans_left_cancel
    (nonnegativeFrameFrobenius Φ p hcard hFrob k hk ed)
  rw [← OrderAction.QuasiIsogeny.trans_assoc,
    nonnegativeFrameFrobenius_trans_signed Φ p hcard hFrob k n hk hkn ed e,
    nonnegativeFrameFrobenius_trans_signed Φ p hcard hFrob (k + n) m hkn hknm'
      (shift_trans ed e) e',
    nonnegativeFrameFrobenius_trans_signed Φ p hcard hFrob k (n + m) hk hknm ed
      (shift_trans e e')]
  apply nonnegativeFrameFrobenius_congr
  exact add_assoc k n m

/-- The whole comparison at zero is the actual rational identity of the frame. -/
theorem signedFrameFrobenius_zero (a : κ →ₐ[𝒪[K]] S) :
    signedFrameFrobenius Φ p hcard hFrob 0 (shift_zero a) =
      OrderAction.QuasiIsogeny.refl (Φ.val.order.map a) := by
  rw [signedFrameFrobenius_of_nonneg Φ p hcard hFrob 0 le_rfl]
  apply OrderAction.QuasiIsogeny.ext
  change (nonnegativeFrameFrobenius Φ p hcard hFrob 0 le_rfl (shift_zero a)).hom =
    OrderAction.RationalHom.id _
  rw [nonnegativeFrameFrobenius_hom, ← OrderAction.RationalHom.ofHom_id]
  apply congrArg (OrderAction.RationalHom.ofHom (F := K))
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  rw [nonnegativeFrameFrobenius_coordinates Φ p hcard 0 le_rfl (shift_zero a) a.toRingHom]
  change (CoordinateMap.frobeniusPow (R := κ) p (f * 0)).map a.toRingHom = CoordinateMap.id
  rw [Nat.mul_zero, CoordinateMap.frobeniusPow_zero, CoordinateMap.map_id]

/-- The opposite signed exponent gives the actual inverse comparison. -/
theorem signedFrameFrobenius_symm (n : ℤ) (e : shift n b = a) :
    (signedFrameFrobenius Φ p hcard hFrob n e).symm =
      signedFrameFrobenius Φ p hcard hFrob (-n) (shift_reverse e) := by
  apply OrderAction.QuasiIsogeny.trans_left_cancel
    (signedFrameFrobenius Φ p hcard hFrob n e)
  rw [OrderAction.QuasiIsogeny.self_trans_symm,
    signedFrameFrobenius_trans Φ p hcard hFrob n (-n) e (shift_reverse e)]
  exact ((signedFrameFrobenius_congr Φ p hcard hFrob (add_neg_cancel n) _
    (shift_zero a)).trans (signedFrameFrobenius_zero Φ p hcard hFrob a)).symm

private theorem signedFrameFrobenius_natural_of_nonneg (n : ℤ) (hn : 0 ≤ n)
    (e : shift n b = a) (g : OrderAction.QuasiIsogeny K Φ.val.order Φ.val.order) :
    (signedFrameFrobenius Φ p hcard hFrob n e).trans (g.map b) =
      (g.map a).trans (signedFrameFrobenius Φ p hcard hFrob n e) := by
  lift n to ℕ using hn
  subst a
  rw [signedFrameFrobenius_natCast]
  apply OrderAction.QuasiIsogeny.ext
  exact shiftedFrameFrobeniusQuasiIsogeny_natural Φ p hcard n (hFrob n) b g.hom

/-- Signed Frobenius commutes with actual frame quasi-endomorphisms after shifting
the coefficients of the source endomorphism. -/
theorem signedFrameFrobenius_natural (n : ℤ) (e : shift n b = a)
    (g : OrderAction.QuasiIsogeny K Φ.val.order Φ.val.order) :
    (signedFrameFrobenius Φ p hcard hFrob n e).trans (g.map b) =
      (g.map a).trans (signedFrameFrobenius Φ p hcard hFrob n e) := by
  by_cases hn : 0 ≤ n
  · exact signedFrameFrobenius_natural_of_nonneg Φ p hcard hFrob n hn e g
  · have ht := signedFrameFrobenius_natural_of_nonneg Φ p hcard hFrob (-n) (by omega)
      (shift_reverse e) g
    rw [← signedFrameFrobenius_symm Φ p hcard hFrob n e] at ht
    simpa only [OrderAction.QuasiIsogeny.symm_symm] using
      (OrderAction.QuasiIsogeny.square_reverse (g.map b) _ _ (g.map a) ht.symm).symm

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue
