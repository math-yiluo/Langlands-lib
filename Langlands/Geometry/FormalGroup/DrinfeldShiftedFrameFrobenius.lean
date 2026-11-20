import Langlands.Geometry.FormalGroup.DrinfeldResidueFrobenius
import Langlands.Geometry.FormalGroup.SpecialFrameFrobeniusStatement

/-! # Relative Frobenius from the shifted frame -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open ValuativeRel ModuleLaw MvPowerSeries

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Integral

variable {κ : Type v} [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {S : Type v} [CommRing S] [Algebra 𝒪[K] S]
variable {Λ : Type s} [Ring Λ] [Algebra 𝒪[K] Λ]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw 𝒪[K] κ σ} {N : ModuleLaw 𝒪[K] κ τ}

/-- The actual final identification of the positive relative Frobenius target with the original frame. -/
def frobeniusTargetIso (E : OrderAction Λ M) (n : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    OrderAction.Iso ((E.map (frobenius K κ ^ (n : ℤ)).toAlgHom).map (shift (n : ℤ) ψ))
      (E.map ψ) :=
  let θ := (frobenius K κ ^ (n : ℤ)).toAlgHom
  let a := shift (n : ℤ) ψ
  (E.mapCompIso θ a).trans
    (E.mapReAlgebraIso _ _ rfl (a.comp θ) ψ
      (congrArg AlgHom.toRingHom (shift_comp_frobenius (n : ℤ) ψ)))

/-- Recovering the original frame coefficients has the actual identity series. -/
theorem frobeniusTargetIso_hom_coordinates (E : OrderAction Λ M) (n : ℕ)
    (ψ : κ →ₐ[𝒪[K]] S) :
    (frobeniusTargetIso E n ψ).hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  OrderAction.Iso.trans_hom_coordinates_id _ _ rfl
    (OrderAction.mapReAlgebraIso_hom_coordinates _ _ _ _ _ _ _)

variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)

/-- For a nonnegative shift the relative Frobenius is an actual integral full-order map. -/
def shiftedFrameFrobeniusHom (E : OrderAction Λ M) (n : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    OrderAction.Hom (E.map (shift (n : ℤ) ψ)) (E.map ψ) :=
  let θ := (frobenius K κ ^ (n : ℤ)).toAlgHom
  let a := shift (n : ℤ) ψ
  (frobeniusTargetIso E n ψ).hom.comp
    ((E.frobeniusHom p (f * n) θ (frobenius_natCast_toRingHom K κ p hcard n)).map a)

/-- The forward map has the actual residue-cardinal power series over the target algebra. -/
theorem shiftedFrameFrobeniusHom_series (E : OrderAction Λ M) (n : ℕ)
    (ψ : κ →ₐ[𝒪[K]] S) (i : σ) :
    (shiftedFrameFrobeniusHom p hcard E n ψ).val.toHom.toCoordinateMap.series i =
      X i ^ (Nat.card 𝓀[K] ^ n) := by
  change (((frobeniusTargetIso E n ψ).hom.val.toHom.toCoordinateMap).comp
    ((CoordinateMap.frobeniusPow (R := κ) p (f * n)).map (shift (n : ℤ) ψ).toRingHom)).series i = _
  rw [frobeniusTargetIso_hom_coordinates, CoordinateMap.id_comp, CoordinateMap.map_series,
    CoordinateMap.frobeniusPow_series, map_pow, MvPowerSeries.map_X, hcard, pow_mul]

/-- The power map can be extended along any coefficient map out of the frame field. -/
theorem shiftedFrameFrobeniusHom_coordinates (E : OrderAction Λ M) (n : ℕ)
    (ψ : κ →ₐ[𝒪[K]] S) (a : κ →+* S) :
    (shiftedFrameFrobeniusHom p hcard E n ψ).val.toHom.toCoordinateMap =
      (CoordinateMap.frobeniusPow (R := κ) p (f * n)).map a := by
  apply CoordinateMap.ext
  funext i
  rw [shiftedFrameFrobeniusHom_series p hcard, CoordinateMap.map_series,
    CoordinateMap.frobeniusPow_series, map_pow, MvPowerSeries.map_X, hcard, pow_mul]

/-- Relative Frobenius commutes with every actual frame homomorphism and its shifted extension. -/
theorem shiftedFrameFrobeniusHom_natural (E : OrderAction Λ M) (E' : OrderAction Λ N)
    (g : ModuleLaw.Hom M N) (n : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    (g.map ψ).comp (shiftedFrameFrobeniusHom p hcard E n ψ).val =
      (shiftedFrameFrobeniusHom p hcard E' n ψ).val.comp (g.map (shift (n : ℤ) ψ)) := by
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  let a := shift (n : ℤ) ψ
  let g₀ := g.toHom.toCoordinateMap
  change (g₀.map ψ.toRingHom).comp
      (shiftedFrameFrobeniusHom p hcard E n ψ).val.toHom.toCoordinateMap =
    (shiftedFrameFrobeniusHom p hcard E' n ψ).val.toHom.toCoordinateMap.comp (g₀.map a.toRingHom)
  rw [shiftedFrameFrobeniusHom_coordinates p hcard E n ψ a.toRingHom,
    shiftedFrameFrobeniusHom_coordinates p hcard E' n ψ a.toRingHom]
  have hg := congrArg (fun h : CoordinateMap κ σ τ => h.map a.toRingHom)
    (CoordinateMap.frobeniusPow_natural p (f * n) g₀)
  have hθ : a.toRingHom.comp (iterateFrobenius κ p (f * n)) = ψ.toRingHom := by
    rw [← frobenius_natCast_toRingHom K κ p hcard n]
    exact congrArg AlgHom.toRingHom (shift_comp_frobenius (n : ℤ) ψ)
  rw [CoordinateMap.map_comp, CoordinateMap.map_comp, CoordinateMap.map_ringHom_comp, hθ] at hg
  exact hg.symm

/-- Relative Frobenius commutes with all whole tensor-product maps of the underlying frames. -/
theorem shiftedFrameFrobeniusRationalHom_natural (E : OrderAction Λ M) (E' : OrderAction Λ N)
    (g : ModuleLaw.RationalHom K M N) (n : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.map ψ g)
      (ModuleLaw.RationalHom.ofHom (shiftedFrameFrobeniusHom p hcard E n ψ).val) =
    ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom (shiftedFrameFrobeniusHom p hcard E' n ψ).val)
      (ModuleLaw.RationalHom.map (shift (n : ℤ) ψ) g) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ h₁ h₂ =>
    simp only [_root_.map_add, ModuleLaw.RationalHom.add_comp, ModuleLaw.RationalHom.comp_add, h₁, h₂]
  | tmul a g =>
    simp only [ModuleLaw.RationalHom.map_tmul, ModuleLaw.RationalHom.ofHom_apply,
      ModuleLaw.RationalHom.comp_tmul, mul_one, one_mul,
      shiftedFrameFrobeniusHom_natural p hcard E E' g n ψ]

omit [ExpChar κ p] in
/-- The zero residue shift compares to the original frame by identity coordinates. -/
def shiftedFrameZeroIso (E : OrderAction Λ M) (ψ : κ →ₐ[𝒪[K]] S) :
    OrderAction.Iso (E.map (shift 0 ψ)) (E.map ψ) :=
  E.mapReAlgebraIso _ _ rfl _ _ (congrArg AlgHom.toRingHom (shift_zero ψ))

/-- At exponent zero the relative map is the actual identity-coordinate comparison. -/
theorem shiftedFrameFrobeniusHom_zero (E : OrderAction Λ M) (ψ : κ →ₐ[𝒪[K]] S) :
    shiftedFrameFrobeniusHom p hcard E 0 ψ = (shiftedFrameZeroIso E ψ).hom := by
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (shiftedFrameFrobeniusHom p hcard E 0 ψ).val.toHom.toCoordinateMap =
    (shiftedFrameZeroIso E ψ).hom.val.toHom.toCoordinateMap
  rw [shiftedFrameFrobeniusHom_coordinates p hcard E 0 ψ ψ.toRingHom, Nat.mul_zero,
    CoordinateMap.frobeniusPow_zero, CoordinateMap.map_id]
  exact (OrderAction.mapReAlgebraIso_hom_coordinates _ _ _ _ _ _ _).symm

omit [ExpChar κ p] in
/-- The two successive residue shifts and their sum have the same actual frame
through the identity coordinate comparison. -/
def shiftedFrameAddIso (E : OrderAction Λ M) (n m : ℕ) (ψ : κ →ₐ[𝒪[K]] S) :
    OrderAction.Iso (E.map (shift (m : ℤ) (shift (n : ℤ) ψ)))
      (E.map (shift ((n + m : ℕ) : ℤ) ψ)) :=
  E.mapReAlgebraIso _ _ rfl _ _ (congrArg AlgHom.toRingHom
    (by rw [Int.natCast_add, shift_shift]))

/-- The actual positive relative maps compose, with the source identified by
the sum of the residue shifts. -/
theorem shiftedFrameFrobeniusHom_add (E : OrderAction Λ M) (n m : ℕ)
    (ψ : κ →ₐ[𝒪[K]] S) :
    (shiftedFrameFrobeniusHom p hcard E n ψ).comp
      (shiftedFrameFrobeniusHom p hcard E m (shift (n : ℤ) ψ)) =
    (shiftedFrameFrobeniusHom p hcard E (n + m) ψ).comp
      (shiftedFrameAddIso E n m ψ).hom := by
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (shiftedFrameFrobeniusHom p hcard E n ψ).val.toHom.toCoordinateMap.comp
      (shiftedFrameFrobeniusHom p hcard E m (shift (n : ℤ) ψ)).val.toHom.toCoordinateMap =
    (shiftedFrameFrobeniusHom p hcard E (n + m) ψ).val.toHom.toCoordinateMap.comp
      (shiftedFrameAddIso E n m ψ).hom.val.toHom.toCoordinateMap
  have hi : (shiftedFrameAddIso E n m ψ).hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
    OrderAction.mapReAlgebraIso_hom_coordinates _ _ _ _ _ _ _
  rw [hi, CoordinateMap.comp_id,
    shiftedFrameFrobeniusHom_coordinates p hcard E n ψ ψ.toRingHom,
    shiftedFrameFrobeniusHom_coordinates p hcard E m (shift (n : ℤ) ψ) ψ.toRingHom,
    shiftedFrameFrobeniusHom_coordinates p hcard E (n + m) ψ ψ.toRingHom,
    Nat.mul_add, Nat.add_comm (f * n) (f * m), ← CoordinateMap.map_comp,
    CoordinateMap.frobeniusPow_add]

end Integral

section SpecialFrame

open CentralDivision

variable {κ : Type u} [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
variable {D : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)

/-- A proof of the exact whole inverse target yields the positive frame comparison over the actual residue map. -/
def shiftedFrameFrobeniusQuasiIsogeny (n : ℕ)
    (h : SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * n))
    (ψ : κ →ₐ[𝒪[K]] S) :
    OrderAction.QuasiIsogeny K (Φ.val.order.map (shift (n : ℤ) ψ)) (Φ.val.order.map ψ) :=
  let θ := (frobenius K κ ^ (n : ℤ)).toAlgHom
  let a := shift (n : ℤ) ψ
  ((SpecialModule.frobeniusQuasiIsogenyOfStatement Φ p (f * n) h θ
    (frobenius_natCast_toRingHom K κ p hcard n)).map a).trans
    (OrderAction.QuasiIsogeny.ofIso (frobeniusTargetIso Φ.val.order n ψ))

/-- The positive comparison's whole forward tensor is exactly the rationalized integral map. -/
theorem shiftedFrameFrobeniusQuasiIsogeny_hom (n : ℕ)
    (h : SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * n))
    (ψ : κ →ₐ[𝒪[K]] S) :
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n h ψ).hom =
      OrderAction.RationalHom.ofHom (shiftedFrameFrobeniusHom p hcard Φ.val.order n ψ) := by
  change (OrderAction.RationalHom.ofHom (frobeniusTargetIso Φ.val.order n ψ).hom).comp
    (OrderAction.RationalHom.map _ (SpecialModule.frobeniusQuasiIsogenyOfStatement Φ p (f * n)
      h _ _).hom) = _
  rw [SpecialModule.frobeniusQuasiIsogenyOfStatement_hom, OrderAction.RationalHom.map_ofHom,
    ← OrderAction.RationalHom.ofHom_comp]
  rfl

/-- The whole positive comparison commutes with any rational full-order endomorphism of the frame. -/
theorem shiftedFrameFrobeniusQuasiIsogeny_natural (n : ℕ)
    (h : SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * n))
    (ψ : κ →ₐ[𝒪[K]] S) (g : OrderAction.RationalHom K Φ.val.order Φ.val.order) :
    (OrderAction.RationalHom.map ψ g).comp
      (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n h ψ).hom =
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n h ψ).hom.comp
      (OrderAction.RationalHom.map (shift (n : ℤ) ψ) g) := by
  rw [shiftedFrameFrobeniusQuasiIsogeny_hom]
  apply OrderAction.RationalHom.ext
  exact shiftedFrameFrobeniusRationalHom_natural p hcard Φ.val.order Φ.val.order g.val n ψ

/-- The zero whole comparison rationalizes the actual identity-coordinate isomorphism. -/
theorem shiftedFrameFrobeniusQuasiIsogeny_zero
    (h : SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * 0))
    (ψ : κ →ₐ[𝒪[K]] S) :
    shiftedFrameFrobeniusQuasiIsogeny Φ p hcard 0 h ψ =
      OrderAction.QuasiIsogeny.ofIso (shiftedFrameZeroIso Φ.val.order ψ) := by
  apply OrderAction.QuasiIsogeny.ext
  rw [shiftedFrameFrobeniusQuasiIsogeny_hom, shiftedFrameFrobeniusHom_zero]
  rfl

/-- The whole positive comparisons compose with the same actual shift-addition isomorphism. -/
theorem shiftedFrameFrobeniusQuasiIsogeny_add (n m : ℕ)
    (h : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
    (ψ : κ →ₐ[𝒪[K]] S) :
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard m (h m) (shift (n : ℤ) ψ)).trans
      (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n (h n) ψ) =
    (OrderAction.QuasiIsogeny.ofIso (F := K) (shiftedFrameAddIso Φ.val.order n m ψ)).trans
      (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard (n + m) (h (n + m)) ψ) := by
  apply OrderAction.QuasiIsogeny.ext
  change (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard n (h n) ψ).hom.comp
      (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard m (h m) (shift (n : ℤ) ψ)).hom =
    (shiftedFrameFrobeniusQuasiIsogeny Φ p hcard (n + m) (h (n + m)) ψ).hom.comp
      (OrderAction.RationalHom.ofHom (shiftedFrameAddIso Φ.val.order n m ψ).hom)
  rw [shiftedFrameFrobeniusQuasiIsogeny_hom, shiftedFrameFrobeniusQuasiIsogeny_hom,
    shiftedFrameFrobeniusQuasiIsogeny_hom, ← OrderAction.RationalHom.ofHom_comp,
    ← OrderAction.RationalHom.ofHom_comp, shiftedFrameFrobeniusHom_add]

end SpecialFrame

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue
