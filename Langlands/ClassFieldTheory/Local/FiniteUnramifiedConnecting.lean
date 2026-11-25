import Langlands.ClassFieldTheory.Local.FiniteLocalUnramifiedInvariant
import Langlands.ClassFieldTheory.Local.RationalConnecting

noncomputable section

open CategoryTheory groupCohomology Langlands.LocalClassField ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u v

section Carry

variable {G : Type v} [Group G] {n : ℕ} [NeZero n]
  (χ : G →* Multiplicative (ZMod n)) (z : ℤ)

private def cyclicRationalLift (g : G) : ℚ :=
  (z : ℚ) * ((χ g).toAdd.val : ℚ) / n

private theorem cyclicRationalLift_d (g h : G) :
    cyclicRationalLift χ z h - cyclicRationalLift χ z (g * h) + cyclicRationalLift χ z g =
      (z : ℚ) * (cyclicCarry (χ g).toAdd (χ h).toAdd : ℚ) := by
  simp only [cyclicRationalLift, map_mul, toAdd_mul, cyclicCarry_rational]
  ring

private theorem rationalClass_integer (k : ℤ) : rationalClass (k : ℚ) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨k, by simp⟩)

private def cyclicRationalCharacter : Additive G →+ trivialRationalQuotientCoefficients G where
  toFun g := ULift.up (rationalClass (cyclicRationalLift χ z g.toMul))
  map_zero' := by
    apply ULift.ext
    change rationalClass (cyclicRationalLift χ z 1) = 0
    simp [cyclicRationalLift]
  map_add' g h := by
    apply ULift.ext
    change rationalClass (cyclicRationalLift χ z (g.toMul * h.toMul)) =
      rationalClass (cyclicRationalLift χ z g.toMul) + rationalClass (cyclicRationalLift χ z h.toMul)
    have hz := congrArg rationalClass (cyclicRationalLift_d χ z g.toMul h.toMul)
    rw [← Int.cast_natCast, ← Int.cast_mul, rationalClass_integer] at hz
    simp only [map_add, map_sub, sub_add_eq_add_sub, sub_eq_zero] at hz
    exact hz.symm.trans (add_comm _ _)

private theorem cyclicRationalCharacter_generator (σ : G)
    (hσ : χ σ = Multiplicative.ofAdd (1 : ZMod n)) :
    (cyclicRationalCharacter χ z (.ofMul σ)).down = rationalClass ((z : ℚ) / n) := by
  change rationalClass (cyclicRationalLift χ z σ) = _
  unfold cyclicRationalLift
  rw [hσ, toAdd_ofAdd]
  by_cases hn : n = 1
  · subst n
    simp [ZMod.val_one_eq_one_mod, rationalClass_integer]
  · rw [ZMod.val_one'' hn, Nat.cast_one, mul_one]

end Carry

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]
  (hcont : Continuous (algebraMap K L)) (he : localRamificationFactor K L = 1)

/-- Normalized valuation as an equivariant map from actual units to trivial integer coefficients. -/
def localUnramifiedValuationCoefficients :
    unitsRepresentation K L ⟶ Langlands.Tate.integralTrivial Gal(L/K) :=
  Rep.ofHom ⟨{
    toFun a := ULift.up (normalizedUnitOrder L a)
    map_add' a b := ULift.ext (map_add (normalizedUnitOrder L) a b)
    map_smul' z a := ULift.ext (map_zsmul (normalizedUnitOrder L) z.down a) }, by
    intro σ
    apply LinearMap.ext
    intro a₀
    apply ULift.ext
    let a : Additive Lˣ := a₀
    let b : Additive Lˣ := (unitsRepresentation K L).ρ σ a₀
    change normalizedUnitOrder L b = normalizedUnitOrder L a
    have hnorm : normUnits K L b.toMul = normUnits K L a.toMul :=
      Units.ext (Algebra.norm_eq_of_algEquiv σ (a.toMul : L))
    have hord := congrArg (fun b : Kˣ => normalizedUnitOrder K (.ofMul b)) hnorm
    rw [normalizedUnitOrder_norm_of_unramified K L hcont he,
      normalizedUnitOrder_norm_of_unramified K L hcont he, ofMul_toMul, ofMul_toMul] at hord
    have hd : (Module.finrank K L : ℤ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := K) (M := L)).ne'
    exact mul_left_cancel₀ hd hord⟩

theorem localUnramifiedValuationCoefficients_baseUnit (a : Kˣ) :
    (localUnramifiedValuationCoefficients K L hcont he).hom (baseUnit K L a) =
      ULift.up (normalizedUnitOrder K (.ofMul a)) := by
  apply ULift.ext
  change normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) a)) = _
  rw [normalizedUnitOrder_map K L, he, Nat.cast_one, one_mul]

variable [IsGalois K L] (χ : Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)))

/-- Valuation, inverse connecting map and evaluation at the generator of the cyclic coordinate. -/
def serreFiniteUnramifiedInvariant (x : relativeCohomology K L 2) : RationalModIntegers :=
  ((H1IsoOfIsTrivial (trivialRationalQuotientCoefficients Gal(L/K))).hom
    ((rationalConnectingIso Gal(L/K)).inv
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (localUnramifiedValuationCoefficients K L hcont he) 2 x))
    (.ofMul (cyclicCoordinateGenerator χ))).down

/-- The finite invariant agrees with Serre's corrected inverse-connecting construction. -/
theorem finiteLocalUnramifiedInvariant_eq_serre (x : relativeCohomology K L 2) :
    finiteLocalUnramifiedInvariant K L hcont he χ x =
      serreFiniteUnramifiedInvariant K L hcont he χ x := by
  let : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨a, rfl⟩ := exists_finiteLocal_cyclicClass K L χ x
  let G := Gal(L/K)
  let z := normalizedUnitOrder K (.ofMul a)
  let V := trivialRationalQuotientCoefficients G
  let c : cocycles₁ V := (cocycles₁IsoOfIsTrivial V).inv (cyclicRationalCharacter χ.toMonoidHom z)
  let y : H1 V := H1π V c
  let φ := localUnramifiedValuationCoefficients K L hcont he
  have hδ : (rationalConnectingIso G).hom y =
      groupCohomology.map (MonoidHom.id G) φ 2 (cyclicClass K L χ.toMonoidHom a) := by
    rw [rationalConnectingIso_hom, cyclicClass, H2π_comp_map_apply]
    let lift (g : G) : trivialRationalCoefficients G :=
      ULift.up (cyclicRationalLift χ.toMonoidHom z g)
    let cv := mapCocycles₂ (MonoidHom.id G) φ (cyclicUnitCocycle K L χ.toMonoidHom a)
    refine δ₁_apply (rationalCoefficientSequence_shortExact G) c lift ?_ cv ?_
    · funext g
      rfl
    · funext gh
      obtain ⟨g, h⟩ := gh
      have hv : cv (g, h) = cyclicCarry (χ g).toAdd (χ h).toAdd • (ULift.up z : IntegerScalars.{v}) := by
        change φ.hom (cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a) = _
        rw [map_nsmul, localUnramifiedValuationCoefficients_baseUnit]
      apply ULift.ext
      change ((rationalCoefficientSequence G).f.hom (cv (g, h))).down =
        cyclicRationalLift χ.toMonoidHom z h - cyclicRationalLift χ.toMonoidHom z (g * h) +
          cyclicRationalLift χ.toMonoidHom z g
      rw [rationalCoefficientSequence_f_down, hv]
      change ((cyclicCarry (χ g).toAdd (χ h).toAdd • z : ℤ) : ℚ) =
        _
      rw [cyclicRationalLift_d, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
      simp only [MulEquiv.coe_toMonoidHom, mul_comm]
  rw [finiteLocalUnramifiedInvariant_cyclicClass]
  change _ = ((H1IsoOfIsTrivial V).hom ((rationalConnectingIso G).inv
    (groupCohomology.map (MonoidHom.id G) φ 2 (cyclicClass K L χ.toMonoidHom a)))
    (.ofMul (cyclicCoordinateGenerator χ))).down
  rw [← hδ, Iso.hom_inv_id_apply]
  change _ = ((H1IsoOfIsTrivial V).hom (H1π V c) (.ofMul (cyclicCoordinateGenerator χ))).down
  rw [H1IsoOfIsTrivial_H1π_apply_apply]
  exact (cyclicRationalCharacter_generator χ.toMonoidHom z (cyclicCoordinateGenerator χ)
    (χ.apply_symm_apply _)).symm

end Langlands.ClassFieldTheory.Local
