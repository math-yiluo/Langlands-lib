import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof

/-!
# Contragredient maps from highest-derivative pairings

Let `W ⊆ π|P` be a representation of the mirabolic subgroup `P_(N+1)` inside the
restriction of a representation `π` of `GL_(N+1)`, and let `π' ≃ |det| π̃`. The
natural pairing of `π` and `π̃` restricts to a `|det|`-covariant pairing of `W` and
`π'|P`, nondegenerate in `W`. If `k > 0` is the level of `W`, the highest-derivative
pairing (BZ77 Proposition 3.8) then gives, for every irreducible subrepresentation
`σ` of `W^(k)`, a nonzero map from the order-`k` `GL` derivative of `π'` to `σ̃`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.MirabolicDerivativeContragredient

open GeneralLinear PadicField.TopologicalData Derivative

universe uG uF uV uW

section Contragredient

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An invariant pairing `γ` of `X` and `Y` and an intertwiner `ι : σ → X` give the
intertwiner `Y ⟶ σ̃`, `y ↦ (v ↦ γ (ι v) y)`, into the smooth contragredient of `σ`. -/
def pairingContragredientHom {X : SmoothRep.{0, uG, uW} ℂ G} {Y σ : SmoothRep.{0, uG, uV} ℂ G}
    (γ : InvariantBilinear.forms X.representation Y.representation (fun _ => (1 : ℂ)))
    (ι : σ.representation.IntertwiningMap X.representation) : Y ⟶ σ.contragredient :=
  SmoothRep.ofHom (A := Y) (B := σ.contragredient) (smoothLift Y.isSmooth
    { toLinearMap := (γ.val.comp ι.toLinearMap).flip
      isIntertwining' := fun g => by
        ext y v
        change γ.val (ι v) (Y.representation g y) = γ.val (ι (σ.representation g⁻¹ v)) y
        have h1 : ι (σ.representation g⁻¹ v) = X.representation g⁻¹ (ι v) :=
          LinearMap.congr_fun (ι.isIntertwining' g⁻¹) v
        have h2 : γ.val (X.representation g (X.representation g⁻¹ (ι v)))
            (Y.representation g y) = 1 * γ.val (X.representation g⁻¹ (ι v)) y :=
          γ.property g _ y
        rw [Representation.self_inv_apply, one_mul] at h2
        rw [h1, h2] })

/-- The functional `pairingContragredientHom γ ι y` takes `v` to `γ (ι v) y`. -/
theorem pairingContragredientHom_apply {X : SmoothRep.{0, uG, uW} ℂ G}
    {Y σ : SmoothRep.{0, uG, uV} ℂ G}
    (γ : InvariantBilinear.forms X.representation Y.representation (fun _ => (1 : ℂ)))
    (ι : σ.representation.IntertwiningMap X.representation) (y : Y) (v : σ) :
    ((SmoothRep.hom (pairingContragredientHom γ ι)).toLinearMap y).val v = γ.val (ι v) y :=
  rfl

/-- The map `pairingContragredientHom γ ι` is nonzero when `γ` is nondegenerate in `X`,
`ι` is injective and `σ` is nonzero. -/
theorem pairingContragredientHom_ne_zero {X : SmoothRep.{0, uG, uW} ℂ G}
    {Y σ : SmoothRep.{0, uG, uV} ℂ G}
    (γ : InvariantBilinear.forms X.representation Y.representation (fun _ => (1 : ℂ)))
    (hγ : ∀ x : X, (∀ y : Y, γ.val x y = 0) → x = 0)
    (ι : σ.representation.IntertwiningMap X.representation) (hι : Function.Injective ι)
    {v₀ : σ} (hv₀ : v₀ ≠ 0) :
    SmoothRep.hom (pairingContragredientHom γ ι) ≠ 0 := by
  intro hq
  have hιv : ι v₀ ≠ 0 := fun h => hv₀ (hι (h.trans (map_zero ι).symm))
  obtain ⟨y, hy⟩ : ∃ y, γ.val (ι v₀) y ≠ 0 := by
    by_contra! H
    exact hιv (hγ _ H)
  apply hy
  rw [← pairingContragredientHom_apply γ ι y v₀]
  have h0 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap hq) y
  exact congrArg (fun z : SmoothDual σ.representation => z.val v₀) h0

end Contragredient

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

section Bridge

/-- Restriction to the mirabolic subgroup commutes with the rank transports. -/
theorem mirabolicRankCast_restriction {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (a + 1) F.Carrier)) :
    letI := T.topology
    (mirabolicRankCast T h).obj ((generalLinearRestriction T a).obj X) =
      (generalLinearRestriction T b).obj ((generalLinearRankCast T h').obj X) := by
  subst h
  rfl

/-- The order-`k` derivative of the restriction of a representation of `GL_(N+1)` to
`P_(N+1)` is its order-`k` `GL` derivative. -/
theorem mirabolicDerivativeOfOrder_restriction
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)) :
    letI := T.topology
    (mirabolicDerivativeOfOrder T ψ N k hk).obj ((generalLinearRestriction T N).obj X) =
      (generalLinearDerivative T ψ (N + 1) k hk.2).obj X := by
  let := T.topology
  rw [generalLinearDerivative_of_pos T ψ (N + 1) k hk.2 hk.1]
  exact congrArg (mirabolicDerivative T ψ (N + 1 - k) (k - 1)).obj
    (mirabolicRankCast_restriction (mirabolic_rank_eq_of_order hk)
      (rank_eq_of_pos_le hk.2 hk.1) X)

end Bridge

section Pairing

open scoped NNReal

/-- If `π' ≃ |det| π̃` on `GL_(N+1)`, then a representation `W ⊆ π|P` pairs with `π'|P`
by a `|det|`-covariant form nondegenerate in `W`. -/
theorem exists_determinant_pairing {N : ℕ}
    (π π' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (Φ : letI := T.topology
      letI := T.generalLinearTopologicalGroup (N + 1)
      π'.representation.Equiv (twist (T.determinantPowerCharacter (N + 1) 1)
        (smoothContragredient π.representation)))
    (W : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (f : letI := T.topology; W ⟶ (generalLinearRestriction T N).obj π)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f)) :
    letI := T.topology
    ∃ β : InvariantBilinear.forms W.representation
        ((generalLinearRestriction T N).obj π').representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      ∀ w : W, (∀ y, β.val w y = 0) → w = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1)
  let u : W →ₗ[ℂ] π := (SmoothRep.hom f).toLinearMap
  let e : (generalLinearRestriction T N).obj π' ≃ₗ[ℂ] SmoothDual π.representation :=
    Φ.toLinearEquiv
  have hu (g : mirabolic N F.Carrier) (w : W) :
      u (W.representation g w) = π.representation g.val (u w) :=
    LinearMap.congr_fun ((SmoothRep.hom f).isIntertwining' g) w
  have he (g : mirabolic N F.Carrier) (y : (generalLinearRestriction T N).obj π') :
      e (((generalLinearRestriction T N).obj π').representation g y) =
        (T.determinantPowerCharacter (N + 1) 1 g.val : ℂ) •
          smoothContragredient π.representation g.val (e y) :=
    LinearMap.congr_fun (Φ.toIntertwiningMap.isIntertwining' g.val) y
  let β₀ : W →ₗ[ℂ] (generalLinearRestriction T N).obj π' →ₗ[ℂ] ℂ :=
    ((smoothDualPairing π.representation).compl₁₂ e.toLinearMap u).flip
  refine ⟨⟨β₀, fun g w y => ?_⟩, fun w hw => ?_⟩
  · change smoothDualPairing π.representation
        (e (((generalLinearRestriction T N).obj π').representation g y))
        (u (W.representation g w)) =
      _ * smoothDualPairing π.representation (e y) (u w)
    rw [he, hu, map_smul, LinearMap.smul_apply, smoothDualPairing_invariant, smul_eq_mul,
      coe_realPowerCharacter, Real.rpow_one]
  · apply hf
    change u w = u 0
    rw [map_zero]
    apply smoothBidual_injective_of_compact_cofinal (compactOpen_cofinal F T (N + 1))
      π.representation π.isSmooth
    rw [map_zero]
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    obtain ⟨y, rfl⟩ := e.surjective ℓ
    exact hw y

end Pairing

section Map

open scoped NNReal

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra! h
  have := hirr
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [h v]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- Let `W` pair with `π'|P` by a `|det|`-covariant form nondegenerate in `W`, and let
`k > 0` be the level of `W`. Every irreducible subrepresentation `σ` of `W^(k)` then
receives a nonzero map from the order-`k` derivative of `π'` to `σ̃`. -/
theorem exists_derivative_hom_contragredient
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ}
    (π' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (W : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (β : letI := T.topology
      InvariantBilinear.forms W.representation
        ((generalLinearRestriction T N).obj π').representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)))
    (hβ : ∀ w : W, (∀ y, β.val w y = 0) → w = 0)
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) (hlevel : level T ψ W = k)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier))
    (hσ : letI := T.topology
      IsIrreducibleSubrepresentation
        ((mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation σ.representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∃ q : (generalLinearDerivative T ψ (N + 1) k hk.2).obj π' ⟶ σ.contragredient,
      SmoothRep.hom q ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1 - k)
  obtain ⟨-, hnz, hhigh⟩ := (level_eq_iff T ψ hk.1 W).mp hlevel
  obtain ⟨γ, hγ⟩ := mirabolicHighestDerivativePairing F T ψ N W
    ((generalLinearRestriction T N).obj π') k hk ((hasNonzeroDerivative_iff T ψ hk W).mp hnz)
    (fun j hj hkj => not_nontrivial_iff_subsingleton.mp fun h => hhigh hkj hj.2 ⟨hj, h⟩)
    β hβ
  obtain ⟨hirr, ι, hι⟩ := hσ
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible σ.representation hirr
  rw [← mirabolicDerivativeOfOrder_restriction ψ N k hk π']
  exact ⟨pairingContragredientHom γ ι, pairingContragredientHom_ne_zero γ hγ ι hι hv₀⟩

end Map

end Langlands.Classification.MirabolicDerivativeContragredient
