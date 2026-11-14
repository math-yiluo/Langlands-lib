import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicHighestDerivativePairingProof
import Langlands.Representation.Classification.MirabolicDerivativeContragredient

/-!
# All-field port of `Langlands.Representation.Classification.MirabolicDerivativeContragredient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.MirabolicDerivativeContragredient` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient
open Langlands.Classification.MirabolicDerivativeContragredient hiding exists_derivative_hom_contragredient exists_determinant_pairing mirabolicDerivativeOfOrder_restriction mirabolicRankCast_restriction
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.AllFieldBZ.Derivative
universe uG uF uV uW

section Contragredient
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Contragredient
variable {F : LocalFieldPackage.{uF}} {T : F.TopologicalData}

section Bridge
/-- Restriction to the mirabolic subgroup commutes with the rank transports. -/
theorem mirabolicRankCast_restriction {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (a + 1) F.Carrier)) :
    letI := T.topology
    (Langlands.AllFieldBZ.Derivative.mirabolicRankCast T h).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T a).obj X) =
      (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T b).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h').obj X) := by
  subst h
  rfl

/-- The order-`k` derivative of the restriction of a representation of `GL_(N+1)` to
`P_(N+1)` is its order-`k` `GL` derivative. -/
theorem mirabolicDerivativeOfOrder_restriction
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)) :
    letI := T.topology
    (Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj X) =
      (Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (N + 1) k hk.2).obj X := by
  let := T.topology
  rw [Langlands.AllFieldBZ.Derivative.generalLinearDerivative_of_pos T ψ (N + 1) k hk.2 hk.1]
  exact congrArg (Langlands.AllFieldBZ.Derivative.mirabolicDerivative T ψ (N + 1 - k) (k - 1)).obj
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
    (f : letI := T.topology; W ⟶ (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f)) :
    letI := T.topology
    ∃ β : InvariantBilinear.forms W.representation
        ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π').representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      ∀ w : W, (∀ y, β.val w y = 0) → w = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1)
  let u : W →ₗ[ℂ] π := (SmoothRep.hom f).toLinearMap
  let e : (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π' ≃ₗ[ℂ] SmoothDual π.representation :=
    Φ.toLinearEquiv
  have hu (g : mirabolic N F.Carrier) (w : W) :
      u (W.representation g w) = π.representation g.val (u w) :=
    LinearMap.congr_fun ((SmoothRep.hom f).isIntertwining' g) w
  have he (g : mirabolic N F.Carrier) (y : (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π') :
      e (((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π').representation g y) =
        (T.determinantPowerCharacter (N + 1) 1 g.val : ℂ) •
          smoothContragredient π.representation g.val (e y) :=
    LinearMap.congr_fun (Φ.toIntertwiningMap.isIntertwining' g.val) y
  let β₀ : W →ₗ[ℂ] (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π' →ₗ[ℂ] ℂ :=
    ((smoothDualPairing π.representation).compl₁₂ e.toLinearMap u).flip
  refine ⟨⟨β₀, fun g w y => ?_⟩, fun w hw => ?_⟩
  · change smoothDualPairing π.representation
        (e (((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π').representation g y))
        (u (W.representation g w)) =
      _ * smoothDualPairing π.representation (e y) (u w)
    rw [he, hu, map_smul, LinearMap.smul_apply, smoothDualPairing_invariant, smul_eq_mul,
      coe_realPowerCharacter, Real.rpow_one]
  · apply hf
    change u w = u 0
    rw [map_zero]
    apply smoothBidual_injective_of_compact_cofinal (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T (N + 1))
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
/-- Let `W` pair with `π'|P` by a `|det|`-covariant form nondegenerate in `W`, and let
`k > 0` be the level of `W`. Every irreducible subrepresentation `σ` of `W^(k)` then
receives a nonzero map from the order-`k` derivative of `π'` to `σ̃`. -/
theorem exists_derivative_hom_contragredient
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ}
    (π' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (W : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (β : letI := T.topology
      InvariantBilinear.forms W.representation
        ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π').representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)))
    (hβ : ∀ w : W, (∀ y, β.val w y = 0) → w = 0)
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) (hlevel : Langlands.AllFieldBZ.Derivative.level T ψ W = k)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier))
    (hσ : letI := T.topology
      Langlands.Classification.IsIrreducibleSubrepresentation
        ((Langlands.AllFieldBZ.Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation σ.representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∃ q : (Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (N + 1) k hk.2).obj π' ⟶ σ.contragredient,
      SmoothRep.hom q ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (N + 1 - k)
  obtain ⟨-, hnz, hhigh⟩ := (Langlands.AllFieldBZ.Derivative.level_eq_iff T ψ hk.1 W).mp hlevel
  obtain ⟨γ, hγ⟩ := Langlands.AllFieldBZ.Derivative.mirabolicHighestDerivativePairing F T ψ N W
    ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T N).obj π') k hk ((Langlands.AllFieldBZ.Derivative.hasNonzeroDerivative_iff T ψ hk W).mp hnz)
    (fun j hj hkj => not_nontrivial_iff_subsingleton.mp fun h => hhigh hkj hj.2 ⟨hj, h⟩)
    β hβ
  obtain ⟨hirr, ι, hι⟩ := hσ
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible σ.representation hirr
  rw [← mirabolicDerivativeOfOrder_restriction ψ N k hk π']
  exact ⟨pairingContragredientHom γ ι, pairingContragredientHom_ne_zero γ hγ ι hι hv₀⟩

end Map
end Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient
