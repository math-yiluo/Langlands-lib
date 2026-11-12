import Langlands.Representation.Classification.BernsteinOrderZeroPositivity
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.LocalField.Uniformizer

/-!
# Eigenvectors of the uniformizer on shifted derivatives

If an irreducible subquotient of an admissible smooth representation has a central
element acting by the scalar `c`, then `c` is an eigenvalue of that element on the
representation itself. Shifted derivatives of irreducible representations of `GL_N`
are admissible. On `ν^(1/2) Ψ⁻ τ` the determinant twists cancel, so a matrix acts on
a radical-coinvariant class through its Levi image. Combining these, the shifted
derivative `ν^(1/2) Ψ⁻ τ` has positive central exponents as soon as every eigenvalue
of the Levi uniformizer scalar on the radical coinvariants of `τ` has norm less than
one. This is the reduction step of Bernstein 1984, §7.4.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV uG

/-! ## Eigenvectors in finite-dimensional invariant subspaces -/

/-- If `L` preserves a finite-dimensional subspace `W`, and a linear map `f` kills
`(L - c) W` but not `W`, then `L` has an eigenvector with eigenvalue `c` in `W`. -/
theorem exists_eigenvector_of_finiteDimensional {V U : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (L : V →ₗ[ℂ] V) (hL : ∀ w ∈ W, L w ∈ W) (f : V →ₗ[ℂ] U) (c : ℂ)
    (hf : ∀ w ∈ W, f (L w - c • w) = 0) {x : V} (hx : x ∈ W) (hfx : f x ≠ 0) :
    ∃ w ∈ W, w ≠ 0 ∧ L w = c • w := by
  by_contra h
  push Not at h
  let M : W →ₗ[ℂ] W := (L - c • LinearMap.id).restrict fun w hw => by
    simpa using W.sub_mem (hL w hw) (W.smul_mem c hw)
  have hM : ∀ w : W, (M w : V) = L w - c • w := fun w => by simp [M]
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hne
    apply h w w.2 (by simpa using hne)
    have := hM w
    rw [hw, Submodule.coe_zero] at this
    exact (sub_eq_zero.mp this.symm)
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨x, hx⟩
  apply hfx
  have := hM w
  rw [hw] at this
  rw [show x = L w - c • w from this]
  exact hf w w.2

/-! ## Eigenvectors in admissible representations -/

section Admissible

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- On an admissible smooth representation `B`, a central element `g₀` has eigenvalue
`c` as soon as some nonzero intertwiner from `B` sees `g₀` acting by `c`. -/
theorem exists_eigenvector_of_hom {B D : SmoothRep.{0, uG, uV} ℂ G} (hB : B.IsAdmissible)
    {g₀ : G} (hg₀ : ∀ g, g₀ * g = g * g₀) {c : ℂ}
    (hD : ∀ v : D, D.representation g₀ v = c • v) (f : B ⟶ D) {x : B}
    (hx : SmoothRep.hom f x ≠ 0) :
    ∃ w : B, w ≠ 0 ∧ B.representation g₀ w = c • w := by
  obtain ⟨K, hK⟩ := B.isSmooth x
  let W := fixedVectors B.representation K.toSubgroup
  have : FiniteDimensional ℂ W := hB.2 K
  have hmem : ∀ w, w ∈ W ↔ ∀ k : K.toSubgroup, B.representation k w = w := fun w =>
    Representation.mem_invariants _ w
  have hL : ∀ w ∈ W, B.representation g₀ w ∈ W := by
    intro w hw
    rw [hmem] at hw ⊢
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← hg₀, map_mul, Module.End.mul_apply, hw k]
  have hf : ∀ w ∈ W, (SmoothRep.hom f).toLinearMap (B.representation g₀ w - c • w) = 0 := by
    intro w _
    rw [map_sub, map_smul]
    change SmoothRep.hom f (B.representation g₀ w) - c • SmoothRep.hom f w = 0
    rw [Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g₀ w, hD,
      sub_self]
  obtain ⟨w, _, hw0, hw⟩ := exists_eigenvector_of_finiteDimensional W (B.representation g₀) hL
    (SmoothRep.hom f).toLinearMap c hf hK hx
  exact ⟨w, hw0, hw⟩

/-- If a nonzero smooth subquotient of an admissible representation `A` has a central
element `g₀` acting by the scalar `c`, then `c` is an eigenvalue of `g₀` on `A`. -/
theorem exists_eigenvector_of_isSubquotient {A D : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.IsAdmissible) {g₀ : G} (hg₀ : ∀ g, g₀ * g = g * g₀) {c : ℂ}
    (hD : ∀ v : D, D.representation g₀ v = c • v) (hsub : SmoothRep.IsSubquotient D A)
    [Nontrivial D] :
    ∃ w : A, w ≠ 0 ∧ A.representation g₀ w = c • w := by
  obtain ⟨S, S', ⟨e⟩⟩ := hsub
  have hB : (SmoothRep.subrepresentation A S).IsAdmissible :=
    isAdmissible_of_injective (SmoothRep.hom (SmoothRep.subtype A S))
      (SmoothRep.subtype_injective A S) hA
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  obtain ⟨x, hx⟩ := SmoothRep.mkQ_surjective _ S' (SmoothRep.hom e.hom d)
  have hfx : SmoothRep.hom (SmoothRep.mkQ _ S' ≫ e.inv) x ≠ 0 := by
    change SmoothRep.hom e.inv (SmoothRep.hom (SmoothRep.mkQ _ S') x) ≠ 0
    rw [hx]
    change SmoothRep.hom (e.hom ≫ e.inv) d ≠ 0
    rw [e.hom_inv_id]
    exact hd
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_of_hom hB hg₀ hD _ hfx
  refine ⟨SmoothRep.hom (SmoothRep.subtype A S) w, fun h => hw0 ?_, ?_⟩
  · exact SmoothRep.subtype_injective A S (h.trans (map_zero _).symm)
  · rw [← Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom (SmoothRep.subtype A S)),
      hw, map_smul]

end Admissible

/-! ## Shifted derivatives -/

section Derivative

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every shifted derivative `ν^(1/2) π^(k)` of an irreducible smooth representation
of `GL_N(F)` is admissible: it has finite length. -/
theorem bernsteinShiftedDerivative_isAdmissible
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (k : ℕ) (hk : k ≤ N) :
    letI := T.topology
    (bernsteinShiftedDerivative T ψ π k hk).IsAdmissible := by
  let := T.topology
  refine (SmoothRep.isAdmissible_twist_iff _ (T.isOpen_ker_determinantPowerCharacter _ _) _).mpr ?_
  exact glFiniteLengthAdmissibility F T _ _
    (Derivative.generalLinearDerivativeFiniteLength F T ψ N k hk π
      (SmoothRep.hasFiniteLength_of_isIrreducible hirr))

variable {F}

/-- The determinant twists of `ν^(1/2)` and of the normalized `Ψ⁻` cancel: a matrix
acts on a radical-coinvariant class through its Levi image. -/
theorem segmentFactor_psiMinus_action {n : ℕ}
    (τ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
    (g : GeneralLinear n F.Carrier) (y : τ) :
    letI := T.topology
    (T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)).representation g
        (Derivative.Mirabolic.psiMinusQuotient T n τ y) =
      Derivative.Mirabolic.psiMinusQuotient T n τ (τ.representation (levi g) y) := by
  let := T.topology
  have hc : (T.determinantPowerCharacter n (1 / 2) g : ℂ) *
      (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) = 1 := by
    rw [coe_realPowerCharacter, coe_realPowerCharacter, ← Complex.ofReal_mul,
      ← Real.rpow_add (by exact_mod_cast (pos_iff_ne_zero.mpr (T.determinantNorm n g).ne_zero))]
    norm_num
  change (T.determinantPowerCharacter n (1 / 2) g : ℂ) •
      ((realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
        Derivative.Mirabolic.psiMinusQuotient T n τ (τ.representation (levi g) y)) = _
  rw [smul_smul, hc, one_smul]

/-- The normalized absolute value of the chosen uniformizer is less than one. -/
theorem normalizedAbs_uniformizer_lt_one : T.normalizedAbs T.uniformizer < 1 := by
  rw [T.normalizedAbs_uniformizer, zpow_neg_one]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  exact inv_lt_one_of_one_lt₀ hq

/-- Bernstein 1984, §7.4, reduction step: `ν^(1/2) Ψ⁻ τ` has positive central exponents
when it is admissible and every eigenvalue `c` of the Levi uniformizer scalar on a
nonzero radical-coinvariant class of `τ` has norm less than one. -/
theorem bernsteinPositiveCentralExponents_segmentFactor_psiMinus {n : ℕ}
    (τ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
    (hadm : letI := T.topology
      (T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)).IsAdmissible)
    (hτ : letI := T.topology
      ∀ (y : τ) (c : ℂ),
      y ∉ Jacquet.Localization.relations τ.representation (radical n F.Carrier) 1 →
      τ.representation (levi (scalar (LocalFactor.PadicAbelian.uniformizerUnit T))) y - c • y ∈
        Jacquet.Localization.relations τ.representation (radical n F.Carrier) 1 →
      ‖c‖ < 1) :
    letI := T.topology
    BernsteinPositiveCentralExponents T
      (T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)) := by
  let := T.topology
  rintro e ⟨D, hDirr, hDsub, ω, hω, hnorm⟩
  have := hDirr
  have : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      D.representation.asModule
  let ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
  have hcentral : ∀ g : GeneralLinear n F.Carrier, scalar ϖ * g = g * scalar ϖ := fun g =>
    (Subgroup.mem_center_iff.mp (scalarToCenter ϖ).2 g).symm
  obtain ⟨w, hw0, hw⟩ :=
    exists_eigenvector_of_isSubquotient hadm hcentral (fun v => hω ϖ v) hDsub
  obtain ⟨y, rfl⟩ := Derivative.Mirabolic.psiMinusQuotient_surjective T n τ w
  rw [segmentFactor_psiMinus_action] at hw
  have hw' : Derivative.Mirabolic.psiMinusQuotient T n τ (τ.representation (levi (scalar ϖ)) y) =
      (ω ϖ : ℂ) • Derivative.Mirabolic.psiMinusQuotient T n τ y := hw
  have hy : y ∉ Jacquet.Localization.relations τ.representation (radical n F.Carrier) 1 :=
    fun h => hw0 ((Jacquet.Localization.mk_eq_zero _ _ _ y).mpr h)
  have hrel : τ.representation (levi (scalar ϖ)) y - (ω ϖ : ℂ) • y ∈
      Jacquet.Localization.relations τ.representation (radical n F.Carrier) 1 := by
    rw [← Jacquet.Localization.mk_eq_zero]
    change Derivative.Mirabolic.psiMinusQuotient T n τ _ = 0
    rw [map_sub, map_smul, hw', sub_self]
  have hc := hτ y _ hy hrel
  rw [hnorm ϖ, LocalFactor.PadicAbelian.uniformizerUnit_coe] at hc
  obtain ⟨hpos, -⟩ := UnitaryWeylRigidity.normalizedAbs_uniformizer_pos_ne_one T
  rcases (Real.rpow_lt_one_iff_of_pos hpos).mp hc with ⟨h1, -⟩ | ⟨-, he⟩
  · exact absurd h1 (not_lt.mpr (normalizedAbs_uniformizer_lt_one T).le)
  · exact he

end Derivative

end Langlands.Classification
