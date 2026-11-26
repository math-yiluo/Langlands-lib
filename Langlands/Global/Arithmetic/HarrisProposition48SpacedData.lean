import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.Arithmetic.HarrisDatumArchimedean
import Langlands.Global.Arithmetic.CMGaloisModel
import Langlands.Global.Arithmetic.QuadraticRootSupport
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters

/-!
# Even real degree and weights at distance at least two in Proposition 4.8

Two clauses added to the datum of Harris (1998), Proposition 4.8, and to the problems
of its recursion: the maximal totally real subfield of the base field has even degree
over `ℚ`, and the inducing Hecke character has weights at distance at least `2` above
each archimedean place of the base field. They restrict the construction to the range
in which the theorem of Clozel and Kottwitz in the form with multiplicity of Henniart
2001, §5.5, is applied with two added hypotheses: even real degree (the real quadratic
field of Henniart's §5.1; the one-place range of Clozel 1991, Théorème 5.7) and regular
highest weight (Kottwitz 1992, remark on printed p. 658). The module proves elementary
facts about the clauses and their preservation by the parity correction of the
recursion.
-/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField InfinitePlace.Completion AdelicFunctoriality IntermediateField
open scoped NumberField.LiesOver

section EvenDegree

variable (E : Type*) [Field E] [NumberField E]

/-- The maximal totally real subfield of `E` has even degree over `ℚ`. For a CM field
`E = E₀ K₀` with `K₀` imaginary quadratic and `E₀` totally real, `E₀` is the maximal
totally real subfield, so this is the condition `[E₀ : ℚ]` even, the range in which
Clozel (1991), Théorème 5.7, needs only one split place. -/
def HasEvenRealDegree : Prop :=
  Even (Module.finrank ℚ (maximalRealSubfield E))

variable {E}

/-- For a CM field, `[E : ℚ] = 2 [E⁺ : ℚ]`. -/
theorem finrank_eq_two_mul_finrank_maximalRealSubfield [IsCMField E] :
    Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
  rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]

/-- Even real degree is divisibility of `[E : ℚ]` by `4`. -/
theorem hasEvenRealDegree_iff [IsCMField E] :
    HasEvenRealDegree E ↔ 4 ∣ Module.finrank ℚ E := by
  rw [HasEvenRealDegree, finrank_eq_two_mul_finrank_maximalRealSubfield (E := E),
    even_iff_two_dvd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

/-- Even real degree passes to every CM extension. -/
theorem HasEvenRealDegree.of_algebra {D : Type*} [Field D] [NumberField D] [IsCMField E]
    [IsCMField D] [Algebra E D] (h : HasEvenRealDegree E) : HasEvenRealDegree D := by
  rw [hasEvenRealDegree_iff] at h ⊢
  rw [← Module.finrank_mul_finrank ℚ E D]
  exact Dvd.dvd.mul_right h _

/-- Even real degree is invariant under ring isomorphisms of number fields. -/
theorem HasEvenRealDegree.of_ringEquiv {D : Type*} [Field D] [NumberField D] [IsCMField E]
    [IsCMField D] (e : E ≃+* D) (h : HasEvenRealDegree E) : HasEvenRealDegree D := by
  rw [hasEvenRealDegree_iff] at h ⊢
  rwa [← (e.toRatAlgEquiv).toLinearEquiv.finrank_eq]

/-- A CM field containing a square root of a positive rational number that is not a
square has even real degree: the real quadratic field it generates lies in the maximal
totally real subfield. -/
theorem hasEvenRealDegree_of_sq_pos {d : ℚ} (hd : 0 < d) (hns : ¬ IsSquare d) {x : E}
    (hx : x ^ 2 = algebraMap ℚ E d) : HasEvenRealDegree E := by
  have hmem : x ∈ maximalRealSubfield E := CMRealization.mem_maximalRealSubfield_of_sq_pos hd hx
  let y : maximalRealSubfield E := ⟨x, hmem⟩
  have hy : y ^ 2 = algebraMap ℚ (maximalRealSubfield E) d := by
    apply Subtype.ext
    simpa using hx
  have h2 : Module.finrank ℚ ℚ⟮y⟯ = 2 := squareRoot_finrank hns hy
  rw [HasEvenRealDegree, ← Module.finrank_mul_finrank ℚ ℚ⟮y⟯ (maximalRealSubfield E), h2]
  exact even_two_mul _

end EvenDegree

section Spacing

variable (E : Type*) {E' : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E']

/-- The unitary character `z ↦ z / z̄` of `E_τˣ`, read through the embedding
`extensionEmbedding τ` of the completion into `ℂ`. -/
def rotation (τ : InfinitePlace E) (x : (InfiniteCompletion E τ)ˣ) : ℂ :=
  extensionEmbedding τ (x : InfiniteCompletion E τ) /
    star (extensionEmbedding τ (x : InfiniteCompletion E τ))

/-- Weights at distance at least two above every archimedean place of `E`. For every
place `τ` of `E`, distinct places `w, w'` of `E'` above it and `k ∈ {-1, 0, 1}`, the
archimedean components of `χ` at `w` and `w'`, read on `E_τˣ` through the completion
maps, are not related by the factor `rotation E τ ^ k`.

At a complex place `τ`, for `χ` algebraic and conjugate inverse with integral infinity
type `t` after the norm twist of Harris (1998), p. 195, the quotient of the two
components is `z ↦ (z / z̄)^{t(σ) - t(σ')}` for the embeddings `σ, σ'` of `E'` at `w, w'`
above the embedding of `τ`. Since `z ↦ z / z̄` maps `ℂˣ` onto the unit circle, the
condition at `τ` then says `|t(σ) - t(σ')| ≥ 2`. At a real place `τ` the rotation is
identically `1`, and the three tests are the single test that the two components
differ on `ℝˣ`. For a totally complex `E` the case `k = 0` alone is the published
`IsRelativelyRegular`. -/
def IsRelativelySpaced (χ : HeckeCharacter E') : Prop :=
  ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ], w ≠ w' →
    ∀ k : ℤ, |k| ≤ 1 → ∃ x : (InfiniteCompletion E τ)ˣ,
      (χ.infiniteComponent w
          (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) : ℂ) ≠
        (χ.infiniteComponent w'
          (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x) : ℂ) *
          rotation E τ x ^ k

variable {E}

/-- Weights at distance at least two are distinct. -/
theorem IsRelativelySpaced.isRelativelyRegular [IsTotallyComplex E] {χ : HeckeCharacter E'}
    (h : IsRelativelySpaced E χ) : IsRelativelyRegular E χ := by
  intro τ w w' _ _ hne
  obtain ⟨x, hx⟩ := h τ w w' hne 0 (by simp)
  refine ⟨x, fun heq => hx ?_⟩
  rw [heq, zpow_zero, mul_one]

end Spacing

section NormTwist

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsTotallyComplex K]

omit [NumberField K] [NumberField L] in
private theorem completion_finrank_one (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] : Module.finrank v.Completion w.Completion = 1 := by
  have hw : w.IsUnramified K := InfinitePlace.isUnramified_iff.mpr (Or.inr (by
    rw [InfinitePlace.LiesOver.comap_eq w v]
    exact IsTotallyComplex.isComplex v))
  exact hw.finrank_eq_one v

omit [NumberField K] [NumberField L] in
private theorem localNorm_completionMap (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (x : v.Completion) :
    InfiniteExtension.localNorm v w (LiesOver.completionMap v w x) = x := by
  rw [InfiniteExtension.localNorm_algebraMap, completion_finrank_one v w, pow_one]

/-- For a totally complex base `K`, the component of `ν ∘ N_{L/K}` at a place `w` above
`v`, read on `K_vˣ` through the completion map, is the component of `ν` at `v`: the local
extension `L_w / K_v` is `ℂ / ℂ`, of degree one, so the local norm is the identity. -/
theorem normComp_infiniteComponent_completionMap (ν : HeckeCharacter K)
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] (x : v.Completionˣ) :
    (HeckeCharacter.normComp (L := L) ν).infiniteComponent w
      (Units.map (LiesOver.completionMap (v := v) (w := w)).toMonoidHom x) =
      ν.infiniteComponent v x := by
  let y := Units.map (LiesOver.completionMap (v := v) (w := w)).toMonoidHom x
  change ν (ideleClassNorm (K := K) (IdeleClassGroup.ofCompletion (𝓞 L) L w y)) =
    ν (IdeleClassGroup.ofCompletion (𝓞 K) K v x)
  rw [ideleClassNorm_ofCompletion v (⟨w, inferInstance⟩ : InfinitePlacesAbove L v) y]
  have hy : InfiniteExtension.localUnitNorm v w y = x :=
    Units.ext (localNorm_completionMap v w x.val)
  rw [hy]

/-- For a totally complex base `K`, a norm twist by a character of the base keeps the
weights at distance at least two: it multiplies the components at all places above `v`
by the same character of `K_vˣ`. -/
theorem IsRelativelySpaced.mul_normComp {ξ : HeckeCharacter L} (h : IsRelativelySpaced K ξ)
    (ν : HeckeCharacter K) : IsRelativelySpaced K (ξ * HeckeCharacter.normComp (L := L) ν) := by
  intro τ w w' _ _ hne k hk
  obtain ⟨x, hx⟩ := h τ w w' hne k hk
  refine ⟨x, fun heq => hx ?_⟩
  simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply, Units.val_mul,
    normComp_infiniteComponent_completionMap] at heq
  have hν : (ν.infiniteComponent τ x : ℂ) ≠ 0 := Units.ne_zero _
  apply mul_right_cancel₀ hν
  rw [heq]
  ring

end NormTwist

section Weights

variable {E E' : Type*} [Field E] [NumberField E] [IsTotallyComplex E]
  [Field E'] [NumberField E'] [IsTotallyComplex E'] [Algebra E E']

omit [NumberField E] in
/-- For totally complex number fields `E ⊆ E'`: a character of anticyclotomic infinity
type `A`, times a character whose components agree at all places above each place of
`E`, has weights at distance at least two when `A` takes values at distance at least two
at the embeddings of `E'` over a common embedding of `E`. The proof uses that `E_τ → ℂ`
is onto to choose a separating element. -/
theorem isRelativelySpaced_of_weights (X Y : HeckeCharacter E') (A : InfinityType E')
    (hX : X.HasPrescribedInfinityComponent (InfinityType.toCharacter A))
    (hA : A.IsAnticyclotomic)
    (hY : ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ]
      (x : (InfiniteCompletion E τ)ˣ),
      Y.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) =
        Y.infiniteComponent w' (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x))
    (hdist : ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ],
      w ≠ w' → 2 ≤ |A (HarrisDatum.lift τ w) - A (HarrisDatum.lift τ w')|) :
    IsRelativelySpaced E (X * Y) := by
  intro τ w w' _ _ hne k hk
  set M : ℤ := A (HarrisDatum.lift τ w) - A (HarrisDatum.lift τ w') - k with hM
  have hM0 : M ≠ 0 := by
    intro h0
    have h2 := hdist τ w w' hne
    have hk' : A (HarrisDatum.lift τ w) - A (HarrisDatum.lift τ w') = k := by omega
    rw [hk'] at h2
    linarith
  set θ : ℝ := Real.pi / (2 * M) with hθ
  set z : ℂ := Complex.exp (θ * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hτ : τ.IsComplex := IsTotallyComplex.isComplex τ
  obtain ⟨x₀, hx₀⟩ := surjective_extensionEmbedding_of_isComplex hτ z
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx₀
    exact hz0 hx₀.symm
  refine ⟨Units.mk0 x₀ hx₀0, fun heq => ?_⟩
  simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply,
    Units.val_mul] at heq
  rw [hY τ w w' (Units.mk0 x₀ hx₀0)] at heq
  have hYne : (Y.infiniteComponent w'
      (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom (Units.mk0 x₀ hx₀0)) : ℂ)
      ≠ 0 := Units.ne_zero _
  have hX' : (X.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ)
      (w := w)).toMonoidHom (Units.mk0 x₀ hx₀0)) : ℂ) =
      (X.infiniteComponent w' (Units.map (LiesOver.completionMap (v := τ)
        (w := w')).toMonoidHom (Units.mk0 x₀ hx₀0)) : ℂ) *
        rotation E τ (Units.mk0 x₀ hx₀0) ^ k := by
    apply mul_right_cancel₀ hYne
    rw [heq]
    ring
  have hrot : rotation E τ (Units.mk0 x₀ hx₀0) = Complex.exp ((2 * (1 : ℤ) * θ : ℝ) * Complex.I) := by
    rw [← HarrisDatum.exp_zpow_mul_star_zpow, zpow_one, zpow_neg, zpow_one]
    simp only [rotation, Units.val_mk0, hx₀, hz, div_eq_mul_inv]
  rw [HarrisDatum.infiniteComponent_completionMap X A hX τ w,
    HarrisDatum.infiniteComponent_completionMap X A hX τ w',
    hA (HarrisDatum.lift τ w), hA (HarrisDatum.lift τ w'), hrot] at hX'
  simp only [Units.val_mk0, hx₀, hz] at hX'
  rw [HarrisDatum.exp_zpow_mul_star_zpow, HarrisDatum.exp_zpow_mul_star_zpow,
    ← Complex.exp_int_mul, ← Complex.exp_add] at hX'
  have hdiff : Complex.exp ((2 * M * θ : ℝ) * Complex.I) = 1 := by
    have hsub : ((2 * M * θ : ℝ) : ℂ) * Complex.I =
        ((2 * (A (HarrisDatum.lift τ w)) * θ : ℝ) : ℂ) * Complex.I -
          ((((2 * (A (HarrisDatum.lift τ w')) * θ : ℝ) : ℂ) * Complex.I) +
            (k : ℂ) * (((2 * (1 : ℤ) * θ : ℝ) : ℂ) * Complex.I)) := by
      rw [hM]
      push_cast
      ring
    rw [hsub, Complex.exp_sub, hX', div_self (Complex.exp_ne_zero _)]
  have hpi : ((2 * M * θ : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I := by
    congr 1
    rw [hθ]
    push_cast
    field_simp
  rw [hpi, Complex.exp_pi_mul_I] at hdiff
  norm_num at hdiff

end Weights

section Datum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {F' : LocalFactor.CommonClosure.Extension F}
  {E E' L : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsCMField E] [IsCMField E']

/-- The datum of Harris (1998), Proposition 4.8 (the published `IsProposition48Datum`),
with the two clauses supplied by Henniart's construction: the base field has even real
degree and the inducing character has weights at distance at least two above every
archimedean place of the base field. -/
def IsProposition48SpacedDatum (e : LocalFactor.CommonClosure.ReciprocityFamily F)
    (χ χs : LocalFactor.CommonClosure.FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E') : Prop :=
  IsProposition48Datum e χ χs K₀ P Ps ξ ∧ HasEvenRealDegree E ∧ IsRelativelySpaced E ξ

end Datum

namespace Proposition48Problem

/-- The two clauses added to the one-place hypotheses: the base field has even real
degree and the inducing character has weights at distance at least two above every
archimedean place of the base field. -/
def IsSpaced (Q : Proposition48Problem.{uF}) : Prop :=
  HasEvenRealDegree Q.E ∧ IsRelativelySpaced Q.E Q.ξ

/-- The parity normalization of the induction keeps both clauses: the base field is
unchanged and the corrected character is a norm twist. -/
theorem IsSpaced.withCorrectedCharacter {Q : Proposition48Problem.{uF}} (h : Q.IsSpaced)
    (ν : HeckeCharacter Q.E) (χ χs : LocalFactor.CommonClosure.FieldCharacter Q.F Q.F') :
    (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsSpaced :=
  ⟨h.1, h.2.mul_normComp ν⟩

end Proposition48Problem

end Langlands.Global.Harris
