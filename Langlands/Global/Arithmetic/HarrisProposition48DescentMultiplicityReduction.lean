import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Global.Arithmetic.HarrisProposition48MultiplicityStatement
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof
import Langlands.Galois.PureWeightParity

/-!
# The descent step of Proposition 4.8 from Theorem 1.2 with multiplicity

Henniart (2001), §§5.9–5.12: the selection of the correct cyclic descent of a stable
Mackey constituent, from Harris's Theorem 1.2 with multiplicity
(`Harris1998Theorem12CuspidalMultiplicityStatement`), in place of the published
descent selection from Theorem 1.2 (`Proposition48SingletonDescentSelectionTCStatement`).
The argument is reduced to named inputs, which are stated here: the twisting character of
§5.12, the twist of a descent to the hypotheses of the theorem (Harris 1998, proof of
Lemma 1.6; Henniart 2001, §§5.9 and 5.11), the reading of the `ℓ`-adic representation
restricted to the cyclic extension as `a` twists of the induced representation (§5.10),
the equality of the `a` twists by the pole of order `a²` of the L-function of the pair
(§5.10), and the untwisting of the selected descent (§5.10, end). The reduction itself is
proved.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure AdelicFunctoriality
open InfinitePlace.Completion

section Helpers

/-- Uniqueness of `a`-th roots among polynomials with constant term `1`: two complex
polynomials with constant term `1` whose `a`-th powers agree for some `a > 0` are equal. -/
theorem eq_of_pow_eq_pow_of_eval_zero {P Q : Polynomial ℂ} {a : ℕ} (ha : 0 < a)
    (hP : P.eval 0 = 1) (hQ : Q.eval 0 = 1) (h : P ^ a = Q ^ a) : P = Q := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  have hroots : P.roots = Q.roots := by
    have h1 := congrArg Polynomial.roots h
    rw [Polynomial.roots_pow, Polynomial.roots_pow] at h1
    exact (nsmul_right_injective (Nat.pos_iff_ne_zero.mp ha)) h1
  have hPs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hQs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := Q))
  rw [hroots] at hPs
  set M := (Q.roots.map fun r => Polynomial.X - Polynomial.C r).prod with hM
  have hP' : P.leadingCoeff * M.eval 0 = 1 := by
    have h0 := congrArg (Polynomial.eval 0) hPs
    rw [Polynomial.eval_mul, Polynomial.eval_C] at h0
    rw [h0, hP]
  have hQ' : Q.leadingCoeff * M.eval 0 = 1 := by
    have h0 := congrArg (Polynomial.eval 0) hQs
    rw [Polynomial.eval_mul, Polynomial.eval_C] at h0
    rw [h0, hQ]
  have hM0 : M.eval 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hP'
    exact zero_ne_one hP'
  have hlc : P.leadingCoeff = Q.leadingCoeff :=
    mul_right_cancel₀ hM0 (hP'.trans hQ'.symm)
  calc P = Polynomial.C P.leadingCoeff * M := hPs.symm
    _ = Polynomial.C Q.leadingCoeff * M := by rw [hlc]
    _ = Q := hQs

variable (E : Type*) [Field E] [NumberField E]

/-- The maximal totally real subfield as an intermediate field over `ℚ`. -/
def realIntermediateField : IntermediateField ℚ E :=
  (maximalRealSubfield E).toIntermediateField fun x => by
    rw [eq_ratCast]
    exact SubfieldClass.ratCast_mem _ x

instance : IsTotallyReal (realIntermediateField E) :=
  inferInstanceAs (IsTotallyReal (maximalRealSubfield E))

variable {E}

theorem HasEvenRealDegree.even_finrank_realIntermediateField (h : HasEvenRealDegree E) :
    Even (Module.finrank ℚ (realIntermediateField E)) := by
  have e : realIntermediateField E ≃+* maximalRealSubfield E := RingEquiv.refl _
  rw [(e.toRatAlgEquiv).toLinearEquiv.finrank_eq]
  exact h

/-- In a CM field, the maximal totally real subfield and any totally complex subfield
generate the field. -/
theorem realIntermediateField_sup_eq_top [IsCMField E] (K₀ : IntermediateField ℚ E)
    [IsTotallyComplex K₀] : realIntermediateField E ⊔ K₀ = ⊤ := by
  have hfix (y : E) : IsCMField.complexConj E y = y ↔ y ∈ maximalRealSubfield E :=
    IsCMField.complexConj_eq_self_iff E y
  have hcc (y : E) : IsCMField.complexConj E (IsCMField.complexConj E y) = y :=
    IsCMField.complexConj_apply_apply E y
  -- some element of `K₀` is not fixed by complex conjugation
  obtain ⟨z, hzK, hz⟩ : ∃ z ∈ K₀, IsCMField.complexConj E z ≠ z := by
    by_contra hall
    push Not at hall
    have hle : K₀.toSubfield ≤ maximalRealSubfield E := fun z hz => (hfix z).mp (hall z hz)
    have : IsTotallyReal K₀.toSubfield := isTotallyReal_iff_le_maximalRealSubfield.mpr hle
    have hreal : IsTotallyReal K₀ := this
    obtain ⟨w⟩ : Nonempty (InfinitePlace K₀) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
      (IsTotallyReal.isReal w)
  let c := IsCMField.complexConj E
  have hcc' (y : E) : c (c y) = y := hcc y
  let b : E := (z - c z) / 2
  have hcb : c b = -b := by
    change c ((z - c z) / 2) = -((z - c z) / 2)
    simp only [map_div₀, map_sub, map_ofNat, hcc']
    ring
  have hb0 : b ≠ 0 := by
    intro h0
    apply hz
    have h1 : z - c z = 0 := by
      have h2 : (z - c z) / 2 = 0 := h0
      simpa using h2
    exact (sub_eq_zero.mp h1).symm
  have hreal (y : E) (hy : c y = y) : y ∈ realIntermediateField E ⊔ K₀ :=
    le_sup_left (a := realIntermediateField E) ((hfix y).mp hy)
  have hbM : b ∈ realIntermediateField E ⊔ K₀ := by
    have hz' : z ∈ realIntermediateField E ⊔ K₀ := le_sup_right (a := realIntermediateField E) hzK
    have ha : (z + c z) / 2 ∈ realIntermediateField E ⊔ K₀ := hreal _ (by
      simp only [map_div₀, map_add, map_ofNat, hcc']
      ring)
    have hb' : b = z - (z + c z) / 2 := by
      change (z - c z) / 2 = z - (z + c z) / 2
      ring
    rw [hb']
    exact sub_mem hz' ha
  rw [eq_top_iff]
  intro y _
  have hy : y = (y + c y) / 2 + ((y - c y) / (2 * b)) * b := by
    field_simp
    ring
  rw [hy]
  refine add_mem (hreal _ ?_) (mul_mem (hreal _ ?_) hbM)
  · simp only [map_div₀, map_add, map_ofNat, hcc']
    ring
  · simp only [map_div₀, map_sub, map_mul, map_ofNat, hcc', hcb]
    field_simp
    ring

end Helpers

section Inputs

open Langlands.Automorphic.Unramified.WeakInduction

/-- Henniart 2001, §5.12: a Hecke character `φ` of a CM field with `φ ∘ c = φ⁻¹` whose
component at every infinite place `v`, read through the embedding of the completion, is
`z ↦ (z / |z|)^{±1}`. -/
def IsHenniartTwistingCharacter {F : Type*} [Field F] [NumberField F] [IsCMField F]
    (φ : HeckeCharacter F) : Prop :=
  IsConjugateInverse φ ∧
    ∀ v : InfinitePlace F, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : (InfiniteCompletion F v)ˣ,
      (φ.infiniteComponent v x : ℂ) =
        (extensionEmbedding v (x : InfiniteCompletion F v) /
          ((‖extensionEmbedding v (x : InfiniteCompletion F v)‖ : ℝ) : ℂ)) ^ ε

/-- Henniart 2001, §5.12, named input: every CM field has a twisting character
(`IsHenniartTwistingCharacter`). Henniart proves it from the triviality of the quadratic
character of `F/F^c` on the relevant infinite ideles and the extension of characters of a
closed subgroup of a locally compact abelian group. The statement is not proved here. -/
def HenniartTwistingCharacterStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsCMField F],
    ∃ φ : HeckeCharacter F, IsHenniartTwistingCharacter φ

/-- Named input, Harris 1998, proof of Lemma 1.6, and Henniart 2001, §§5.9 and 5.11: given a
twisting character `φ` of `E` (§5.12), a cyclic descent `S₀` over `E` of a stable Mackey
constituent `S`, all of whose descents have regular highest weight and a supercuspidal
component at the auxiliary place, has a determinant twist `T₀ = S₀ ⊗ (ψ ∘ det)` that is
conjugate self-dual, of regular highest weight and supercuspidal at the auxiliary place.
In Henniart's argument `ψ` is the inverse of the finite-order character `μ` of Harris's
Lemma 1.6 (§5.9), multiplied by `φ` composed with the norm when the descent is not
algebraic (§5.11, even rank in Henniart's normalization). Here the descents are assumed
to have regular highest weight, and the finite-order twist suffices. The statement is not
proved here. -/
def Proposition48DescentTheorem12TwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r), 1 ≤ r →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      S.isoClass.IsConjugateSelfDual →
      Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
      (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
      (∀ c : CuspidalOperatorRealization.IsoClass Q.E r,
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV} S.isoClass c →
        c.HasRegularHighestWeight ∧ c.HasSupercuspidalComponent.{0, uV} Q.Ps.v) →
      ∀ φ : HeckeCharacter Q.E, IsHenniartTwistingCharacter φ →
      ∀ S₀ : CuspidalOperatorRealization Q.E r,
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
          S.isoClass S₀.isoClass →
        ∃ (ψ : HeckeCharacter Q.E) (T₀ : CuspidalOperatorRealization Q.E r),
          OperatorRealization.IsDeterminantMultiple ψ S₀.realization T₀.realization ∧
          T₀.isoClass.IsConjugateSelfDual ∧ T₀.isoClass.HasRegularHighestWeight ∧
          T₀.isoClass.HasSupercuspidalComponent.{0, uV} Q.Ps.v

/-- Named input, Henniart 2001, §5.10, first part (the restriction to the `a` characters).
Let `η` be a character of `E` with norm kernel `D`, `S₀` a cyclic descent of the stable
Mackey constituent `S`, and `T₀ = S₀ ⊗ (ψ ∘ det)` conjugate self-dual of regular highest
weight. Suppose that for every prime `ℓ` and `ℂ ≅ ℚ̄_ℓ`, `T₀` has a semisimple `ℓ`-adic
representation with `L(R_v, s) = L(T₀_v, s + (n − 1)/2)^a` (the conclusion of
`Harris1998Theorem12CuspidalMultiplicityStatement`). Then there are `a ≥ 1` and exponents
`i₁, …, i_a < [D : E]` such that, at almost every place, the Euler polynomial of `T₀` to the
power `a` is the product over `k` of the Euler polynomials weakly induced from
`ξ · ((ψ η^{i_k}) ∘ N_{E'/E})`. Henniart's argument restricts the representation to
`Gal(Ē/D)`, compares it with `a` copies of the induced representation by Chebotarev's density
theorem, and reads the characters `η^{i_k}` off Frobenius reciprocity. The statement is not
proved here. -/
def Proposition48DescentRestrictionCharactersStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r), 1 ≤ r →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      S.isoClass.IsConjugateSelfDual →
      Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
      (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
      ∀ η : HeckeCharacter Q.E, η.HasNormKernel D →
      ∀ (S₀ T₀ : CuspidalOperatorRealization Q.E r) (ψ : HeckeCharacter Q.E),
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
          S.isoClass S₀.isoClass →
        OperatorRealization.IsDeterminantMultiple ψ S₀.realization T₀.realization →
        T₀.isoClass.IsConjugateSelfDual → T₀.isoClass.HasRegularHighestWeight →
        (∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιℓ : ℂ ≃+* PadicAlgCl ℓ),
          ∃ (a : ℕ) (R : Objects.{0, 0, uV} Q.E (PadicAlgCl ℓ)),
            0 < a ∧ R.val.rank = a * (r + 1) ∧
            Representation.IsSemisimpleRepresentation R.val.representation ∧
            T₀.isoClass.IsHenniartAssociatedAt.{0, 0, uV, uV} ιℓ.toRingHom R a) →
        ∃ (a : ℕ) (i : Fin a → ℕ) (s : SpectralSystem (FinitePlace Q.E) (r + 1))
          (t : Fin a → SpectralSystem (FinitePlace Q.E) (r + 1)),
          0 < a ∧ (∀ k, i k < Module.finrank Q.E D) ∧
          CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{0, uV} T₀.isoClass s ∧
          (∀ k, (t k).IsWeakInductionOf
            (Q.ξ * HeckeCharacter.normComp (L := Q.E') (ψ * η ^ i k))) ∧
          ∀ᶠ v in Filter.cofinite, ∀ (hs : v ∉ s.exceptional)
            (ht : ∀ k, v ∉ (t k).exceptional),
            s.eulerPolynomial v hs ^ a = ∏ k, (t k).eulerPolynomial v (ht k)

/-- Named input, Henniart 2001, §5.10, second part (the pole of order `a²`). In the
situation of `Proposition48DescentRestrictionCharactersStatement`, if the Euler polynomial
of `T₀` to the power `a` is at almost every place the product of the Euler polynomials
weakly induced from `ξ · ((ψ η^{i_k}) ∘ N)`, `i_k < [D : E]`, then all exponents `i_k` are
equal. The partial L-function of the pair `(T₀, T₀^∨)` has a pole of order one at `s = 1`,
so its `a²`-th power has a pole of order `a²`. The product side has a pole of order the
number of pairs `(k, l)` with `i_k = i_l`, since the induced representations are irreducible
on restriction to `D` (one Mackey class) and pairwise distinct for distinct exponents.
The statement is not proved here. -/
def Proposition48DescentPairPoleStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r), 1 ≤ r →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      S.isoClass.IsConjugateSelfDual →
      Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
      (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
      ∀ η : HeckeCharacter Q.E, η.HasNormKernel D →
      ∀ (S₀ T₀ : CuspidalOperatorRealization Q.E r) (ψ : HeckeCharacter Q.E),
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
          S.isoClass S₀.isoClass →
        OperatorRealization.IsDeterminantMultiple ψ S₀.realization T₀.realization →
        T₀.isoClass.IsConjugateSelfDual →
        ∀ (a : ℕ) (i : Fin a → ℕ) (s : SpectralSystem (FinitePlace Q.E) (r + 1))
          (t : Fin a → SpectralSystem (FinitePlace Q.E) (r + 1)),
          (∀ k, i k < Module.finrank Q.E D) →
          CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{0, uV} T₀.isoClass s →
          (∀ k, (t k).IsWeakInductionOf
            (Q.ξ * HeckeCharacter.normComp (L := Q.E') (ψ * η ^ i k))) →
          (∀ᶠ v in Filter.cofinite, ∀ (hs : v ∉ s.exceptional)
            (ht : ∀ k, v ∉ (t k).exceptional),
            s.eulerPolynomial v hs ^ a = ∏ k, (t k).eulerPolynomial v (ht k)) →
          ∀ k l, i k = i l

/-- Named input, Henniart 2001, §5.10, end: if the twist `T₀ = S₀ ⊗ (ψ ∘ det)` of a cyclic
descent `S₀` of `S` is a weak automorphic induction of `ξ · ((ψ η^i) ∘ N_{E'/E})`, then the
twist of `S₀` by `η^{−i}` is a cyclic descent of `S` that is a weak automorphic induction of
`ξ`. The twist by `η^{−i}` is again a descent because `η` is trivial on norms from `D`
(Arthur–Clozel, Lemma III.6.3), and the Euler polynomials of the twists are those of `S₀`
with the Satake parameters multiplied by the values of the characters. The statement is
not proved here. -/
def Proposition48DescentUntwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsSpaced → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
    ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r), 1 ≤ r →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      S.isoClass.IsConjugateSelfDual →
      Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
      (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
      ∀ η : HeckeCharacter Q.E, η.HasNormKernel D →
      ∀ (S₀ T₀ : CuspidalOperatorRealization Q.E r) (ψ : HeckeCharacter Q.E) (i : ℕ),
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
          S.isoClass S₀.isoClass →
        OperatorRealization.IsDeterminantMultiple ψ S₀.realization T₀.realization →
        T₀.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV}
          (Q.ξ * HeckeCharacter.normComp (L := Q.E') (ψ * η ^ i)) →
        ∃ c : CuspidalOperatorRealization.IsoClass Q.E r,
          CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV} S.isoClass c ∧
          c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ

end Inputs

/-- The descent step of Proposition 4.8 from Theorem 1.2 with multiplicity and the named
inputs of Henniart 2001, §§5.10–5.12. -/
def Proposition48DescentMultiplicityReductionStatement : Prop :=
  HenniartTwistingCharacterStatement →
  Proposition48DescentTheorem12TwistStatement.{uF, uV} →
  Proposition48DescentRestrictionCharactersStatement.{uF, uV} →
  Proposition48DescentPairPoleStatement.{uF, uV} →
  Proposition48DescentUntwistStatement.{uF, uV} →
  Proposition48MultiplicitySingletonDescentSelectionTCStatement.{uF, uV}

/-- Proof of `Proposition48DescentMultiplicityReductionStatement`, following Henniart 2001,
§§5.9–5.12: descend `S` (published cyclic stable descent), twist the descent to the
hypotheses of the theorem, apply the theorem with multiplicity, read off the `a` twists,
make them equal by the pole of the pair, take the `a`-th root of the Euler polynomials,
and untwist. -/
theorem proposition48DescentMultiplicityReduction :
    Proposition48DescentMultiplicityReductionStatement.{uF, uV} := by
  intro hφ hA hB hC hD hThm _hRig hDesc Q D hvalid hspaced hprime hsingle
  let _ : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  intro _ r S hr hunit hcsd hmack hstable hprops
  have : IsGalois Q.E D := hprime.1
  have : IsCyclic (D ≃ₐ[Q.E] D) := hprime.2.1
  -- A character of `E` with norm kernel `D` and a generator of `Gal(D/E)`.
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{0, 0} Q.E D).1
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := D ≃ₐ[Q.E] D)
  -- A cyclic descent of `S` (Arthur–Clozel, Lemma III.6.3).
  obtain ⟨c₀, hc₀, -⟩ := hDesc Q.E D σ hσ η hη r S hunit (hstable σ)
  obtain ⟨S₀, rfl⟩ := Quotient.exists_rep c₀
  -- The twist to the hypotheses of Theorem 1.2.
  obtain ⟨φ, hφφ⟩ := hφ Q.E
  obtain ⟨ψ, T₀, hdet, hcsd₀, hreg₀, hsc₀⟩ :=
    hA Q D hvalid hspaced hprime hsingle r S hr hunit hcsd hmack hstable hprops φ hφφ S₀ hc₀
  -- Theorem 1.2 with multiplicity for the twist.
  have hK₀ := hvalid.2.1
  have : IsTotallyComplex Q.K₀ := hK₀.2.1
  have hsplit : Harris.IsSplitImaginaryQuadratic (residueCharacteristic Q.Ps.v) Q.K₀ := by
    rw [residueCharacteristic_eq_of_natCast_mem Q.prime.out hvalid.2.2.2.2.1]
    exact hK₀
  have hthm : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιℓ : ℂ ≃+* PadicAlgCl ℓ),
      ∃ (a : ℕ) (R : Objects.{0, 0, uV} Q.E (PadicAlgCl ℓ)),
        0 < a ∧ R.val.rank = a * (r + 1) ∧
        Representation.IsSemisimpleRepresentation R.val.representation ∧
        T₀.isoClass.IsHenniartAssociatedAt.{0, 0, uV, uV} ιℓ.toRingHom R a := fun ℓ _ ιℓ =>
    hThm Q.E (realIntermediateField Q.E) Q.K₀ inferInstance hK₀.1 hK₀.2.1
      (realIntermediateField_sup_eq_top Q.K₀)
      hspaced.1.even_finrank_realIntermediateField r hr T₀.isoClass Q.Ps.v hreg₀ hcsd₀ hsc₀
      hsplit ℓ ιℓ
  -- Restriction to the `a` characters, and their equality by the pole of order `a²`.
  obtain ⟨a, i, s, t, ha, hi, hs, ht, hid⟩ :=
    hB Q D hvalid hspaced hprime hsingle r S hr hunit hcsd hmack hstable η hη S₀ T₀ ψ hc₀ hdet
      hcsd₀ hreg₀ hthm
  have hall := hC Q D hvalid hspaced hprime hsingle r S hr hunit hcsd hmack hstable η hη S₀ T₀ ψ
    hc₀ hdet hcsd₀ a i s t hi hs ht hid
  let k₀ : Fin a := ⟨0, ha⟩
  -- The `a`-th root: `T₀` is a weak automorphic induction of `ξ · ((ψ η^{i₀}) ∘ N)`.
  have hti : ∀ k, (t k).IsWeakInductionOf
      (Q.ξ * HeckeCharacter.normComp (L := Q.E') (ψ * η ^ i k₀)) := fun k => by
    rw [← hall k k₀]
    exact ht k
  have hsWI : s.IsWeakInductionOf (Q.ξ * HeckeCharacter.normComp (L := Q.E') (ψ * η ^ i k₀)) := by
    refine ⟨(hti k₀).1, ?_⟩
    filter_upwards [hid, Filter.eventually_all.mpr fun k => (hti k).2,
      Filter.eventually_all.mpr fun k => (t k).exceptional.eventually_cofinite_notMem]
      with v hv1 hv2 hv3
    intro hvs
    refine ⟨(hv2 k₀ (hv3 k₀)).1, fun ϖ hϖ => ?_⟩
    have hk : ∀ k, (t k).eulerPolynomial v (hv3 k) = (t k₀).eulerPolynomial v (hv3 k₀) := by
      intro k
      rw [(hv2 k (hv3 k)).2 ϖ hϖ, (hv2 k₀ (hv3 k₀)).2 ϖ hϖ]
    have hpow : s.eulerPolynomial v hvs ^ a = (t k₀).eulerPolynomial v (hv3 k₀) ^ a := by
      rw [hv1 hvs hv3, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [eq_of_pow_eq_pow_of_eval_zero ha (s.eulerPolynomial_eval_zero v hvs)
      ((t k₀).eulerPolynomial_eval_zero v (hv3 k₀)) hpow]
    exact (hv2 k₀ (hv3 k₀)).2 ϖ hϖ
  -- Untwisting the selected descent.
  exact hD Q D hvalid hspaced hprime hsingle r S hr hunit hcsd hmack hstable η hη S₀ T₀ ψ (i k₀)
    hc₀ hdet ⟨s, hs, hsWI⟩

end Langlands.Global.Harris
