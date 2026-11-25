# Harris Proposition 4.8: the auxiliary conjugate pair

Module `Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement`,
namespace `Langlands.Global.Harris`. The module declares `universe u uV`, sets
`autoImplicit false` and opens `NumberField Langlands.Automorphic`. It imports
exactly `Langlands.Automorphic.ConjugateContragredient`,
`Langlands.Automorphic.SupercuspidalComponent`,
`Langlands.Automorphic.AssociatedFactorStatement` and
`Langlands.Global.Arithmetic.HarrisSetup`.

It contains three proposition definitions (`Prop`-valued `def`s) and nothing
else:

| Declaration | Universe parameters |
| --- | --- |
| `ConjugateSelfDualUnitaryCentralCharacterStatement` | `u` |
| `ConjugateSelfDualSupercuspidalConjPlaceStatement` | `u, uV` |
| `SplitPlaceNeConjPlaceStatement` | `u` |

`u` is the universe of the CM field `E`. `uV` is the universe of the carrier
spaces of the local factors of spectral presentations.

These are inputs to the two exact-stabilizer branches (singleton and prime
orbit) of Harris (1998), Proposition 4.8, at the auxiliary conjugate pair.
Nothing is proved here. The proofs are separate tasks.

**Provenance.** All three statements are *derived* consequences of Harris's
setup and of standard facts. None is a quotation. Harris uses them without
stating them separately: conjugate self-duality `π ≅ π^∨ ∘ c` in
Theorem 1.2(ii), and the splitting of `p` in `K₀` in Section 2. Their form
here (an arbitrary CM field `E`, unitary central characters, supercuspidal
components of spectral presentations) is the form needed by the Library's
hypotheses of B5 and restricted B7. See "Sources" below.

No totally complex (TC) form is stated. Every statement assumes
`NumberField.IsCMField E`, and a CM field is totally complex (Mathlib instance
`IsCMField.isTotallyComplex`).

## Common vocabulary

- **CM field and complex conjugation.** `NumberField.IsCMField E` (Mathlib)
  says that `E` is a totally complex quadratic extension of its maximal real
  subfield `E⁺`. `IsCMField.complexConj E : E ≃ₐ[E⁺] E` is its complex
  conjugation `c`. For every complex embedding `φ : E →+* ℂ`, `φ (c x)` is the
  complex conjugate of `φ x` (`IsCMField.complexEmbedding_complexConj`), and
  `c` is an involution (`IsCMField.complexConj_apply_apply`).
- **Finite places.** `FinitePlace E` is the Library abbreviation for
  `IsDedekindDomain.HeightOneSpectrum (𝓞 E)`, the nonzero primes of the ring
  of integers. `v.asIdeal` is the prime ideal of `v`.
- **The conjugate place.** `conjPlace E v` (`HarrisSetup`) is defined as
  `finitePlaceEquiv (IsCMField.complexConj E).toRingEquiv v`. Its prime ideal
  is the preimage of `v.asIdeal` under `c` on `𝓞 E`
  (`finitePlaceEquiv_asIdeal`). Since `c` is an involution, this is the image
  `c(v)`.
- **Compact adele quotient.** `[CompactSpace (AdeleQuotient E)]` says that
  `𝔸_E / E` is compact. This is true for every number field. It is supplied as
  an instance hypothesis, as in the Library's other cuspidal-class statements,
  because the cuspidal vocabulary requires it.
- **Cuspidal realizations.** `CuspidalOperatorRealization E r` is an actual
  irreducible cuspidal realization of `GL_{r+1}(𝔸_E)`: an operator realization
  `S.realization : OperatorRealization E (r + 1)` on a space of automorphic
  forms, with full-operator irreducibility and cuspidality. The index `r`
  means matrix rank `r + 1`. `S.isoClass` is its isomorphism class, of type
  `CuspidalOperatorRealization.IsoClass E r`.

## 1. `ConjugateSelfDualUnitaryCentralCharacterStatement`

```lean
def ConjugateSelfDualUnitaryCentralCharacterStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S : CuspidalOperatorRealization E r),
    S.isoClass.IsConjugateSelfDual →
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S
```

**Hypotheses.** `E` is a CM number field in universe `u` with compact adele
quotient. `S` is an actual irreducible cuspidal realization of `GL_{r+1}`
over `E`, and its class is conjugate self-dual.

`CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual`
(`ConjugateContragredient`) asks that the underlying full-operator class have
a representative `S'` with `OperatorRealization.IsConjugateSelfDual S'`. By
`CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff`, this holds
exactly when `S.realization.IsConjugateSelfDual`, so the condition is on the
actual realization. `OperatorRealization.IsConjugateSelfDual` asks for a
bilinear pairing `B` on the space of the realization such that the following
hold (`IsConjugateContragredientPairing`):

- `B` is invariant under the operators twisted by `c` in the first variable:
  - `B (π(c d) y) (π(d) x) = B y x` for finite adelic `d`;
  - the same for the standard compact subgroup at infinity, with
    `compactConj`;
  - `B (X^c y) x + B y (X x) = 0` for the real Lie algebra.
- Every `B (·) x` is a contragredient functional: smooth for the finite adelic
  group and finite for the standard compact subgroup.
- The map `x ↦ B (·) x` is injective.
- Every contragredient functional is of the form `B (·) x`.

So `x ↦ B (·) x` is an isomorphism `π ≅ π^∨ ∘ c` on the actual realization.
This is Harris's condition `π ≅ π̌ ∘ c` (Theorem 1.2(ii)).

**Conclusion.** `HasUnitaryCentralCharacter S` holds. This predicate is in
namespace `Langlands.ClassFieldTheory.Global.RelativeWeilGroup`, module
`AssociatedFactorStatement`. It says that there is a continuous character
`χ : IdeleClassGroup (𝓞 E) E →ₜ* ℂˣ` of the idele class group with
`‖χ x‖ = 1` for all `x` such that `S.HasCentralCharacter χ`. That is, every
form `f` of the realization satisfies `f(z g) = χ(z) f(g)` for the scalar
idele matrices `z` (`centralCharacterAutomorphicSubrepresentation`). In other
words, `S` has a unitary continuous character of the idele class group as its
central character.

**Mathematical argument.**

1. By Schur's lemma the irreducible cuspidal realization has a central
   character `ω`, a Hecke character of `E`.
2. Conjugate self-duality gives `ω ∘ c = ω⁻¹`, because the central character
   of `π^∨ ∘ c` is `ω⁻¹ ∘ c`. Concretely, the invariance of the pairing `B`
   under central elements gives `ω(c z) ω(z) B y x = B y x`. Here `z` runs over
   the finite scalar ideles, the centre of the standard compact subgroup, and
   the scalar real Lie algebra elements; the last gives the infinitesimal
   form. Since `B ≠ 0`, this yields `ω(c z) ω(z) = 1`.
3. The absolute value `|ω|` is a continuous homomorphism into the positive
   reals. It is therefore trivial on the compact group of norm-one idele
   classes, so `|ω| = ‖·‖^t` for a real `t`.
4. The idelic norm satisfies `‖x ∘ c‖ = ‖x‖`, because `c` permutes the places
   and preserves the normalized absolute values. With `ω ∘ c = ω⁻¹` this gives
   `‖·‖^t = ‖·‖^{-t}`. Since the norm is surjective onto the positive reals,
   `t = -t`, so `t = 0` and `ω` is unitary.

**Library inputs for the proof.**

- Step 1 is proved in the Library:
  `Langlands.Automorphic.OperatorRealization.existsUnique_hasCentralCharacter`
  (module `Langlands.Automorphic.IrreducibleCentralCharacterProof`). For an
  irreducible actual operator realization it gives a unique continuous
  character `ω : IdeleClassGroup (𝓞 E) E →ₜ* ℂˣ` with
  `HasCentralCharacter ω`. Apply it to `S.realization` with the
  irreducibility witness `S.irreducible`. `S.HasCentralCharacter ω` is by
  definition `S.realization.HasCentralCharacter ω`
  (`CuspidalOperatorRealization`).
- Steps 3–4 are proved in the Library for a Hecke character with
  `ω ∘ c = ω⁻¹`:
  `Langlands.Global.HeckeConjugateInverse.isUnitary_of_isConjugateInverse`
  (module `Langlands.Global.HeckeConjugateInverseUnitary`). Its hypothesis is
  `Harris.IsConjugateInverse ω` (`HarrisSetup`): `ω (c x) = (ω x)⁻¹` for the
  complex conjugation `ideleClassComplexConj` of the idele class group. Its
  conclusion `HeckeCharacter.IsUnitary ω` says `‖ω x‖ = 1` for all `x`. The
  type `HeckeCharacter E` is an abbreviation for
  `IdeleClassGroup (𝓞 E) E →ₜ* ℂˣ`, so the character of step 1 can be used
  directly.
- The Library has no lemma deriving `IsConjugateInverse ω` from conjugate
  self-duality (step 2). This step remains the content of the proof. It uses
  the conjugate-dual pairing `B` as described in step 2.

`HasUnitaryCentralCharacter.conjugate` (`CuspidalConjugateRealization`)
transports unitarity to the conjugate realization and may also help.

## 2. `ConjugateSelfDualSupercuspidalConjPlaceStatement`

```lean
def ConjugateSelfDualSupercuspidalConjPlaceStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
    c.IsConjugateSelfDual →
    c.HasSupercuspidalComponent.{u, uV} v →
    c.HasSupercuspidalComponent.{u, uV} (conjPlace E v)
```

**Hypotheses.** `E` is as in Statement 1. `c` is the isomorphism class of an
irreducible cuspidal realization of `GL_{r+1}` over `E`, and `v` is a finite
place of `E`. The class `c` is conjugate self-dual (Statement 1) and has a
supercuspidal component at `v`.

`IsoClass.HasSupercuspidalComponent.{u, uV} c v` (`SupercuspidalComponent`)
says that there are a representative `S` of `c` and an actual spectral
presentation `P : CuspidalSpectralPresentation.{u, uV} S` whose local
component `P.localComponent v` is supercuspidal. The presentation consists of
genuine tensor and spectral data on a nonzero finite slice of `S`, with a
local factor at every finite place whose carrier space lies in `Type uV`.
`P.localComponent v` is the embedded local copy of the factor at `v`.
`LocalRealization.IsSupercuspidal` asks that this local realization be
irreducible and admissible, and that its canonical `p`-adic class lie in the
Library's Jacquet-vanishing supercuspidal class space
`Correspondence.IsSupercuspidalClass (CompletionPadic.padicField v)`. By
`hasSupercuspidalComponent_iff` the witness can be taken at any
representative. The presentation universe `uV` is the same in the hypothesis
and in the conclusion.

**Conclusion.** `c` has a supercuspidal component at the complex-conjugate
place `conjPlace E v`.

**Mathematical argument.** `π ≅ π^∨ ∘ c` gives `π_{c(v)} ≅ (π_v)^∨`,
transported along the completion `c : E_v ≅ E_{c(v)}`. This is an
isomorphism of `p`-adic fields, because `|c x|_{c(v)} = |x|_v`. The
contragredient of an irreducible supercuspidal representation is irreducible
and supercuspidal. Transport along an isomorphism of local fields preserves
supercuspidality. Hence `π_{c(v)}` is supercuspidal.

For the Lean proof, the local component at `conjPlace E v` of a spectral
presentation must be compared with the contragredient of the component at
`v`, transported along `c`. For the contragredient of supercuspidal
representations, see `Langlands/Representation/Classification/SupercuspidalContragredient.lean`
(which reduces the question to
`GeneralLinear.SupercuspidalContragredientStatement`) and
`Langlands/Representation/CuspidalSupport/ContragredientIrreducibilityFromInputsProof.lean`.

## 3. `SplitPlaceNeConjPlaceStatement`

```lean
def SplitPlaceNeConjPlaceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type u) [Field E] [NumberField E] [IsCMField E]
    (K₀ : IntermediateField ℚ E) (v : FinitePlace E),
    IsSplitImaginaryQuadratic p K₀ → (p : 𝓞 E) ∈ v.asIdeal → v ≠ conjPlace E v
```

**Hypotheses.** `p` is a rational prime, `E` is a CM number field in universe
`u`, `K₀` is a subfield of `E`, and `v` is a finite place of `E`. No
automorphic data and no compactness instance are involved.

`IsSplitImaginaryQuadratic p K₀` (`HarrisSetup`) says three things about
`K₀`, viewed as a number field:

- `Module.finrank ℚ K₀ = 2`;
- `K₀` is totally complex;
- there are two distinct finite places `P ≠ Q` of `K₀` with
  `(p : 𝓞 K₀) ∈ P.asIdeal` and `(p : 𝓞 K₀) ∈ Q.asIdeal`.

That is, `K₀` is an imaginary quadratic field with two distinct finite places
containing `p`, so `p` splits in `K₀`. The hypothesis
`(p : 𝓞 E) ∈ v.asIdeal` says that `v` lies above `p`.

**Conclusion.** `v ≠ conjPlace E v`: the place `v` differs from its complex
conjugate.

**Mathematical argument.**

1. Complex conjugation of `E` preserves `K₀` and acts on it as its
   non-trivial automorphism `σ`. For every complex embedding `φ` of `E`,
   `φ(c(K₀)) = conj(φ(K₀)) = φ(K₀)`, because the imaginary quadratic field
   `φ(K₀) ⊂ ℂ` is stable under complex conjugation. Moreover `c` is not the
   identity on `K₀`, since otherwise `K₀ ⊆ E⁺` would be totally real.
2. The two primes `P`, `Q` of `K₀` above the split prime `p` are all the
   primes above `p`. The Galois group `{1, σ}` permutes them transitively, so
   `σ` exchanges them.
3. The prime `v ∩ 𝓞 K₀` contains `p`, so it is `P` or `Q`. The prime
   `conjPlace E v ∩ 𝓞 K₀ = σ(v ∩ 𝓞 K₀)` is the other one. So `v` and
   `conjPlace E v` lie over different primes of `K₀`, and they differ.

**Library inputs for the proof.** The Library proves `v ≠ conjPlace E v` only
for specific places built from Harris data. It does so inside
`Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.lean`, through
`ne_of_neg_place` (`Langlands/Global/Arithmetic/CMPairedPlaceAssembly.lean`),
using explicit `p`-adic embeddings. It does not prove the inequality as a
general statement. The module
`Langlands/Global/Arithmetic/HarrisDatumCharacterRealizationProof.lean` may
help with steps 1 and 3:

- `HarrisDatum.complexConj_algebraMap` and `HarrisDatum.conjPlace_liesOver`
  give the compatibility of complex conjugation with field maps between CM
  fields;
- `HarrisDatum.ne_of_liesOver` passes the inequality of two places up to
  places above them.

## Use in the exact-stabilizer branches

The targets are `Proposition48ExactStabilizerSingletonBranchStatement`,
`Proposition48ExactStabilizerPrimeBranchStatement` and their TC forms (module
`Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerBranchStatement`).
Fix a problem `Q : Proposition48Problem` with
`Q.IsAuxiliaryExactStabilizerValid`. For each child, the branch hypotheses
give an untwisted constituent with two properties
(`R.IsUntwistedSolution`): it is conjugate self-dual, and it has a
supercuspidal component at the child's auxiliary place `R.Ps.v` only. The
global inputs the branches apply on the cyclic step `D/Q.E` need more:

- B5 (`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement`,
  singleton branch);
- restricted B7
  (`Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceStatement`,
  both branches).

These ask for unitary central characters, for supercuspidal components at
both places of the pair `v₀ = Q.Ps.v`, `conjPlace Q.E Q.Ps.v` and at the
unique places of `D` above them, and for `v₀ ≠ conjPlace Q.E v₀`. The three
statements supply exactly these:

- **Statement 3** applied to `Q.p`, `Q.E`, `Q.K₀` and `Q.Ps.v` gives
  `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v`. Its two hypotheses
  `IsSplitImaginaryQuadratic Q.p Q.K₀` and `(Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal`
  are conjuncts of `Q.IsAuxiliaryExactStabilizerValid`. This gives the
  hypothesis `v₀ ≠ Harris.conjPlace F v₀` of restricted B7, with `F = Q.E` and
  `v₀ = Q.Ps.v`.
- **Statement 1** gives `HasUnitaryCentralCharacter` for every conjugate
  self-dual class to which B5 or restricted B7 is applied:
  - the child's constituent (conjugate self-dual by `IsUntwistedSolution`);
  - the selected descent in the singleton branch and the induced class in the
    prime branch, once the branch proof has established their conjugate
    self-duality.

  This gives the hypothesis `HasUnitaryCentralCharacter S` of B5 and the two
  hypotheses `HasUnitaryCentralCharacter S` and
  `HasUnitaryCentralCharacter T` of restricted B7. In the prime branch it
  also gives the hypothesis `HasUnitaryCentralCharacter T` of B4
  (`Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement`)
  for the child's constituent.
- **Statement 2** turns supercuspidality at the first place of a pair into
  supercuspidality at its conjugate, and gives the conjugate-place hypotheses
  of restricted B7:
  - `S.isoClass.HasSupercuspidalComponent (Harris.conjPlace F v₀)`, from the
    component at `v₀ = Q.Ps.v` supplied by B5 (singleton) or B4 (prime);
  - `T.isoClass.HasSupercuspidalComponent wc.1`, from the child's component
    at `R.Ps.v`, applied over the child's CM field. The place `wc` of `D`
    above `conjPlace Q.E Q.Ps.v` is matched with the conjugate of the place
    above `Q.Ps.v` by `conjPlace_liesOver` and the unique-place hypotheses
    `HasUniquePlaceAbove Q.L`.

This is the list of obligations "unitarity of the central characters …;
supercuspidality at the conjugate place `conjPlace Q.E Q.Ps.v` (from conjugate
self-duality); `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v` (from the split imaginary
quadratic field `K₀`)" in the Markdown of the branch statements. The remaining
obligations listed there are not stated here: the unique places of `D`, the
transport of the child to `D`, and the permutation identities.

## Sources

- **Harris 1998** (source `harris-1998-local-langlands`). M. Harris, *The
  local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent.
  Math. 134 (1998), 177–210. Printed page = registered PDF page + 176.
  - The two pairs of conjugate places: printed p.200 (PDF p.24). Harris
    first chooses complex conjugate places `v₁`, `v₂` of `E` dividing `p`, as
    in Section 2. Since the component `Π_{v₁}` need not be supercuspidal, he
    then assumes "a second pair `v*₁` and `v*₂` of complex conjugate places
    of `E` dividing `p`", each divisible by exactly one prime of the Galois
    closure. This second pair is the auxiliary conjugate pair of the title.
  - Proposition 4.8, statement and proof: printed pp.201–203 (PDF pp.25–27).
    The statement on p.201 concludes that the local component `Π_{v*₁}` at
    `v*₁` is supercuspidal. The induction on p.202 produces cuspidal
    representations `Π(a, i)` in `CU(n(a, i), E_i)` with local component
    supercuspidal at the prime dividing `v*₁`. The conclusion on p.203 again
    gives a supercuspidal local component at `v*₁`.
  - Theorem 1.2(ii): printed p.185 (PDF p.9). `π_i ≅ π̌_i ∘ c` with `c` the
    non-trivial element of `Gal(E/E₀)`, `E = E₀ · K₀`, and the primes `p_i`
    split in `K₀`.
  - Section 2 setup: printed p.192 (PDF p.16). "We assume the rational prime
    p splits in K₀, so that v splits in E as the product of two primes v₁ and
    v₂."

  Harris's `E` has the form `E₀ · K₀`. Statement 3 holds for every CM field
  `E` containing an imaginary quadratic `K₀`, which is the generality of the
  Library's `Proposition48Problem`.
- **Operator plan.** Source `operator-external-inputs-plan-2026-11-16`, file
  `external-inputs-plan.tex`:
  - Section 4.8, Remark 4.2 (lines 859–894), whose claims concern "cuspidal
    unitary" representations supercuspidal at the auxiliary places;
  - the recommendation closing Section 4.6 (lines 767–770), which restricts
    to representations "supercuspidal at a pair of conjugate places with a
    single prime above each".

  These are cited in the same way in the Markdown of
  `RestrictedCyclicWeakBaseChangeComplexPlaceStatement`.
- **Operator ruling.**
  `/home/taskhub/pilot/correspondence/afc4eb775dc157d6807bbc17caa2b02b.md`,
  point 4(ii): the branches apply B7 only to classes that are supercuspidal at
  the auxiliary conjugate pair, since every descent and induced class is.
  Statements 2 and 3 make the conjugate half of that pair available from
  conjugate self-duality and from the split prime.

The three statements are derived consequences of these sources and of
standard facts: Schur's lemma, compactness of the norm-one idele classes, and
supercuspidality of contragredients. They are not quotations of any of them.
