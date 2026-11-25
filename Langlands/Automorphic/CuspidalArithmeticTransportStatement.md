# Arithmetic transport of unitarity, supercuspidal components and conjugate self-duality

Module `Langlands.Automorphic.CuspidalArithmeticTransportStatement`. Statements
only (Prop-valued definitions); nothing is proved here.

## Setting

For number fields `K`, `L` and a ring isomorphism `e : K ≃+* L`, the Library
transports cuspidal realizations and their classes from `L` to `K`:
`CuspidalOperatorRealization.arithmeticComap e` and
`CuspidalOperatorRealization.IsoClass.arithmeticComap e`
(`Langlands/Automorphic/OperatorArithmeticTransport.lean`,
`Langlands/Automorphic/OperatorArithmeticTransportClasses.lean`). Finite places
move with `finitePlaceEquiv e : FinitePlace L ≃ FinitePlace K`
(`Langlands/Global/AdelicFunctoriality/Finite.lean`), which sends a place `w` of
`L` to its pullback along `e`. The Galois conjugate `IsoClass.galoisConj σ c` is
by definition `arithmeticComap σ.symm c`. So each statement below contains its
Galois-conjugation case (`K = L`, `e = σ.symm`).

Every statement quantifies over the number fields `K : Type uK`, `L : Type uL`
and over the instances `CompactSpace (AdeleQuotient K)` and
`CompactSpace (AdeleQuotient L)`. These instances are needed to form cuspidal
realizations and are true for every number field, so they restrict nothing.

## Statements

### `ArithmeticComapUnitaryCentralCharacterStatement.{uK, uL}`

- Hypotheses: `e : K ≃+* L`, `r : ℕ`, a cuspidal realization
  `S : CuspidalOperatorRealization L r`, and
  `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`: some
  character `χ` of the idele class group of `L` with `‖χ x‖ = 1` for all `x`
  is a central character of `S`.
- Conclusion: `HasUnitaryCentralCharacter (S.arithmeticComap e)`.
- Why: by the Library theorem
  `CuspidalOperatorRealization.arithmeticComap_hasCentralCharacter_iff`,
  `S.arithmeticComap e` has central character `HeckeCharacter.comap e χ`. This
  character is `χ` composed with the isomorphism of idele class groups induced
  by `e`, so it takes the same values and is unitary.

### `ArithmeticComapSupercuspidalComponentStatement.{uK, uL, uV}`

- Hypotheses: `e : K ≃+* L`, `r : ℕ`, a cuspidal class
  `c : CuspidalOperatorRealization.IsoClass L r`, a finite place `w` of `L`, and
  `c.HasSupercuspidalComponent w`: some representative of `c` has a spectral
  presentation with carrier universe `uV` whose local component at `w` is
  supercuspidal.
- Conclusion: `(IsoClass.arithmeticComap e c).HasSupercuspidalComponent
  (finitePlaceEquiv e w)`, with presentations in the same carrier universe `uV`.
- Why: a spectral presentation of a representative `S` transports along `e` to
  one of `S.arithmeticComap e`. Its local component at `finitePlaceEquiv e w`
  is the component of `S` at `w`, read through the isomorphism of completions
  `K_{finitePlaceEquiv e w} ≅ L_w` induced by `e`. An isomorphism of local
  fields preserves supercuspidality (vanishing of all proper Jacquet modules).

### `ArithmeticComapConjugateSelfDualStatement.{uK, uL}`

- Hypotheses: `K` and `L` are CM fields (`IsCMField`), `e : K ≃+* L`, `r : ℕ`,
  `c : CuspidalOperatorRealization.IsoClass L r`, and `c.IsConjugateSelfDual`.
  By `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff`, this
  says that a representative `S` (equivalently, every representative) has
  `S.realization.IsConjugateSelfDual`
  (`Langlands/Automorphic/ConjugateContragredient.lean`). That is, there is a
  complex bilinear pairing `B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ` with
  `IsConjugateContragredientPairing B`, which has two parts:
  1. `B` is invariant under the operators twisted by the CM involution of `L`
     in the first variable (`IsConjugateInvariantPairing`):
     `B (π(conj d) y) (π(d) x) = B y x` for the finite adelic group,
     the same identity for the standard compact subgroup at infinity, and
     `B (X^conj · y) x + B y (X · x) = 0` for the real Lie algebra;
  2. the partial map `x ↦ B (·) x` is a bijection from `S.Space` onto the
     contragredient functionals, the algebraic functionals that are smooth
     for the finite adelic group and finite for the standard compact subgroup
     (`IsContragredientFunctional`). Each `B (·) x` is such a functional, the
     map `B.flip` is injective, and every such functional is some `B (·) x`.

  So `B` is an isomorphism from the representation to its contragredient
  composed with the CM involution, as in Harris (1998), Theorem 1.2(ii).
  Part 2 makes `B` nondegenerate. Without it the zero pairing would satisfy
  part 1 for every realization.
- Conclusion: `(IsoClass.arithmeticComap e c).IsConjugateSelfDual`, in the same
  sense, for the CM involution of `K` and a representative over `K`.
- Why: the CM involution of a CM field is the unique automorphism that induces
  complex conjugation under every complex embedding. Hence
  `e ∘ conj_K = conj_L ∘ e`. Let `φ = S.arithmeticComapEquiv e`, the
  continuous linear equivalence `S.Space ≃L[ℂ] (S.arithmeticComap e).Space`
  (`Langlands/Automorphic/OperatorArithmeticTransport.lean`). It intertwines
  the finite, compact and differential actions of the pullback with those of
  `S`, through `AdelicGLTransport.finiteEquiv`,
  `ArchimedeanCompactTransport.compactEquiv` and
  `ArchimedeanLieTransport.envelopingEquiv`
  (`arithmeticComapEquiv_finite`, `arithmeticComapEquiv_compact`,
  `arithmeticComapEquiv_differential`). Since `e` commutes with the CM
  involutions, these group and Lie algebra equivalences commute with the
  twists by the involutions. So `B' y' x' = B (φ⁻¹ y') (φ⁻¹ x')` satisfies the
  twisted identities of part 1 over `K`. The equivalences carry open compact
  subgroups to open compact subgroups and the standard compact subgroup onto
  the standard compact subgroup, so `l ↦ l ∘ φ⁻¹` maps the contragredient
  functionals of `S` bijectively onto those of the pullback. Hence
  `B'.flip = (· ∘ φ⁻¹) ∘ B.flip ∘ φ⁻¹` is again a bijection onto the
  contragredient functionals, which is part 2. Thus `B'` is a
  conjugate-contragredient pairing of the representative `S.arithmeticComap e`
  of `IsoClass.arithmeticComap e c`.

The field universes `uK`, `uL` and the carrier universe `uV` are independent.

## Provenance

The three statements are derived transport-of-structure interfaces. They are
not statements from the literature. The literature uses them silently whenever
it applies a Galois automorphism to an automorphic representation:

- Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p*, Invent. Math. 134, 177–210 (registered source
  `harris-1998-local-langlands`), proof of Proposition 4.8, printed p.203
  (`math_9611226v1.tex` lines 1646–1663). The Galois conjugates
  `α^j(Π(e,t-1))` of a cuspidal representation that is supercuspidal at the
  place above `v(*)_1` are again cuspidal, with supercuspidal component
  `α^j(Π(e,t-1)_{v(*)_1})` at that place.
- Plan note `operator-external-inputs-plan-2026-11-16`
  (`external-inputs-plan.tex`), Remark 4.2, proof of claim (3) (line 881):
  `α Π(b, i-1) = Π(α b, i-1)`, where `α` fixes the auxiliary place.

Unitarity and conjugate self-duality of the conjugates enter the same way,
because the children of Proposition 4.8 are unitary and conjugate self-dual
representations over CM fields.

## Consumers

The statements are hypotheses of reductions of Proposition 4.8 in
`Langlands/Global/Arithmetic/` (namespace `Langlands.Global.Harris`):

- `Proposition48ExactStabilizerPrimeBranchReductionStatement` (module
  `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionStatement`),
  the exact-stabilizer prime branch, takes the unitary and supercuspidal
  transports: unitarity and supercuspidality of the Galois conjugates of the
  transported child constituent over the step field `D`, for
  `CyclicWeakInductionSupercuspidalStatement` and for
  `HasDistinctMackeyComponents`.
- `Proposition48SingletonBranchTCReductionStatement` (module
  `Langlands.Global.Arithmetic.HarrisProposition48SingletonBranchTCReductionStatement`),
  the singleton branch, takes the supercuspidal and conjugate self-dual
  transports, for its child moved to `D`.
- `Proposition48PrimeBranchReductionStatement` (module
  `Langlands.Global.Arithmetic.HarrisProposition48PrimeBranchReductionStatement`),
  the general-position prime branch, takes all three (through
  `Proposition48PrimeBranchCommonInputs`), for the transport of children to
  `D` and Galois invariance.
