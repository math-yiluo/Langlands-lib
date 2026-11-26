# Proof that arithmetic pullback preserves conjugate self-duality

Module `Langlands.Automorphic.ArithmeticComapConjugateSelfDualProof`.

The theorem
`Langlands.Automorphic.arithmeticComapConjugateSelfDual :
ArithmeticComapConjugateSelfDualStatement.{uK, uL}` proves the published statement
`Langlands.Automorphic.ArithmeticComapConjugateSelfDualStatement` (module
`Langlands.Automorphic.CuspidalArithmeticTransportStatement`), unchanged, at independent
field universes `uK` and `uL`. It uses no hypotheses beyond those of the statement and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

For CM number fields `K : Type uK`, `L : Type uL`, a ring isomorphism `e : K ≃+* L`,
`r : ℕ` and an irreducible cuspidal class `c : CuspidalOperatorRealization.IsoClass L r`:
if `c.IsConjugateSelfDual`, then
`(CuspidalOperatorRealization.IsoClass.arithmeticComap e c).IsConjugateSelfDual`.
Conjugate self-duality of a class means that a representative has a full
conjugate-contragredient pairing (module `Langlands.Automorphic.ConjugateContragredient`):
a bilinear pairing invariant under the operators twisted by the CM involution in the
first variable, whose partial map is a bijection onto the contragredient functionals.

## The implemented proof

The proof applies
`CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap` (module
`Langlands.Automorphic.ConjugateContragredientArithmeticTransport`). That module carries
out the following argument; its Markdown has the details.

1. **Reduction to a representative.** By definition, `c.IsConjugateSelfDual` is
   conjugate self-duality of the full-operator class `c.toOperatorClass`, so some
   realization `S` over `L` with `S.isoClass = c.toOperatorClass` has a
   conjugate-contragredient pairing `B`. By the published
   `IsoClass.toOperatorClass_arithmeticComap`, the full-operator class of
   `IsoClass.arithmeticComap e c` is `OperatorRealization.IsoClass.arithmeticComap e
   c.toOperatorClass`, and that class has representative `S.arithmeticComap e`.
2. **The CM involutions commute with `e`.** For every complex embedding `ψ` of `L`, the
   CM involutions of `K` and `L` induce complex conjugation under `ψ ∘ e` and under `ψ`,
   so `e ∘ c_K = c_L ∘ e` (`CMConjugation.ringEquiv_complexConj`, module
   `Langlands.Global.CMConjugationArithmeticTransport`). Hence the arithmetic transports
   of the finite adelic group, of the standard compact subgroup and of the real Lie
   algebra commute with the CM conjugations (`finiteEquiv_finiteConj`,
   `compactEquiv_compactConj`, `realLieEquiv_lieConj`).
3. **Pulling back the pairing.** With `φ = S.arithmeticComapEquiv e`, the pairing
   `B' y x = B (φ⁻¹ y) (φ⁻¹ x)` satisfies the three twisted invariance identities over
   `K`. The reason is that `φ⁻¹` intertwines the finite, compact and Lie algebra actions
   of the pullback with those of `S` through the arithmetic transports, which commute
   with the conjugations by step 2.
4. **Contragredient functionals.** `l ↦ l ∘ φ⁻¹` maps the contragredient functionals of
   `S` bijectively onto those of the pullback. Each direction is an instance of a general
   lemma: pulling back a functional along a linear map that intertwines two
   representations through a group homomorphism `α` preserves smoothness of the dual
   action when `α` is continuous, and preserves finiteness of the orbit span. So
   `B'.flip x = B.flip (φ⁻¹ x) ∘ φ⁻¹` is a contragredient functional, `B'.flip` is
   injective because `B.flip` and `φ⁻¹` are, and every contragredient functional `l` of
   the pullback is `B'.flip (φ x)`, where `l ∘ φ = B.flip x`.

So `B'` is a full conjugate-contragredient pairing of `S.arithmeticComap e`, not only a
pairing satisfying the three invariance identities.

## Source

The statement is a transport-of-structure interface, not a statement of the literature.
It is used silently in Harris (1998), *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134, 177–210 (registered source
`harris-1998-local-langlands`), proof of Proposition 4.8, printed p.203
(`math_9611226v1.tex`, lines 1646–1663). There the Galois conjugates `α^j(Π(e,t-1))`
of a cuspidal representation `Π(e,t-1)` are treated as cuspidal representations with
the corresponding properties, such as a supercuspidal component at the place above
`v(*)_1`. As the statement's Markdown records, conjugate self-duality of the conjugates
(an isomorphism with the contragredient composed with the CM involution, as in Harris
(1998), Theorem 1.2(ii)) enters the same way. A Galois conjugate is the case `K = L`,
`e = σ.symm` of `arithmeticComap e`.
