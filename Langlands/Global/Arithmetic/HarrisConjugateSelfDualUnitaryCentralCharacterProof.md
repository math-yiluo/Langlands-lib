# Conjugate self-dual cuspidal realizations have unitary central characters

`Langlands.Global.Harris.conjugateSelfDualUnitaryCentralCharacter` proves the
Library statement `Langlands.Global.Harris.ConjugateSelfDualUnitaryCentralCharacterStatement`
(Statement 1 of
[HarrisAuxiliaryConjugatePairStatement](HarrisAuxiliaryConjugatePairStatement.md#1-conjugateselfdualunitarycentralcharacterstatement))
at universe `u`. The statement is not changed and has no extra premise. Take a
CM number field `E` with compact adele quotient and an actual irreducible
cuspidal realization `S` of `GL_{r+1}` over `E` whose isomorphism class is
conjugate self-dual. The theorem gives a continuous character `ω` of the idele
class group with `‖ω x‖ = 1` for all `x` and `S.HasCentralCharacter ω`.

The proof follows steps 1–4 of the statement note. Steps 1, 3 and 4 come from
the Library. The new content is step 2, `ω ∘ c = ω⁻¹`. From the pairing it
uses only the invariance under the finite adelic group and the injectivity of
`x ↦ B (·) x`. The proof does not use the compact-subgroup or Lie-algebra
invariance, the surjectivity onto contragredient functionals, or cuspidality.

## Implemented proof

1. **The pairing and the central character.**
   `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff` turns the
   hypothesis into `S.realization.IsConjugateSelfDual`. This gives a bilinear
   pairing `B` on the space of `S.realization` with finite invariance
   `B (π(finiteConj d) y) (π(d) x) = B y x` for every `d` in the finite adelic
   group, and with `x ↦ B (·) x` injective.
   `OperatorRealization.existsUnique_hasCentralCharacter`, applied with
   `S.irreducible`, gives the central character `ω` with
   `S.realization.HasCentralCharacter ω`.

2. **A nonzero pairing value** (`exists_pairing_ne_zero`). Irreducibility
   gives a form `f₀` and a point `x₀` with `f₀(x₀) ≠ 0`
   (`OperatorRealization.exists_evaluate_ne_zero`). So the space is nonzero.
   If `B` vanished identically, every `B (·) x` would be zero, and
   injectivity of `x ↦ B (·) x` would force every vector to be zero. Hence
   `B y x ≠ 0` for some `y`, `x`.

3. **Finite scalar matrices act by `ω`** (`finiteRepresentation_scalar`). Let
   `z` be an idele with trivial infinite part (`IdeleDensity.infPart z = 1`).
   Its scalar matrix `AdelicGL.scalar E n z` equals the image under
   `AdelicGL.ofFinite` of its finite component (`ofFinite_finite_scalar`,
   checked entrywise). Evaluating at a point `g`, the finite operator of this
   component is right translation by the scalar matrix
   (`evaluate_finiteRepresentation`). The scalar matrix is central
   (`AdelicGL.scalar_commute`), so the translate equals the left translate
   by the scalar matrix. `OperatorRealization.centralCharacter_evaluate`
   evaluates the left translate as `ω(z) f(g)`. Injectivity of the maps to
   continuous functions turns this pointwise identity into an equality of
   vectors.

4. **Conjugation of finite scalar matrices** (`adelicConj_scalar`,
   `infPart_ideleEquiv`). Entrywise CM conjugation sends the scalar matrix of
   `z` to the scalar matrix of the conjugate idele
   `ideleEquiv (fieldConj E) z`, and this conjugate idele again has trivial
   infinite part. Since `finiteConj` of the finite component of an adelic
   matrix is the finite component of its entrywise conjugate
   (`CMConjugation.finite_adelicConj`), `finiteConj` of the finite scalar
   matrix of `z` is the finite scalar matrix of `c z`.

5. **The product relation** (`mul_eq_one_of_pairing`). Apply finite
   invariance to the finite scalar matrix `d` of `z`, with the vectors of
   step 2. By steps 3 and 4, `π(finiteConj d) y = ω(c z) • y` and
   `π(d) x = ω(z) • x`. Bilinearity turns invariance into
   `ω(c z) ω(z) B y x = B y x`, so `ω(c z) ω(z) = 1` since `B y x ≠ 0`. The
   bilinear cancellation is the abstract lemma `mul_eq_one_of_bilinear`,
   stated for an arbitrary complex module. This avoids slow rewriting inside
   the concrete realization space.

6. **Extension to all ideles** (`isConjugateInverse_of_mul_eq_one`). The map
   `φ(z) = ω(c z) ω(z)` is a continuous homomorphism from the ideles to `ℂˣ`,
   because `ω` and `ideleEquiv (fieldConj E)` are continuous homomorphisms.
   Its kernel is a closed subgroup. It contains every principal idele: the
   conjugate of the diagonal idele of `a` is the diagonal idele of `c a`
   (`ideleEquiv_diagonal`), and `ω` is trivial on principal ideles
   (`centralIdeleCharacter_principal`). It contains every local finite idele
   `finiteIdeleInclusion v a`, by step 5, because these have trivial infinite
   part (`IdeleDensity.infPart_finiteIdeleInclusion`). The Library density
   lemma `IdeleDensity.eq_top_of_isClosed`, used with the empty set of
   excluded places, shows that the kernel is the whole idele group. Passing
   to idele classes, `ω(c q) = ω(q)⁻¹` for every idele class `q`. This is
   `Harris.IsConjugateInverse ω`.

7. **Unitarity.** `HeckeConjugateInverse.isUnitary_of_isConjugateInverse`
   (steps 3–4 of the statement note) turns `IsConjugateInverse ω` into
   `‖ω x‖ = 1` for all `x`. Together with `S.HasCentralCharacter ω`, this is
   `HasUnitaryCentralCharacter S`.

## Relation to the sources

The statement note gives the mathematical argument and its provenance:
Harris (1998), Theorem 1.2(ii) (printed p.185), for conjugate self-duality
`π ≅ π̌ ∘ c`; the unitarity of the central character is a derived standard
consequence. Step 2 of that argument mentions central elements of all three
kinds: finite scalar ideles, the centre of the standard compact subgroup and
the scalar Lie algebra. The Lean proof uses only the finite scalar ideles.
The relation `ω(c z) ω(z) = 1` for ideles with trivial infinite part, together
with continuity and the principal ideles, already determines `ω ∘ c = ω⁻¹` on
all ideles, by the density lemma of step 6.
