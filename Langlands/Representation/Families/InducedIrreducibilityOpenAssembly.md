# Renard VI.8.4 from admissibility, compactness and uniform detection

Worker 452, using Worker 1444's actual universal induced family in
`ActualLeviUnramifiedInducedFamily`. This module is the final assembly for
Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026),
VI.8.4 Proposition, printed pp. 192–193, PDF pp. 198–199. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. It proves
the closed proposition `InducedIrreducibilityOpenStatement` from three other
propositions. The first two are published Library statements. The third,
`InducedTwistsUniformDetectionStatement`, is stated in this development. The
module does not prove any of the three.

`isFullSpecialization_of_toRingHom_eq` says that `IsFullSpecialization S A χ D`
depends on the complex character `χ` of `S` only through its underlying ring
map. Suppose `χ.toRingHom = φ`. Suppose also that, with the algebra structure
`φ.toAlgebra` on `ℂ`, there is an intertwiner from `A` to `D` with the scalar
law `f (s • v) = φ s • f v` whose coefficient scalar extension is bijective.
Then `A` specializes fully to `D` at `χ`. The proof substitutes `φ` by
`χ.toRingHom`, after which the hypothesis is the definition.

`universalFamily_isGlobalCoefficientFamily` works with the binders of the
closed proposition: a nonarchimedean local field `k`, a connected reductive
group `G` over `k`, and a parabolic subgroup `P` with rational Levi subgroup `M`
and unipotent radical `U`. The groups `G(k)` and `M(k)` carry their canonical
topologies, and the scheme of `M` is affine and locally of finite type. It
assumes that the quotient of `G(k)` by the points of `P` is compact, and it
takes an admissible smooth complex representation `ρ` of `M(k)`. It then proves
`IsGlobalCoefficientFamily` for Worker 1444's family
`ActualLevi.universalFamily p l r hp hl hr hmul ρ`, with these data:

- the coefficient algebra is the algebra of regular functions on the
  unramified characters transported to the Levi image;
- the algebra equivalence is `(ActualLevi.regularAlgebraEquiv p l hp hl).symm`;
- the fiber at `ψ` is `ActualLevi.fiber p l r hp hl hr hmul ρ ψ`, the
  normalized parabolic induction `leviInductionFunctor` of the twist `ρ ⊗ ψ`.

Freeness and finiteness of compact fixed vectors are
`ActualLevi.universalFamily_fixed_finite_free`, which uses admissibility and
compactness. For full specialization at `ψ`, the proof applies
`isFullSpecialization_of_toRingHom_eq` to
`ActualLevi.universalFamily_specialization`. Here `φ` is evaluation of the
transported regular functions at `ActualLevi.parameterEquiv p l hp hl ψ`. The
two ring maps agree on each `b`: both send `b` to the value of `b` at the
transported parameter. This follows by rewriting with
`coefficientCharacter_apply`, `ActualLevi.regularAlgebraEquiv_symm_apply` and
`UnramifiedNormalized.evaluation_apply`.

`inducedIrreducibilityOpen_of_statements` assumes three propositions:

- `RationalPointsIrreducibleAdmissibleStatement.{u, v}`, Jacquet's theorem
  that irreducible smooth representations are admissible (Renard VI.2.2);
- `ArbitraryParabolicQuotientCompactStatement.{u}`, compactness of the
  rational-point quotient of every parabolic subgroup (Renard V.5.1);
- `InducedTwistsUniformDetectionStatement.{u, v}`: for each irreducible `ρ`,
  one compact open subgroup of `G(k)` has nonzero fixed vectors in every
  irreducible subquotient of every induced unramified twist of `ρ`.

From these it proves `InducedIrreducibilityOpenStatement.{u, v}`, with exactly
its published binders and universes. After introducing the binders and the
instances of the statement, the proof gets compactness of the quotient from the
second proposition. The first proposition, applied to `M` and `ρ`, gives
admissibility of `ρ`; the canonical topology of `M(k)` there is definitionally
the Levi topology of the target. The proof then applies
`InducedIrreducibilityOpenReduction.exists_principal_neighborhood_of_detection`
to the third proposition, the family `ActualLevi.universalFamily`, the
equivalence `(ActualLevi.regularAlgebraEquiv p l hp hl).symm` and the global
family property above.

So the remaining obligations for the closed proposition are exactly these
three propositions. The theorem does not assume them anywhere else, and it
introduces no further hypotheses.

The structure `Inputs.{u, v}` is a proposition with three fields,
`admissible`, `quotientCompact` and `uniformDetection`. They are the three
propositions above, at the same universes. `inducedIrreducibilityOpen_of_inputs`
proves `InducedIrreducibilityOpenStatement.{u, v}` from `Inputs.{u, v}` by
passing its three fields to `inducedIrreducibilityOpen_of_statements`.
Nothing in the module proves `Inputs`.
