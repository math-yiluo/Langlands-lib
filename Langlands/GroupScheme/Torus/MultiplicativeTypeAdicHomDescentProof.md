# Proof: finite étale descent of the adic Hom comparison

`Langlands.GroupScheme.multiplicativeTypeAdicHomDescent` proves
`MultiplicativeTypeAdicHomDescentStatement.{u}` for every universe `u`.

## Statement

Assume the diagonalizable adic Hom comparison
`DiagonalizableAdicHomComparisonStatement.{u}`. Let `A` be a noetherian ring,
`I`-adically complete for an ideal `I`. Let `H` and `G` be group schemes over
`Spec A`, with `G` affine over `Spec A`. Suppose there is a finite, étale,
surjective morphism `p : S' → Spec A` such that the base change of `H` along `p`
is diagonalizable. Then restriction of homomorphisms `H ⟶ G` to compatible
systems over the thickenings `Spec A/I^(n+1)`, `System.restrict I H G`, is
bijective. This is the finite étale descent step of SGA 3, Exposé IX,
Théorème 7.1.

## Proof

After introducing the hypotheses and destructuring the cover, the proof is a
single application of `HomScheme.Adic.restrict_bijective_of_finiteEtale` from
`Langlands.GroupScheme.HomScheme.AdicFiniteDescent`. The finiteness, étaleness
and surjectivity hypotheses on `p` become local instances, and diagonalizability
of `(baseChange p).obj H` is passed directly. The theorem needs two affine
inputs:

* `AffineAlgebraizationExists I H G` is discharged by
  `HomScheme.Adic.exists_isAlgebraization_affine hdiag`.
* `AffineAlgebraizationUnique I H G` is discharged by
  `HomScheme.Adic.eq_of_isAlgebraization_affine hdiag`.

Both come from `Langlands.GroupScheme.HomScheme.AdicFiniteTest`. For a finite
ring map `ψ : A →+* C` over which `H` becomes diagonalizable, they apply the
assumed diagonalizable comparison to `C` with the ideal `I.map ψ`. Such a `C` is
again noetherian and `I.map ψ`-adically complete, and the base change of `G`
stays affine. The pulled-back system then has a unique algebraization over
`Spec C`. This is where the noetherian, completeness and affineness hypotheses
of the statement are used.

`restrict_bijective_of_finiteEtale` then concludes as follows. Its Markdown has
the details.

* Every finite test scheme is isomorphic to the spectrum of a finite
  `A`-algebra, so the affine inputs hold over the cover `S'` and the double
  overlap `S' ×_A S'`.
* Injectivity: two homomorphisms with the same restriction system have
  constant families over `S'` that algebraize the same system. They agree by
  uniqueness, and pullback along `p` is faithful.
* Surjectivity: a system has an algebraization over `S'`. Its two pullbacks to
  the overlap agree by uniqueness, so it satisfies the descent condition.
  Étale descent of homomorphisms, `Descent.EtaleHomDescent`, gives a
  homomorphism `H ⟶ G`. Its restriction system is the given one. This is
  checked level by level after flat surjective base change along the pullback
  of `p` to each thickening.

## Dependencies

* `Langlands.GroupScheme.HomScheme.AdicAlgebraization`: the predicate
  `System.IsAlgebraization`.
* `Langlands.GroupScheme.HomScheme.AdicFiniteDescent`: transport from finite
  test schemes to spectra of finite algebras, and the descent argument.
* `Langlands.GroupScheme.HomScheme.AdicFiniteTest` (Worker 323): the affine
  existence and uniqueness of algebraizations.
* `Langlands.GroupScheme.HomScheme.AdicBaseChange` and
  `Langlands.GroupScheme.HomScheme.AdicSystemBaseChange` (Worker 323):
  pullback of adic systems along ring maps, used by `AdicFiniteTest`, and
  `evaluate_injective_of_flat_surjective`, used by `AdicFiniteDescent`.

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
