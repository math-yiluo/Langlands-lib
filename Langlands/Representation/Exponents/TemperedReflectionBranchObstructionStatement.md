# A selected Weyl-branch obstruction for tempered quotient reflection

Author: Worker 497. The statement boundary was designed by Worker 359 in
coordination with Worker 430.

`Langlands.GLTemperedReflectionBranchObstructionStatement` is a Prop-valued
statement definition. It isolates an internal derived boundary of the proof
of Silberger 1978, Proposition 5.8, printed p.102. Silberger does not state
this as a separately numbered theorem. This pair supplies no Lean proof of
branch selection, analytic continuation, or quotient reflection.

## Unchanged reflection inputs

The complete input telescope through the two surjections onto `J` is copied
from the published
[`GLTemperedRelativeQuotientReflectionStatement`](../Classification/RelativeRecoveryStatement.md).
The field and representation carriers have five independent universes:
`uF` for the actual `PadicField p`, `uV` for the fine representation,
`uM` for the middle representation, `uW` for the coarse representation,
and `uZ` for `J`. The prime, compatible `TopologicalData T`, and positive
ambient rank `n` are arbitrary. Induced carriers retain the saturation
`max uF uV` or `max uF uW` of the imported constructions.

The coarse ordered block shape is `B`. A refinement `Q` gives
`D = B.flatten Q`; a refinement `R` of `D` and a direct refinement `S` of
`B` come with the actual shape equality
`h : D.flatten R = B.flatten S`. The fine representation `ω` is irreducible,
Levi-cuspidal and unitarizable. Its determinant parameter `v₀` satisfies
`RelativeRegularComparison.IsPositiveRootParameter D R v₀`: a strictly
positive combination of the adjacent scalar roots within each middle
block, with the existing inverse-block-size factors in determinant
coordinates. The direct fine objects are literally `ωB = h ▸ ω` and
`vB = h ▸ v₀`.

The middle representation `σ` is irreducible and analytically square
integrable modulo its full product-Levi center. There is an actual
surjective intertwiner from
`innerInduced T D R (fineTwist T D R ω v₀ 0)` onto `σ`.
The coarse representation `π` is an arbitrary irreducible analytically
tempered representation of the whole `B`-Levi. There is no middle support
map, fine support map, or constituent premise on `π`. These analytic
predicates retain the published quantification over Borel Haar measures
on the actual central quotient.

For every real determinant parameter `t` with `StrictAnti t`, put
`πt = Rep.of (T.leviRealPowerTwist B t π.ρ)`. An arbitrary actual irreducible
`J` receives both of the following actual surjective intertwiners:

- from `CuspidalJacquetMultiplicity.induced T B πt`;
- from `RelativeRecovery.fineAmbientInduced T B S ωB vB t`.

The second representation is the ambient fine induction with determinant
exponents `-vB(k) + t(parent(k))`. Both maps have the same target `J`.
The hypotheses do not choose a head or assume head uniqueness.
`StrictAnti t` preserves every real central shift and imposes no sign
condition on individual entries. The one-block case is included; its
strict-decrease condition is vacuous.

## The single additional hypothesis and selected branch

After precisely those inputs, the statement assumes that no actual
surjective intertwiner exists from

```lean
(RelativeJacquetMultiplicity.innerInduced T B S
  (RelativeJacquetMultiplicity.fineTwist T B S ωB vB 0)).ρ
```

to `π.ρ`. This is the negation of the inner-quotient conclusion of the
reflection statement, added as the sole contradiction hypothesis.

Let `C = B.flatten S`. The conclusion uses ordinary existential quantifiers
to select one `w : Equiv.Perm (Fin n)` and one proof
`hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C w`. This is
conjugacy of the actual embedded fine Levi by the actual permutation matrix.
All three following clauses concern that same `w`:

1. `w ∉ Geometric.blockWeyl B`, where the coarse Weyl subgroup consists of
   the actual permutations preserving each coarse block.
2. On every full diagonal coordinate `a : Fin n`,

   ```lean
   vB (Geometric.blockIndex C (w.symm a)) -
       t (Geometric.blockIndex B (w.symm a)) =
     vB (Geometric.blockIndex C a) -
       t (Geometric.blockIndex B a)
   ```

3. There is the actual class occurrence

   ```lean
   T.IsOppositeJacquetClassExponent C
     (CuspidalJacquetMultiplicity.induced T B π)
     (Rep.of (CuspidalSupport.transport C C w hw
       (T.leviRealPowerTwist C (-vB) ωB.ρ)))
   ```

The Lean expression explicitly supplies `ωB.V`, `ωB.hV1`, and `ωB.hV2`
to these same three constructors. These are the carrier and stored
additive-group and complex-module instances of the literal transported
bundle `ωB`; supplying them resolves elaboration without adding data
or a hypothesis.

The stabilizer equation is at the fixed real `t` from the hypotheses.
Transport sends source coordinate `a` to target coordinate `w a`, hence a
transported exponent at target `a` reads the source at `w.symm a`.
The real determinant twist is applied to the actual fine base representation
before inverse-conjugation transport. If
`e = CuspidalSupport.leviConjugation C C w hw`, its action at a target
Levi element `m` is the action of
`T.leviRealPowerTwist C (-vB) ωB.ρ` at `e.symm m`. Both the character
and the base action are evaluated there. No second transport of the offset,
scalar-character replacement, or representation equality inferred solely
from coordinates occurs in the statement.

The ambient representation in clause 3 is the entire **untwisted**
outer induction of `π`. The imported
`T.IsOppositeJacquetClassExponent` predicate requires the candidate to be
irreducible and admissible and to be an actual subquotient of the
normalized opposite Jacquet module: an invariant subspace with an actual
surjective intertwiner onto the candidate. This is an actual
representation-class occurrence, not just an equality of central exponents.
The Jacquet construction uses the lower block radical and the positive
half of the upper modulus.

## Original-source provenance and zero specialization

The original is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. **236** (1978), 95–104, retained as
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
Its registered source ID is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
SHA256 is
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The supporting fine and middle data are on printed p.99, the responsible
branch definition is recalled from p.101, and the arbitrary-tempered
contradiction and continuation argument is on p.102. Worker 497 read those
passages and inspected their page images, together with the parameter
convention on p.96 and the class-exponent definition on p.97.
No retained source-specific erratum was found. The published
[scope audit](../../../notes/jacquet/silberger-lemma53-scope.md) and
[continuation-parameter note](../../../notes/jacquet/silberger-continuation-parameters.md)
are source-reading notes, not author errata or Lean theorems.

The source's p.96 convention is
`χ_ν(m) = q^(i⟨ν,H(m)⟩)`, so real source parameters describe unitary twists.
In the Library determinant convention the corresponding complex parameter
is `i ν`. In particular `ν = -i t` gives determinant exponent `t`, and
the fine parameter `i(v₀-t)` gives `-v₀+t` after restriction.

Under the contradiction hypotheses, the p.102 argument selects responsible
branches in a set `Y` disjoint from the coarse Weyl group. Their fixed real
stabilizer equation is `s(v₀-t) = v₀-t`. It asserts the continuation of their
actual class occurrences in the varying unitary coarse family:

\[
\omega_{\,i\,s v_0+\nu''}
\in \mathfrak D_{\,I(P'',\,\sigma''_{\nu''})}(P,A)
\quad\text{for all }\nu''\in\mathfrak a''^* .
\]

The positive sign before `i s v₀`, the absence of `s` on the added `ν''`,
and the subscript `ν''` on the ambient inducing representation all matter.
Setting this varying parameter to zero gives the untwisted ambient induction
and the transported fine twist with real offset `-vB` in clause 3.
The statement requests only this resulting zero occurrence, together with
selection and the fixed real stabilizer. It does not assert a universal
continuation family, nor introduce an assumed selection or comparison
certificate.

The distinct sentence in Lemma 5.6, p.101, varies the middle-Levi parameter
and asserts occurrence for almost all parameters. An almost-everywhere
assertion cannot be specialized at zero. The present source-derived
boundary uses the all-parameter p.102 assertion; neither its selection nor
its continuation has been proved by this pair.

The actual family definitions of
[`ComplexTwistFamilies`](ComplexTwistFamilies.md) are imported without
modification. They construct actual twists, induced families, transports
and occurrence predicates, with no selection or continuation theorem.
The conclusion here directly displays the zero representations instead
of using a family-expression abbreviation. Consequently no additional
family zero-specialization identification is needed or asserted.

## Remaining proof obligations and scope

The unproved content isolated here is the implication from the full common
quotient data and absence of an inner quotient to one branch with all three
properties. A proof must establish the responsible-branch selection and
the required class occurrence, including the actual transport convention.
In particular, the repaired constituent-only scope of Lemma 5.3 does not
automatically apply to this arbitrary `π`. Unrestricted Lemma 5.3 or
Corollary 5.4 is not invoked as justification.

After this implication, a proof of reflection still separately needs
analytic temperedness of the untwisted induced representation,
representation-to-cone extraction with the correct block-size weights,
and numerical rigidity. Determinant offsets become block-scalar exponents
only after multiplication by the corresponding block sizes. The published
numerical result `Langlands.Exponents.closedConeStabilizerRigidity`
supplies none of the actual occurrence or temperedness hypotheses.
These later steps are not premises or conclusions of this statement.

Regular-positive head uniqueness is needed in a proof to identify arbitrary
weak quotient witnesses with the source's distinguished `J`; it is not an
extra hypothesis here. The full reflection theorem and downstream
Langlands uniqueness or classification cannot be assumed to prove this
prerequisite.

The conclusion supplies no occurrence in the prescribed quotient `J`,
no Jordan–Hölder multiplicity or Hom-dimension equality, no cosocle
comparison, and no head theorem. The conditional actual-`J` Hom route
that assumes reflection is a different implication and cannot establish
this prerequisite. Existing statement interfaces and their dependencies
are unchanged. A proof successor must target this exact declaration after
its independent acceptance and Library publication.
