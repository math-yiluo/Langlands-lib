# Faithfulness of the actual rational Tate action at every prime

The theorem `Langlands.AbelianScheme.Tate.fieldPrimeRationalFaithfulness` proves
the published `FieldPrimeRationalFaithfulnessStatement` with its full universe
parameter. It applies to every algebraically closed characteristic-zero field,
every pair of actual abelian schemes over its spectrum, and every natural prime.

The proof first clears the rational denominator of an element of
`Rationalization.Hom A B`. Its positive integer multiple is `1 ⊗ f` for an
actual homomorphism `f`. If the element has zero prime Tate action, the
pure-tensor formula for `PrimeAdic.rationalHomMap` shows that `f` has zero
rational prime Tate operator. Injectivity of the existing integral-to-rational
map then gives zero on the integral prime Tate module. Divisibility of actual
geometric points supplies a coherent prime Tate lift of every prime-power
torsion point, using `evaluation_surjective_of_pow`. Evaluation therefore
shows that all actual prime-power level maps of `f` vanish.

The new `PrimePowerTorsion.dense_locus` theorem gives Zariski density of these
actual torsion sections. Its homomorphism detection lemma forces `f = 0`.
The original rational homomorphism is consequently zero, since its positive
integer multiple is zero in a rational vector space. The kernel criterion for
the existing rational-linear Hom map proves injectivity.

The torsion-density helpers generalize the published two-power closure
construction. Their separate Markdown files describe the reduced closure,
connectedness and cardinality argument. The final module imports the full Tate
faithfulness proof only for the general algebraic denominator-clearing lemma
`exists_nsmul_eq_one_tmul`; the geometric density input in this proof is for the
selected prime.

This is a derived proof of the target, whose source provenance is Milne,
*Abelian Varieties*, author revision January 2, 2022, Theorem 12.5 and
Lemma 12.6, pp.21–22 (`milne-abelian-varieties-1986-author-2022`).
It implements the weaker rational faithfulness consequence by torsion density,
rather than formalizing finite freeness and the torsion-free cokernel of
Theorem 12.5. The retained correction to that proof is recorded in
`milne-abelian-varieties-1986-errata-2026-10-25`. The geometric density route
corresponds to Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary version, Chapter V, Theorem (5.30), printed p.84 / PDF p.88
(`edixhoven-vandergeer-moonen-abelian-varieties-draft`).

No target or existing imported module is changed.
