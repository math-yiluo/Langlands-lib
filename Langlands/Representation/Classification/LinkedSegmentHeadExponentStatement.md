# Exponent comparison for linked segment heads

Author: Worker 161. Target design: Worker 17; shared strict-comparison requirement:
Worker 391.

`Langlands.Classification.LinkedSegmentHeadExponentComparison.{uF,uV} F T`
is a proposition definition, not a theorem. It states an internal derived
comparison needed when ordering actual special segment heads. Its direct imports
are `Segments` and `Essential`.

## Exact statement

Fix any prime `p` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The field and carrier parameters `uF` and
`uV` are independent. With `w = max uF uV`, quantify over:

- segments `Δ Γ : T.Segment.{w,uF}`;
- actual smooth complex representations `π` of `GL_(Δ.degree)(F)` and `τ`
  of `GL_(Γ.degree)(F)`, both with carriers in `Type w`;
- strong-head hypotheses `T.IsSegmentHead Δ π` and `T.IsSegmentHead Γ τ`;
- arbitrary `u : UnitaryExponentData (T.determinantNorm Δ.degree) π.representation`
  and `v : UnitaryExponentData (T.determinantNorm Γ.degree) τ.representation`.

Under this single quantifier block the conclusion is the conjunction:

1. If `Δ.IsLinked Γ` and `¬ Δ.Precedes Γ`, then
   `v.exponent ≤ u.exponent`.
2. If `Δ.Precedes Γ`, then `u.exponent < v.exponent`.

The second implication needs no additional linkage premise because the existing
`Precedes` definition includes linkage. The first implication intentionally
states a weak inequality. No relationship is asserted for an unlinked pair.
In particular, the segments may have different lengths and degrees.

`IsSegmentHead` provides an actual supercuspidal representative of the beginning,
an irreducible quotient map from its increasing segment induction, and uniqueness
of that quotient kernel. `UnitaryExponentData` consists of a real exponent and an
invariant positive definite Hermitian form on the actual negative-exponent twist.
Thus `u` supplies a form on `ν^(-u.exponent)π`, and likewise for `v`.
The witnesses are universally quantified; no exponent, form, central character
or common cuspidal presentation is chosen in the statement. Existence of these
witnesses is not asserted.

There is no added analytic square-integrability, admissibility, equal-rank,
common-base or ordering/classification hypothesis. The segment representative,
induced representation and head all have the saturated carrier universe `w`,
since `max uF w = w`.

## Existing relations and the sign

The imported `Segment.IsLinked` says neither support contains the other and their
union is a segment support. `Segment.Precedes Δ Γ` adds that `Γ.base` is
`Δ.base.twist k` for some positive natural `k`. These are the existing relations,
not interval replacements introduced by this file.

Here `ν = |det|_F`, with the residue-normalized absolute value
`|ϖ|_F = q^(-1)`. Induction is from the standard upper block parabolic, with
positive half-modulus covariance and right translation. For
`Δ = [ρ, νρ, …, ν^(m-1)ρ]`, the strong-head hypothesis concerns the special
quotient `St_m(ρ)` of this increasing product. Henniart §2.6 uses precisely
this quotient convention; the segment socle is a different relation.

The expected scalar-character calculation explains the exponent sign without
adding a premise. Suppose, for this explanatory calculation, that a rank-`r`
representative of `ρ` has scalar character `ω`. On the scalar `z·1_(mr)`,
the block modulus is one, and the inducing factors have product scalar action

    ω(z)^m |z|^(r(0 + 1 + … + (m-1)))
      = ω(z)^m |z|^(r m(m-1)/2).

An actual quotient inherits this scalar action. If at a uniformizer
`|ω(ϖ)| = |ϖ|^(r a)`, its modulus on the head is therefore
`|ϖ|^(m r (a + (m-1)/2))`. Invariance of the positive form supplied by `u`
forces a scalar on `ν^(-u.exponent)π` to have modulus one. Evaluating on a
nonzero vector and using `|ϖ| ≠ 1` gives the expected formula

    u.exponent = a + (m - 1)/2.

The positive midpoint contribution, and the negative twist used to remove it,
agree with the Library conventions. The parameter `a` here is an explanatory
scalar-character exponent; this discussion does not assume or construct a
positive form on the initial cuspidal representation.

After proving nonperiodicity of integral norm twists, linked supports can be
identified on one cuspidal twist line with integer intervals `[a,b]` and `[c,d]`.
Noncontainment forces the two endpoints to have the same strict order. If `Δ`
precedes `Γ`, then `a < c` and `b < d`, so their means are strictly increasing.
If they are linked and `Δ` does not precede `Γ`, the reverse orientation holds,
giving the reversed exponent inequality. The common base and interval coordinates
must be derived from linkage; they are not hypotheses of the proposition.

## Provenance and original sources

This exact two-clause interface, including arbitrary actual positive-form
witnesses, is internal and derived. The following registered originals motivate
its conventions and use; neither states this Lean interface verbatim.

- F. Rodier, *Representations de GL(n,k) ou k est un corps p-adique*,
  Seminaire Bourbaki, expose 587, Asterisque 92–93 (1982), pp.201–218.
  Literature ID `rodier-1982-gln`, SHA256
  `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
  Printed pp.210–212 (one-based PDF pp.11–13) were read. Proposition 9(ii)
  identifies the special quotient as essentially square-integrable; §4.1
  gives linkage and precedence; §4.3 gives the ordered special-head
  classification and the nonlinkage irreducibility criterion. These motivate
  reordering the special factors; their classification results are not proof
  inputs to this comparison.
- G. Henniart, *Une caracterisation de la correspondance de Langlands locale
  pour GL(n)*, Bull. Soc. Math. France 130 (2002), pp.587–602.
  Literature ID `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Sections 2.5–2.8, printed pp.594–596 (one-based PDF pp.8–10), were read.
  Section 2.5 fixes upper normalized induction; §2.6 fixes the increasing
  special quotient. The real unitary exponent and weakly decreasing order
  are in §2.8, p.596; §2.7 concerns extension of the correspondence.

No source-specific errata files for these IDs were present in the supplied
Library or shared notes. The published classification coverage and
[source-boundary note](../../../notes/henniart/gln-classification-sources.md)
were consulted. They retain the missing cuspidal dual in Henniart's displayed
§2.6 contragredient formula and the limitation of Rodier's Jacquet citation for
tempered exhaustion. Rodier's closing reference to Theorem 2 in §4.3 points in
context to Theorem 3. None of these disputed formulas or exhaustion claims is
used here.

## Future proof and independence

A proof must establish the scalar action of segment induction and its quotient,
obtain the needed scalar character for a supercuspidal representative, extract
the exponent from an arbitrary given positive form, and prove integral-twist
nonperiodicity and endpoint orientation for the support-based linkage relation.
The scalar calculation and interval argument above describe these obligations;
this file proves none of them. The published proposition
`SegmentConstituentCentralCharacter` records a related formula, but a proposition
definition alone supplies no proof. The same applies to centered
square-integrability statement targets.

Any lower-level exponent-uniqueness lemma must be used with its actual hypotheses.
For example, `exponent_eq_of_unitaryCentralCharacter` requires two actual unitary
central characters and a nonzero vector; `exponent_eq_of_isSquareIntegrable`
requires analytic square-integrability of both twists. Neither grants those
hypotheses merely from the existence of the present statement.

The proof successor must remain independent, directly and transitively, of the
ordered conversion, square-integrable exhaustion, regular exhaustion, full
square-integrable classification, tempered block uniqueness, multisegment
exhaustion, ordered-head existence, and quotient coverage tasks named in its
contract. Shared lower-level proofs may be reused only after checking this
independence. This interface provides no classification, exhaustion, analytic
normalization existence or factor-commutation theorem.
