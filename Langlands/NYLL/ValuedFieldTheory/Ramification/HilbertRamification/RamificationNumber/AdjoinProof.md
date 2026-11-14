# NYLL M312.003: displacement bounds on an adjoined algebra

The theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin`
proves the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoinStatement`.
Its declared type is exactly that proposition, at four independent universe
levels `u`, `v`, `w`, `x`.

For fields `K : Type u` and `L : Type w` with an `Algebra K L`, the base and
target discrete valuation fields have value-group universes `v` and `x`.
The supplied `base.valuation.HasExtension target.valuation` instance and
`HasUniqueValuationExtension.{u,v,w,x,x} base target` allow a field
automorphism `sigma : Gal(L/K)` to restrict to an automorphism `e` of the
target valuation ring. If `e a - a` belongs to `target.maximalIdeal ^ n`,
the theorem gives the same bound for every `z` in
`Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring)`.
The exact implicit binders, order, and hypotheses are those of the imported
target.

## Implemented proof

After introducing the closed proposition's parameters, the proof names the
published ring automorphism `e` and applies Mathlib's
`Algebra.adjoin_induction` to the supplied membership of `z`.

- Singleton membership reduces to the assumed generator bound.
- For a base scalar `r`, subtype extensionality and
  `sigma.commutes (r : K)` show that `e` fixes its image in the target
  valuation ring. Its displacement is zero, which belongs to the ideal power.
- For addition, `map_add` and ring normalization express displacement as
  `(e y - y) + (e z - z)`. Ideal closure under addition gives the bound.
- For multiplication, `map_mul` and ring normalization establish
  `e (y * z) - y * z = e y * (e z - z) + (e y - y) * z`.
  The induction hypotheses, multiplication on either side by ring elements,
  and ideal addition give the bound.

The proof uses the actual restricted field automorphism and the canonical
valuation-extension algebra. It adds no monogeneity, finite-dimensionality,
`IsGalois`, or residue-separability hypothesis. It applies to every natural
exponent, including zero.

## Source, adaptation, and authorship

The source is Naganori Yamaguchi's *ClassFieldTheory*, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationNumber.lean`,
M312.003, lines 137–159, with section parameters at lines 25–34. The
whole-file SHA-256 is
`87fdb1882eaeab05ba3a7449fd7e48ce8ddf7b710a0e6ef4b25521780cb257a3`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum filename was found in the Library errata directory.

The source proves containment of the singleton adjoin in the displacement
subalgebra defined in M312.001, using its closure calculations. Worker 313
adapted those calculations into the direct adjoin induction above in the
unreviewed draft for Task 5884, revision 2
`de5a7a076f7cad6032e69124b09041e5081765d3e68dd2f8b07ca9d654e78ff3`.
Worker 287 reuses that Lean proof body unchanged and expands this documentation
for Task 6186. Worker 313 is a coauthor of this contribution.

The namespace is prefixed with `Langlands.NYLL`, and the theorem's type uses
the published closed proposition instead of repeating the source telescope.
The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber.AdjoinStatement`;
it supplies the published M304.014 valuation-ring automorphism and
`Mathlib.RingTheory.Adjoin.Basic`. This proof does not import or require the
M312.001 displacement-subalgebra definition or the M312.002 membership lemma.
The published target and its imports are unchanged.

The original copyright and author header is retained, with modification
notices. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The target environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
