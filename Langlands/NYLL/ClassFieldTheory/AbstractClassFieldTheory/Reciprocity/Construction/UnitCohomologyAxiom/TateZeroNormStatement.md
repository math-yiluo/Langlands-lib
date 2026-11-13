# NYLL M032.017: fixed vectors are norms when Tate `H⁰` vanishes

The paired Lean file gives the Prop-valued target
`Langlands.NYLL.ClassFormation.exists_norm_eq_of_tateHZero_isZeroStatement`
for the source theorem `ClassFormation.exists_norm_eq_of_tateHZero_isZero`.
The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`,
inventory unit M032.017. The theorem occupies lines 173–192: the docstring
is at 173–174, the signature at 175–179 and the proof at 180–192. The
section context is at lines 18–30: `namespace ClassFormation`, the opens
`KummerTheory` and `CyclicCohomology`, `noncomputable section`,
`open CategoryTheory` and `universe u`. The `variable` lines 105–107 bind
`G`, `D` and `A`, but the theorem does not use them, so Lean does not add
them to its telescope. The file SHA-256 is
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`.
The registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## The statement

The parameters are, in the source order and with the source binder kinds:

- implicit `Q : IntegralRepGroupType`, where `IntegralRepGroupType` is the
  Library's `Langlands.NYLL.IntegralRepGroupType` (M002.001, the alias
  `Type 0`). The acting group therefore stays in universe zero, as in the
  source;
- instance arguments `[Group Q]` and `[Fintype Q]`;
- explicit `M : Rep ℤ Q`, an integral representation of `Q`;
- explicit `g : Q`;
- explicit `_hg : ∀ x, x ∈ Subgroup.zpowers g`, saying that `g` generates
  `Q` (source name `hg`);
- explicit `_hzero : Limits.IsZero (tateCohomology M 0)`, saying that
  Mathlib's Tate cohomology object of `M` in degree zero is a zero object of
  its category (source name `hzero`).

The body, which is the source conclusion verbatim, says: for every
`x : M.V` with `M.ρ g x = x` there is `y : M.V` with `M.norm.hom y = x`.
Here `M.ρ` is the representation's action, and `M.norm` is Mathlib's norm
endomorphism `Rep.norm`, the sum of the action over all elements of `Q`.
So the statement says that an element fixed by the generator, and hence by
all of `Q`, is an actual norm. It is the elementwise form of the vanishing
of `Ĥ⁰(Q, M) = M^Q / N(M)`. The objects are Mathlib's actual
representation, norm and Tate cohomology; no separate kernel, image or
cyclicity premise is added.

## Modifications

Worker 5424 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to the name. The `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The argument names `hg` and `hzero` gain leading underscores because the
  body does not refer to these proofs. Both parameters keep their position
  and full types, so a proof of the target takes them in the source order.
- The proof (lines 180–192) is not ported. Proving the target is a separate
  `lean.proof@1` task. The source proof uses the M003 comparison
  `TateCohomology.isoFiniteCyclicZero`, which the Library has as
  `Langlands.NYLL.TateCohomology.isoFiniteCyclicZero`.
- The unused `universe u`, the unused opens `KummerTheory` and
  `CyclicCohomology`, the `noncomputable section` and the other
  declarations of the module are omitted. `open CategoryTheory` is kept, so
  `Limits.IsZero` is written as in the source.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.TateComparison`. They are replaced by
  the focused imports
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic` (for `Rep`,
  `Rep.norm` and `tateCohomology`) and
  `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` (for
  `IntegralRepGroupType`).

A focused `lean_check` of this module, with the declaration inspected,
reports no errors or warnings, `statement_returns_prop: true` and no
universe level parameters. No earlier M032 declaration and no
`FiniteAbstractField` data are needed to state this target.

## Scope

This unit states M032.017 and does not prove it. The other M032 units (the
finite cyclic and unramified cyclic subextension data, their instances and
the fixed representation) are separate units of the same task. No host
reciprocity, class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
