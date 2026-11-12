# Finite arithmetic maximality and exhaustion of the separable inertia fixed field

Lean and statement translation: Worker 60. Target design and original-source
map: Worker 118.

This is a statement unit. It defines propositions and proves none of the
arithmetic assertions below. It imports the published construction
`Langlands.Galois.Local.SeparableInertiaDefinitions`; it does not reconstruct its
field, valuation, integer rings, residue maps or topology.

## Objects, instances and scope

All declarations are in `Langlands.LocalGalois.Separable`, with one arbitrary
universe `u`. The base field is `F : Type u` with exactly
`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`.
The ambient extension is literally `Ω = SeparableClosure F`, and
`U = inertiaFixedField F` is the published intermediate field fixed by the
kernel of the actual residue action of `Gal(Ω/F)`. The base valuation relation
and topology are the supplied ones.

The four file-local instances `localNormedField F`,
`localNormedField_ultrametric F`, `localNormedField_complete F` and
`localResidue_finite F` are the same published choices used in the construction.
They introduce no further hypotheses on `F`. In particular, the chosen
rank-one norm need not have a prescribed numerical normalization.

Write `A = baseIntegers F` for its closed unit ball. For an actual intermediate
field `E : IntermediateField F Ω`, write `B_E = extensionIntegers F E` for the
integer ring of `spectralValuation F E`. Both are valuation subrings, equipped
with their actual local-ring structures. The integer map `A →+* B_E` is
`algebraMap A B_E` from the published spectral `Valuation.HasExtension`
instance. The residue algebra used in `Algebra.IsSeparable` is the canonical
`ResidueField A`-algebra on `ResidueField B_E`: its structure map sends the
residue of `a` to the residue of its image in `B_E`.
Mathlib's `Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`
expresses this compatibility. No residue algebra is supplied as additional
data.

## Exact propositions

`ArithmeticUnramified F E` is the conjunction

1. `Ideal.map (algebraMap A B_E) (maximalIdeal A) = maximalIdeal B_E`;
2. `Algebra.IsSeparable (ResidueField A) (ResidueField B_E)` for the canonical
   residue algebra just described.

The predicate is defined for every intermediate field, so it can be reused
without passing a finiteness instance. The maximality theorem only applies it
to finite-dimensional intermediate fields. It mentions neither inertia nor
`U`, and contains no arithmetic conclusion about `U`.
For a finite extension of a complete discretely valued field, its first
clause says that the ramification index is one; the second is the usual residue
separability requirement. In the present local-field setting the base residue
field is finite and perfect, but the separability clause is retained explicitly.
No equivalence with Mathlib's separate predicate `Algebra.Unramified` is claimed.

`FiniteUnramifiedMaximality F` states that for every actual intermediate field
`E` with `[FiniteDimensional F E]`,
`E ≤ inertiaFixedField F ↔ ArithmeticUnramified F E`.
The forward implication asserts unramifiedness of every finite subextension
of `U/F`; the reverse asserts that every finite arithmetically unramified
subextension of `Ω/F` belongs to `U`.

`FiniteUnramifiedGaloisExhaustion F` quantifies every
`s : Finset (inertiaFixedField F)`, including the empty set, and asserts
the existence of an `E : IntermediateField F Ω` that is finite-dimensional
and Galois over `F`, is contained in `U`, satisfies
`ArithmeticUnramified F E`, and contains `fixedFieldToSepClosure F x` for
every `x ∈ s`. This is the published actual inclusion `U →ₐ[F] Ω`.
The finite field is an intermediate field of this same `Ω`, rather than an
arbitrary field carrier with a hypothesized isomorphism. Finiteness, the Galois
property and arithmetic unramifiedness are existential conclusions.

`SeparableUnramifiedStatement.{u} : Prop` is a closed target: it universally
quantifies the base field and the four supplied structures above, and conjoins
`FiniteUnramifiedMaximality F` and `FiniteUnramifiedGaloisExhaustion F`.
It supplies no desired conclusion as a hypothesis or package field.

There is no `CharZero F` or `PerfectField F` restriction. This includes mixed
characteristic and equal characteristic, even when `F` itself is imperfect.
In the latter case a full algebraic closure has purely inseparable elements;
retaining the actual separable closure is part of the target. This unit asserts
no completeness or local compactness of `U`, and no torus norm or Iwahori result.

## Original sources and correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979. Registered source `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Chapter III §5, Theorem 1 and its proof, printed p. 53/PDF p. 60, identify
  the finite complete-DVR unramified criterion as `B/pB` being a field
  separable over the base residue field. Since `B` is a DVR, the first
  condition is exactly equality of `pB` with its maximal ideal. This is the
  arithmetic definition above.
- Chapter III §5, Theorems 2–3 and Corollary 1, printed pp. 54–55/PDF
  pp. 61–62, give the finite unramified/residue correspondence and the
  direct-limit maximal unramified extension with separably closed residue.
  Over the finite residue field here every finite residue extension is Galois.
  Taking a common finite residue extension for finitely many elements gives
  the finite Galois exhaustion formulation.
- Chapter I §7, Propositions 20–22, printed pp. 21–22/PDF pp. 29–30,
  identify the inertia kernel and its finite fixed field, and describe
  compatibility under intermediate fields. Chapter IV §1, Proposition 1 and
  the corollary after Proposition 2, printed pp. 62–63/PDF pp. 69–70, identify
  its fixed field with the largest unramified subextension.
- Chapter II §2, Proposition 3 and Corollaries 1–3, printed pp. 28–29/PDF
  pp. 36–37, provide discrete valuation, completeness, degree and uniqueness
  for finite extensions. They justify the finite complete-DVR setting of the
  arithmetic criterion and its compatibility with the spectral valuation.

The passage from these finite results to the inertia kernel on `Ω` and its
finite-set exhaustion is a derived formulation of the direct-limit result,
using the published actual objects. Serre does not define the Lean spectral
maps or these proposition names.

Read with Serre, *Corrections to J-P. Serre's books* (2019), registered source
`serre-book-corrections-2019`, retained file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA-256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
PDF pp. 2–3. No entry changes the cited conclusions. The printed p. 63
corrections concern Proposition 3, outside the inertia corollary used here.

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§2.5(c), printed p. 88/PDF p. 119, fixes the maximal unramified extension
inside a separable closure. That is the intended arithmetic interpretation of
`U` in these targets. Their general discretely valued Henselian setup is
broader than the local fields treated here. Lemma 2.5.12 and Definition
2.5.13, printed pp. 89–90/PDF pp. 120–121, motivate later consumers and are
not asserted in this file.

Read with the authors' corrections of 1 November 2024, registered source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 24–25. The §2.5 corrections do not change its maximal-unramified
setup. Both retained files are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
The cited originals and corrections were read for this translation.

## Dependency and status boundary

The sole direct project import is
`Langlands.Galois.Local.SeparableInertiaDefinitions`. Its existing construction
and short comparison proofs are reused unchanged. The new declarations are
unproved arithmetic targets. Residue algebraic closure, value-group, discrete valuation ring and Henselian
conclusions are separate arithmetic targets, outside this unit. Subsequent
proof tasks must discharge the published propositions.

The four local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
