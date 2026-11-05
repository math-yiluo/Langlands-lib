# Admissibility of the actual normalized Jacquet module

Author: Worker 15. Module
`Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement`.
The declaration
`Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement`
is a Prop-valued definition stating preservation of admissibility. This module
does not prove the proposition.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.6.1 Corollary, printed pp.176–177 /
PDF pp.182–183. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The normalization is VI.1.2, equation (VI.1.2.2), printed p.135 / PDF p.141,
with the modular-function convention remark on printed p.136 / PDF p.142.

## Quantifiers and hypotheses

The field is any `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k] [T2Space k]`. The ambient group scheme is any
`G : GroupScheme (Spec (CommRingCat.of k))` with
`hG : IsConnectedReductive G`. The statement installs `hG.isAffineHom` and
`RationalPointFamily.pointTopology` as the canonical topology of
`rationalPoints G`. It then quantifies
`[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` for that topology, exactly as the
published `ArbitraryParabolicExponentStatement` does.

For every triple of group schemes `P, M, U` over the same field, the data are
`p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, together with
`hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`,
`hr : LeviSubgroup.IsGeometricUnipotentRadical r`, and
`hmul : IsIso (subgroupMultiplication l r)`. The radical and the multiplication
isomorphism refer to these same maps `l, r`; the existential radical in `hl`
does not replace `r`. The statement quantifies every such datum and makes no
claim that these data have been constructed for every parabolic.

For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, the entire
representation-theoretic implication is

```lean
π.IsAdmissible →
  ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible
```

The explicit functor argument order is `hp hr hl hmul`. The field universe `u`
and carrier universe `v` are independent. Admissibility uses the existing
`SmoothRep.IsAdmissible`: smoothness and finite-dimensional fixed vectors for
every open subgroup. The source and target are already smooth objects.
There is no characteristic-zero, split-group, general-linear-group or
standard-parabolic restriction. No split component is required.

## Actual quotient, normalization and topology

The imported
[`ArbitraryParabolic`](ArbitraryParabolic.md) construction defines `pointImage j`
as `(rationalPoints.map j).range`. Thus the radical is literally
`pointImage (r ≫ p)` and the Levi group is literally `pointImage (l ≫ p)` in
`G(k)`. Both have the subgroup topology induced from the single canonical
ambient topology. No separately chosen topology on a model of the Levi is
substituted.

`jacquetFunctor p l r hp hr hl hmul` is the existing abbreviation for
`normalizedJacquetFunctor` on these two point images. Radical closedness is
derived from `hp` and `hr`, and Levi normalization from the actual radical's
normality. The underlying module is the actual coinvariant quotient by the
span of `π(n)v - v`; its Levi action is the descended action twisted by
`HaarModulus.closedInverseHalfCharacter` of this closed radical. The
construction and smoothness are imported, not asserted by a new certificate.

For an actual Levi point `m`, its action on a coinvariant class is
`[v] ↦ δ(m)^(-1/2)[π(m)v]`, with `δ` the Library's Haar modulus of conjugation
on the radical. Renard writes `π_N ⊗ δ_P^(1/2)` in (VI.1.2.2).
His following remark explains that his modular-function convention is inverse
to the usual convention. The imported construction uses the inverse half
Haar modulus with the orientation documented in `ArbitraryParabolic` and
[`Parabolic`](../Aubert/General/Parabolic.md); this statement uses that existing
normalized functor unchanged.

## Source correspondence and remaining proof obligation

The VI.6.1 Corollary asserts that for any parabolic `P = MN` and any smooth
admissible representation of `G`, both the unnormalized Jacquet representation
`(π_N, V_N)` of `M` and the normalized `r_P^G(π, V)` are admissible. The
declaration here records precisely the normalized assertion for every
represented parabolic in the displayed canonical-topology scope. Its
point-image packaging and universe parameters follow the existing Library
interface. It has no unnormalized clause.

Renard's proof on printed p.177 / PDF p.183 uses the preceding weak Jacquet
theorem and the existence of a compact open identity-neighborhood basis
admitting Iwahori decompositions along `P`. The existing generic proof
`Langlands.Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction`
retains `Jacquet.HasIwahoriContractionBasis` as a hypothesis. A proof of the
present statement must discharge the actual structural inputs for every
displayed parabolic; the [Chapter V source ledger](../../../notes/renard/chapter-v-structural-inputs.md)
records the relevant S20–S23 boundary. Neither that conditional proof nor the
publication of this proposition supplies the missing structural realization.

The only hypothesis on the representation is source admissibility. No
contraction basis, simultaneous basis, finite length, finite generation or
target admissibility is a premise. No proof of admissibility preservation,
characteristic-space decomposition, finite exponent support or canonical
Jacquet section is supplied here. Those results and their structural
construction and comparison obligations remain separate.
