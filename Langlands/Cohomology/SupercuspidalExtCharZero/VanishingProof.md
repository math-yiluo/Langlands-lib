# Higher Ext vanishing from compact induction

Authors: Worker 1595 (Lean proof and exposition), Worker 1570 (original-source
and subgroup-hypothesis checks).

The theorem
`Langlands.Cohomology.SupercuspidalExtCharZero.compactInductionSupercuspidalExtVanishing`
proves the published
`Langlands.Cohomology.SupercuspidalExtCharZero.CompactInductionSupercuspidalExtVanishingStatement`,
unchanged, with `k`, `G`, and `μ` explicit. It imports the published theorem
`compactCoefficientInjectiveProjective` from
`Langlands.Cohomology.SupercuspidalExtCharZero.InjectiveProjectiveProof`.

The universe `u` is arbitrary. The coefficient field `k : Type u` has
characteristic zero. The group `G : Type u` is Hausdorff, locally compact,
totally disconnected and sigma compact, with its Borel measurable structure
and a regular left Haar measure `μ` which is also right invariant. All smooth
representations have the common universe `SmoothRep.{u,u,u} k G`.
The finite indexing type in the target is `ι : Type`, with `[Finite ι]`.
The restricted finite decomposition is a hypothesis of the target.

For an open subgroup `H`, the five `openSubgroup_*` lemmas prove local
compactness, sigma compactness, and that `μ.comap H.subtype` is a regular,
right-invariant Haar measure. Local compactness follows from openness.
An open subgroup is closed, so sigma compactness follows from the closed
embedding into `G`. The inclusion is an open embedding. Mathlib's
`Measure.IsHaarMeasure.comap`, `Measure.Regular.comap'`, and
`Measure.IsMulRightInvariant.comap` supply the measure assertions.
The subspace instances supply Hausdorffness, total disconnectedness, the
topological group structure, and the Borel measurable structure.

`compactInductionSupercuspidalExtVanishing_of_openSubgroup` assumes the
injective-projective statement on each such subgroup with exactly these
instances and measure. For the finite family `σ` in the unchanged target,
each `σ i` is injective by the injectivity part of that premise. The local
finite-biproduct instance is `Abelian.hasFiniteBiproducts`, as in the target,
and Mathlib proves the biproduct injective. Transport through the supplied
isomorphism makes the restriction of `π` injective. The published
`SupercuspidalExt.compactInductionExtReciprocity` identifies the desired
Ext object with Ext on `H` into that restriction.
`SmoothExt.isZero_ext_succ_of_injective` proves the latter object zero,
and `IsZero.of_iso` transports the conclusion. The projectivity part of the
premise is not used.

The final theorem `compactInductionSupercuspidalExtVanishing` applies this
conditional result. For each open subgroup it installs the five proved
instances and uses `compactCoefficientInjectiveProjective k H
(μ.comap H.subtype)` to discharge the premise. Thus no injectivity,
projectivity, admissibility, or vanishing assumption is added to the
published target.

This is a derived formal argument implementing step 6 of the statement
Markdown. The uses motivating the target are Harris 1999, equation (4.10.1),
printed p.311, where Ext is taken in smooth coefficient modules, and p.312,
where its higher-degree vanishing gives degeneration; and Harris 1997,
printed p.96, where restriction to the component stabilizer and compact
induction reciprocity precede injectivity and degeneration. The Lean
conclusion concerns Ext vanishing; it does not construct those geometric
representations or spectral sequences. The field-valued statement can be
applied to individual coefficient fields. Comparing it with the full product
coefficient algebra `L_ell` in Harris requires a separate argument.

Registered originals read for this draft:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  Michael Harris, *Galois properties of cohomological automorphic forms on
  GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), 299–318, pp.311–312 (PDF pp.13–14),
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1997-drinfeld-cohomology`,
  Michael Harris, *Supercuspidal representations in the cohomology of
  Drinfel'd upper half spaces; elaboration of Carayol's program*,
  Invent. Math. 129 (1997), 75–119, pp.95–96 (PDF pp.21–22),
  SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1998-local-langlands`,
  Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p*, Invent. Math. 134 (1998), 177–210, Erratum to [H1],
  pp.180–182 (PDF pp.4–6),
  SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

The formulas at the cited 1999 pages and at 1997 p.96 were checked visually.
The 1998 erratum was read, with visual checks of pp.181–182. It corrects the
Shimura datum, conjugate place, twisting character, and outer contragredient
in the Galois parameter. These changes concern the later normalization
calculation of Harris 1997 and do not enter the categorical Ext argument
implemented here.
