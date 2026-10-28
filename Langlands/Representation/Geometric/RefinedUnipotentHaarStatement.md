# The Haar modulus of a refined product-Levi radical

Author: Worker 799.

This module states a proposition. It does not prove it. The Prop-valued
definition `Langlands.Geometric.PadicRefinedUnipotentHaarModulus.{uF}` says that
the actual Haar modulus of conjugation on the actual radical of a refined
parabolic, inside a product Levi `B.Levi F`, is the published explicit
character `T.refinedLeviModulus B S`. The refined induction and Jacquet functors
of `Geometric/RefinementFunctors` are normalized by this explicit character, so
the proposition states the missing identification with Bernstein and
Zelevinsky's module.

The module also proves one small topology helper, which the statement needs.

## Topology helper

`Langlands.PadicField.TopologicalData.refinedUnipotentLocallyCompactSpace T B S`
is a theorem. It says that, with the supplied topology `T.topology`, the actual
subgroup `Geometric.refinedUnipotent F.Carrier B S` is a locally compact space.
The proof transports local compactness through the published continuous
multiplicative equivalence `Geometric.refinedUnipotentRadicalEquiv B S F.Carrier`
of `Representation/Parabolic/UnipotentFiniteContainment`. That equivalence goes
to the finite product of the intrinsic block radicals
`(S i).unipotentRadical F.Carrier`. Each block radical is locally compact by
the published `T.unipotentRadicalLocallyCompactSpace (S i)`, and a finite
product of locally compact spaces is locally compact. The module neither
duplicates nor replaces the equivalence.

## Statement

The proposition quantifies over:

- every prime `p`, every p-adic field `F : PadicField.{uF} p` and every supplied
  realization `T : F.TopologicalData`, whose topology `T.topology` is used
  throughout;
- every rank `n`, every ordered block shape `B : GeneralLinear.BlockShape n`
  with blocks `n_1, …, n_r`, and every refinement `S : Geometric.BlockRefinement B`.
  Here `S i : BlockShape n_i` is an arbitrary ordered block shape of the `i`-th
  block. Rank zero, shapes with no blocks, and arbitrary refinements are
  included. There are no minimality, properness, admissibility or
  representation hypotheses.

Write `G = B.Levi F.Carrier`, the product of the groups `GL_{n_i}(F)` with the
product of their topologies from `T.topology`. The actual groups are:

- `U = Geometric.refinedUnipotent F.Carrier B S`, the subgroup of `G` whose
  `i`-th component lies in the strictly upper block unipotent subgroup of
  `S i` for every `i`. It carries the subspace topology from `G`.
- `M = Geometric.refinedLevi F.Carrier B S`, the subgroup of `G` whose `i`-th
  component lies in the block-diagonal Levi subgroup of `S i` for every `i`.
- `Geometric.refinedLeviNormalizer F.Carrier B S : M →* normalizer U`, the
  published homomorphism that regards `m` as an element of the normalizer of
  `U` in `G`. It does not change the underlying element.

For `m : M`, write `a_m = HaarModulus.normalizerConj U
(Geometric.refinedLeviNormalizer F.Carrier B S m)`. This is the published
continuous conjugation automorphism of `U`, with ambient value
`a_m(u) = m * u * m⁻¹`, computed componentwise in `G`.

The definition installs exactly three instances: `T.topology`,
`T.leviTopologicalGroup B` (`G` is a topological group) and
`T.refinedUnipotentLocallyCompactSpace B S` (the helper above). It then asserts
a conjunction of two parts.

1. **Measure law.** For every `m : M`, every measurable structure on `U` that
   is its Borel σ-algebra (`MeasurableSpace U` with `BorelSpace U`), and every
   measure `μ` on `U` with `μ.IsHaarMeasure`,

   `μ.map a_m = ((T.refinedLeviModulus B S m : ℝ≥0)⁻¹) • μ`.

   The scalar is a positive real number. It acts on measures through `ℝ≥0`.
   No regularity, normalization or product form of `μ` is assumed.

2. **Character equality.** As homomorphisms `M →* ℝ≥0ˣ`,

   `(HaarModulus.normalizerCharacter U).comp
     (Geometric.refinedLeviNormalizer F.Carrier B S) = T.refinedLeviModulus B S`.

   This is the published actual character, with no new surrogate. Its
   definition in `Group/HaarModulus` uses Mathlib's `mulEquivHaarChar` with the
   canonical Borel structure `borel U`. The arbitrary Borel structures of part 1
   are bound only inside part 1, so they do not affect part 2.

The explicit character is the published

`T.refinedLeviModulus B S m = ∏_i T.leviModulus (S i) (refinedLeviBlock B S i m)`

(`PadicField.TopologicalData.refinedLeviModulus_apply`). Here
`refinedLeviBlock B S i m`, short for
`PadicField.TopologicalData.refinedLeviBlock B S i m`, is the tuple `(m_{i,1}, …, m_{i,s_i})` of diagonal
blocks of the `i`-th component of `m`, and the blocks of `S i` have sizes
`k_{i,1}, …, k_{i,s_i}`. By `Group/GL/BlockModulus`,

`T.leviModulus (S i) (m_{i,1}, …, m_{i,s_i}) =
  ∏_{j<l} |det m_{i,j}|^(k_{i,l}) / |det m_{i,l}|^(k_{i,j})`,

with the residue-normalized absolute value. If `B` has no blocks, or every
`S i` has one block, the product is empty and the character is `1`.

There are no hypotheses of Haar scaling, Jacobian, product decomposition,
conjugation intertwining or Haar uniqueness. Local compactness enters only
through the proved helper. The field universe `uF` is the only universe.

## Direction

The published convention, `HaarModulus.normalizerCharacter_smul_map`, says this.
For a regular Borel Haar measure `μ` on `U`, write `c` for the value in `ℝ≥0` of
`normalizerCharacter U (refinedLeviNormalizer m)`. Then

`c • μ.map a_m = μ`.

So the pushforward scale in part 1 is `c⁻¹`, and part 2 says that `c` itself is
the explicit `T.refinedLeviModulus B S m`. For a regular Borel Haar measure,
part 2 implies part 1. Part 1 is stated for every Borel Haar measure, with no
regularity hypothesis. Any regularity that a later proof uses must be proved
from the p-adic topology.

## Conventions and source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. The page cited for
each section is the printed page; the PDF page is the printed page minus 439.

- **Section 1.7, printed page 444.** For an automorphism `σ` of an l-group `U`,
  the module is defined by `∫_U f(σ⁻¹(u)) dμ(u) = mod_U σ · ∫_U f(u) dμ(u)`,
  where `μ` is a Haar measure. If `g` normalizes a closed subgroup `U`,
  `mod_U(g)` is the module of `u ↦ g u g⁻¹`. The left side integrates `f`
  against the image of `μ` under `σ⁻¹`. So `(σ⁻¹)_* μ = mod_U(σ) μ`,
  equivalently `σ_* μ = mod_U(σ)⁻¹ μ`. With `σ = a_m`, part 1 says
  `mod_U(m) = T.refinedLeviModulus B S m` in image-measure form. Part 2 says
  the same thing for the Library's packaged character.
- **Sections 2.1–2.2, printed page 446.** A parabolic triple `(P, M, U)` has
  the Levi decomposition `P = MU`. For `GL(n, F)` the standard subgroups
  correspond to ordered partitions `α = (n_1, …, n_r)`, with
  `G_α = G_{n_1} × … × G_{n_r}` embedded block-diagonally. `G_β < G_α` holds
  exactly when `β` is a subpartition of `α`. A refinement `S` of `B` is such a
  subpartition. The Library's refined parabolic, refined Levi and refined
  radical in `B.Levi F` form the corresponding parabolic triple in the product
  Levi, built block by block.
- **Section 6.3, printed page 468.** The source shows that the intersections
  `(M ∩ w⁻¹(Q), M ∩ w⁻¹(N), M ∩ w⁻¹(V))` form a parabolic triple in `M`. This
  is the downstream reason for the identification. The present proposition
  concerns every refinement, whether or not it arises from an intersection, and
  identifies no intersection.

There is no project errata note for this source. Its footnote on printed page
467 concerns section 6.1 only.

Registered source: `bernstein-zelevinsky-1977-induced-i`,
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

## Provenance

This is an internal derived proposition, not a named theorem of the source. It
is the finite-product consequence of the standard block Haar law, read with the
BZ77 section 1.7 convention. The block law is the published
`Langlands.glBlockModulusHaar` of `Group/GL/BlockModulusHaarProof`. It states,
for each intrinsic block radical, `μ.map (B.leviAction F.Carrier m) =
(T.leviModulus B m)⁻¹ • μ` for every Borel Haar measure.

A later proof is expected to use the following inputs, none of which is
assumed here:

- the published equivalence `refinedUnipotentRadicalEquiv B S F.Carrier`;
- a coordinate check that it intertwines `a_m` with the product of the block
  actions `(S i).leviAction F.Carrier (refinedLeviBlock B S i m)`;
- `glBlockModulusHaar` for each block;
- `HarmonicAnalysis.pi_nnreal_smul` to multiply the finite product scaling
  factors;
- product Haar invariance and Haar uniqueness, to pass to an arbitrary Haar
  measure on `U`;
- `normalizerCharacter_smul_map`, to obtain part 2.

## Not claimed

No proof of the proposition is supplied. No Haar measure on `U` is constructed,
and no product decomposition of a Haar measure is asserted. Nothing is said
about intersection subgroups, quotient integrals, or the geometric lemma's
natural comparison. Those are separate obligations.
