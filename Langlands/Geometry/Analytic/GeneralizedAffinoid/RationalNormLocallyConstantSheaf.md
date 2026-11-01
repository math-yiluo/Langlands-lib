# Continuous-action-valued locally constant sheaves on weighted rational sites

## Geometric inputs and original functions

Fix an ultrametric normed field `K`, an actual `PresentedAffinoidAlgebra K`,
a topological group `G`, and a homomorphism `ρ` into the bounded algebra
automorphisms of the affinoid algebra. Assume every forward algebra orbit
`g ↦ (ρ g).hom.toAlgHom a` is continuous. The field, group and coefficient
set have independent universes. For an open subgroup `H`, use the existing
`NormInvariantChart ρ hρ H`: its objects are the original positive-radius
rational quotient presentations whose actual loci are `H`-invariant, and its
arrows are all original bounded restrictions over the fixed base algebra.
Use its already constructed finite rational Grothendieck topology.

The imported `normInvariantLocusLocallyConstantPresheaf` consists of every
locally constant function from each original locus subspace to an arbitrary
coefficient set `C`. Its `DiscreteLocallyConstant` wrapper equips this entire
function set with the discrete topology. The action is inverse precomposition
by the existing jointly continuous locus action. The imported compact-action
construction proves that this discrete function action is jointly continuous;
continuity is not an additional input. The spectrum presheaf analogously uses
every original quotient spectrum, its actual topology, its existing continuous
action and the original bounded restriction maps. There is no topology, action,
nonemptiness hypothesis or chosen default value on `C`.

`normInvariantLocusLocallyConstantForgetIso` removes the discrete wrapper and
forgets the action, identifying the underlying set-valued presheaf with the
ordinary locus presheaf precomposed with the original invariant-chart inclusion.
Its component maps are `toLocallyConstant` and `DiscreteLocallyConstant.mk`.
`normInvariantSpectrumLocallyConstantForgetIso` does the same on the original
quotient spectra. `normInvariantLocallyConstantPresheafIso_forget` identifies
the forgotten comparison with the original ordinary spectrum-locus comparison.
Both directions retain pullback by the original rational homeomorphism and
its inverse. The locus forgetful comparison needs no completeness hypothesis;
the spectrum construction and the sheaf arguments below assume `CompleteSpace K`.

## Categorical sheaf construction

First, `normInvariantLocusLocallyConstantForget_isSheaf` uses the proved
continuity of the actual invariant-chart inclusion and the already constructed
ordinary locally constant sheaf. Transport through the preceding forgetful
isomorphism proves that the full underlying function presheaf is a sheaf.

The helper `normInvariantDiscretePresheaf_isSheaf` applies more generally to
any presheaf `F` of continuous `H`-actions on topological spaces on this actual
finite invariant site, provided every `F(d)` has discrete topology and the
underlying set-valued presheaf is a sheaf. It proves Mathlib's full categorical
sheaf condition: for every test continuous action `E`, the presheaf of
continuous equivariant maps from `E` into `F` has unique amalgamation. The test
space `E` is arbitrary and is not assumed discrete or compact.

For a covering sieve `S` and a compatible family of maps from `E` to its
section spaces, evaluate at each point `x` of `E`. The underlying set-valued
sheaf uniquely glues this pointwise compatible family to a section `q(x)`.
The sheaf's recovery equation holds for every member of the entire sieve.
Extract a finite covering family `f_i : D_i ⟶ d` inside `S` and consider

`r : F(d) → ∏ i, F(D_i)`, sending a section to all its restrictions.

The generated sieve of this family is covering. Its separatedness, transferred
to the generating presieve by `Presieve.isSeparatedFor_iff_generate`, proves
that `r` is injective. Since the family is finite, both its product of discrete
section spaces and `F(d)` are discrete. Thus `r` is a closed embedding, using
continuity from a discrete domain and closedness of all subsets of the discrete
codomain. The recovery equations identify `r ∘ q` with the tuple of supplied
continuous local maps. Continuity of this tuple and the embedding criterion
prove continuity of `q` in the original topology of `E`.

To prove equivariance, restrict both sides of the desired equation along each
`f_i`. Equivariance of the presheaf's restriction maps and of the supplied local
maps, together with recovery, gives equality on every component; injectivity
of `r` gives equality in `F(d)`. The same injectivity proves uniqueness of the
glued continuous equivariant map. This argument proves the categorical sheaf
condition directly, including continuity of the amalgamation.

Applying the helper with the actual discrete locus function spaces gives
`normInvariantLocusLocallyConstantPresheaf_isSheaf`. Transport through the
already constructed natural continuous equivariant rational spectrum-locus
isomorphism gives `normInvariantSpectrumLocallyConstantPresheaf_isSheaf`.
The definitions `normInvariantLocusLocallyConstantSheaf` and
`normInvariantSpectrumLocallyConstantSheaf` package exactly these original
presheaves as Mathlib sheaves with coefficients in `ContAction TopCat H`.
`normInvariantLocallyConstantSheafIso` lifts the original natural comparison
with both its original component maps unchanged.

Empty finite covering families are allowed. In that case the restriction map
has empty product as codomain, and separatedness still proves its injectivity.
The argument requires no inhabited index type, nonempty locus, nonempty
coefficient set, or nonzero quotient algebra.

## Subgroup and comparison coherence

For open subgroups `H ≤ J`, the actual chart inclusion goes from `J`-invariant
to `H`-invariant charts. The existing continuous-site sheaf functor consequently
precomposes sheaves from the `H`-invariant site to the `J`-invariant site. The
continuous acting-group restriction functor goes from `J`-actions to `H`-actions
along `openSubgroupInclusion h` with the original subgroup topologies.

`normInvariantLocusLocallyConstantPresheaf_subgroup` and its spectrum counterpart
prove that these two operations give exactly the same presheaves: precomposing
the `H` function presheaf by chart inclusion equals postcomposing the `J`
function presheaf by continuous action restriction. No function, bounded
restriction or underlying topology is replaced. The locus identity needs no
completeness assumption. `normInvariantLocallyConstantPresheafIso_subgroup`
proves equality of the natural comparison isomorphisms obtained by the two
routes, retaining the original homeomorphism and its inverse.

The two `normInvariant...LocallyConstantRestrictedSheaf` definitions package
the original `J` presheaves with action restricted to `H`. Their sheafness is
proved using the actual chart-inclusion sheaf functor and the exact presheaf
identities. The theorems `normInvariantLocusLocallyConstantSheaf_subgroup` and
`normInvariantSpectrumLocallyConstantSheaf_subgroup` give the corresponding
equalities of sheaf objects. Finally,
`normInvariantLocallyConstantRestrictedSheafIso` retains the group-restricted
original comparison, and `normInvariantLocallyConstantSheafIso_subgroup`
identifies it with the image of the `H` sheaf comparison under the chart-site
sheaf functor. These equalities follow from the definitions, with proof
irrelevance accounting for the sheaf-property fields.

## Provenance and scope

This is an internal construction by Worker 56 from the existing weighted
rational charts, ordinary locally constant sheaf, continuous compact-action
function presheaves, and invariant-site functoriality. The finite-cover
continuous gluing argument above is implemented in this file. Mathlib supplies
the categorical sheaf definition, underlying-set sheaf amalgamation, separatedness
and embedding tools; the action-valued sheaf property itself is proved here.
The unchanged included invariant-site and restriction-site prerequisites retain
their attribution to Workers 56 and 36 and their separate independent reviews.

The inherited geometric conventions come from Berkovich, *Non-archimedean
analytic spaces* (Trieste lectures, 2009), printed/PDF p.9 Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), and p.10 Fact 2.2.3(i) and Definition 2.2.7:
represented affinoid domains, positive-radius rational quotient presentations,
intersections, spectrum-locus identification and domain embeddings. Registered
source `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The existing presentations retain explicit unit generation as a sufficient
condition for absence of common zeros, with no converse asserted.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript, section 1.1 printed/PDF pp.2-3 and section 1.2 p.3,
motivates continuous operators, continuous acting-group homomorphisms,
equivariant maps, geometric covering families and site/sheaf functoriality.
The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Neither source is claimed to state this internal finite-site categorical gluing
result or to identify its coefficient-action sheaves with the manuscript's
full equivariant etale or quasi-etale sheaf categories.

The construction retains arbitrary positive real radii, trivial valuations,
nilpotents, zero quotients and empty loci. Sheafness uses a complete ultrametric
base field. General analytic algebra sheafness, analytic atlases, the full
analytic automorphism topology and its comparison with the explicit norm-orbit
hypothesis, compact/distinguished-domain lifting, analytic etale/quasi-etale
sites and the Harris tower remain separate obligations. This is a progressive
local prerequisite and does not complete the host task.
