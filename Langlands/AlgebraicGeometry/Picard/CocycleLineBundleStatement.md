# Line bundles glued from unit cocycles

`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleStatement` (universe
parameter `u`, module
`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleStatement`) is a
Prop-valued statement target. This file supplies no proof.

## The proposition

Let `X : Scheme.{u}` be a scheme, `ι : Type u` an index type and
`T : ι → X.Opens` a family of opens with `⨆ i, T i = ⊤`, so the `T i` cover
`X`. Let `g i j` be units of `Γ(X, T i ⊓ T j)` for all `i j : ι`, and assume
the cocycle identity

`g i j * g j k = g i k` in `Γ(X, T i ⊓ T j ⊓ T k)`

for all `i j k`, where each factor is restricted along the evident inclusion
(`T i ⊓ T j ⊓ T k` into `T i ⊓ T j`, `T j ⊓ T k` and `T i ⊓ T k`
respectively). Then there is a line bundle `N : LineBundle X` such that the
following holds for every family `a i ∈ Γ(X, T i)`. If

`a i = g i j * a j` in `Γ(X, T i ⊓ T j)` for all `i j`

(with `a i` and `a j` restricted to `T i ⊓ T j`), then there is a global
section `t : GlobalSections N.obj` with

`T i ⊓ trivializationOpen N.obj t = X.basicOpen (a i)` for every `i`.

The quantifier order matters: one bundle `N`, chosen from `T` and `g` alone,
serves every compatible family `a`.

The Library objects are the following.

- `LineBundle X` (from `Langlands.AlgebraicGeometry.Picard.LineBundle`) is an
  actual sheaf of `O_X`-modules `N.obj` with the property
  `IsLocallyFreeRankOne`: each point has an open neighbourhood on which the
  restriction of `N.obj` is isomorphic to the structure sheaf.
- `GlobalSections N.obj` (from `Langlands.AlgebraicGeometry.Modules.SectionLocus`)
  is the module of sections of `N.obj` over `⊤`.
- `trivializationOpen N.obj t` is the supremum of all opens `U` on which the
  restriction of `sectionHom N.obj t : O_X → N.obj`, the morphism sending `1`
  to `t`, is an isomorphism (`TrivializesOn`). It is the whole maximal open on
  which `t` generates `N.obj`.
- `X.basicOpen (a i)` is Mathlib's basic open of `a i ∈ Γ(X, T i)`: the points
  `x ∈ T i` at which the germ of `a i` is a unit. It is contained in `T i`.

## Scope

The scheme, the index type in universe `u`, and the cover are arbitrary. The
`T i` need not be affine or nonempty, and the cover need not be finite. If `ι`
is empty then the cover hypothesis forces `X` to be empty. The units `g` are
subject only to the displayed triple-overlap identity. The identities
`g i i = 1` and `g i j * g j i = 1` are not assumed: taking `i = j = k` gives
`g i i * g i i = g i i`, hence `g i i = 1` because `g i i` is a unit, and then
`k = i` gives `g i j * g j i = g i i = 1`. Every compatible family `a` is
covered, including families of non-units and the zero family. No
quasi-compactness, separatedness or noetherianity hypothesis appears, and the
bundle and its sections are not given as structure data.

## Convention and intended meaning

The proposition fixes the following convention through its compatibility
condition. The intended witness `N` is the invertible module glued from `g`:
it has local generators `e i` of `N` over `T i` with

`e j = g i j * e i` on `T i ⊓ T j`.

These relations are consistent exactly because of the cocycle identity:
`e k = g j k * e j = g j k * g i j * e i` and `e k = g i k * e i` on the triple
overlap. A section equal to `a i * e i` on each `T i` satisfies
`a i * e i = a j * e j = a j * g i j * e i`, that is `a i = g i j * a j`; this
is the displayed compatibility condition. Conversely, a compatible family `a`
is the family of local expressions of one global section `t` of the glued
bundle. On `T i` the generator `e i` identifies `N` with `O_X`, and the
section morphism of `t` becomes multiplication by `a i`. That multiplication is
an isomorphism on an open `V ⊆ T i` exactly when `a i` restricts to a unit on
`V`, that is, when `V ⊆ X.basicOpen (a i)`. Hence the generation open of `t`
meets `T i` exactly in `X.basicOpen (a i)`.

The Lean proposition records only the existence of `N` and the generation-open
equality for each compatible family. It does not state that `N` is determined
by `g` up to isomorphism, it does not mention the local generators `e i`, and
it does not assert that `t` has local expressions `a i`. Those are the
intended construction, explained here to fix the meaning of the convention.

## Source correspondence

This is an internal, derived formulation. It is not stated in this form in the
source. The source is the registered Stacks Project snapshot
`stacks-norms-field-ample-descent-2026-10-26`, file `0BCX.html`, Section 31.18
(tag 0BCX):

- Proof of Lemma 31.18.2: the proof chooses generating sections `s_j` of an
  invertible module over the opens of a cover and writes `s_j = u_{jj'} s_{j'}`
  for units `u_{jj'}` on the overlaps. Their norms "satisfy the cocycle
  condition ... and therefore define an invertible `O_Y`-module". This
  proposition supplies that step: an actual line bundle glued from a unit
  cocycle on an arbitrary open cover.
- Proof of Lemma 31.18.3: "Define `Norm(φ)` to be multiplication by
  `Norm(f_j)` on `V_j`". The map is thus given by local expressions on the
  cover, and the lemma's final part locates where it vanishes. In the
  proposition, compatible families `a` play the role of these local
  expressions (for a section, that is a map from `O_Y`). The generation-open
  equality is the corresponding local computation of where the section
  generates.

The source indexes its transition units the other way round. Stacks writes
`s_j = u_{jj'} s_{j'}`, while here `e j = g i j * e i`. So the glued bundle of
this proposition corresponds, in Stacks' notation, to the cocycle
`u_{ij} = g j i` (which equals the inverse of `g i j`). Both conventions use
the same multiplicative cocycle identity. The convention here matches the
consumer's construction, which writes `s_j = c_ij s_i` and takes
`g i j = Norm(c_ij)`.

The source invokes "the correspondence between isomorphism classes of
invertible `O_X`-modules and elements of `H^1(X, O_X^*)`" of Cohomology,
Lemma 20.6.1 (registered snapshot
`stacks-first-cohomology-invertible-20-6-2026-10-28`, files `09NT.html` and
`09NU.html`, Section 20.6, Lemma 20.6.1 and its proof). That lemma is not
formalized here. Its proof uses the sheaf `L^*` of local generators, the
sections `s` over `U` such that `O_U → L_U`, `f ↦ f s`, is an isomorphism. In
that language, `trivializationOpen N.obj t` is the union of the opens `U` on
which `t` restricts to a section of `N^*`. Comments on 0BCX (#7175, #7312) and
on Section 20.6 and Lemma 20.6.1 (#5992, #5993, #8241, #8888) were checked;
none affects this formulation. Schemes have local stalks, as Lemma 20.6.1
requires.

## Use

The statement is the gluing interface needed by the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement`
(Stacks Proposition 31.18.9(1) via Lemmas 31.18.4 and 31.18.6). That proof
builds a norm line bundle on `X` from the norms of transition functions on a
finite cover and needs global sections whose generation opens can be computed
on each cover member. It does not involve norms or ampleness.

## Imports

The module imports the published
`Langlands.AlgebraicGeometry.Modules.SectionLocus` (for `GlobalSections` and
`trivializationOpen`) and `Langlands.AlgebraicGeometry.Picard.LineBundle` (for
`LineBundle`), unchanged.

## Authorship

The Lean statement and a first companion were drafted by Worker 770. Worker 303
revised the docstring and this companion.
