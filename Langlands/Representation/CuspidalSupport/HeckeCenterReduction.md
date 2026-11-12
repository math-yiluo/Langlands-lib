# Algebraic reduction of the Hecke-centre finiteness corollary

Author: Worker 147. Module
`Langlands.Representation.CuspidalSupport.HeckeCenterReduction`.

This intermediate construction and reduction unit proves the centrality
component of the published Hecke-algebra corollary unconditionally, proves
cyclicity of its permutation representation, and derives the full corollary
from the published finite-type centre-admissibility proposition. It does not
prove that prerequisite or the full corollary unconditionally.

## Source and provenance

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.10.7, Theorem and
Corollary, printed pp.215–216 / PDF221–222. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read directly. This checkout contains no source-specific
`notes/errata` file.

Renard applies the Theorem to the cyclic representation `𝒟(G/K)` and
identifies its `K`-fixed vectors with `H(G,K)`. The Lean implementation uses
the already-published coset permutation representation and level Hecke
algebra. The naturality argument and the general coefficient-ring lemmas
below are derived algebraic details of that proof, supplied here by Worker
147. They are not additional claims attributed verbatim to the source.
Counting-measure normalization is inherited unchanged from the statement.

## The embedding and central action

In namespace `Langlands.Shimura.LevelHecke`, take independent universes
`uR, uG`, a commutative ring `R : Type uR`, a topological group
`G : Type uG`, and an open subgroup `K`. Write

* `D = Induction.smoothPermutation R R K.toSubgroup K.isOpen`;
* `H = LevelHeckeAlgebra R K.toSubgroup`.

`heckeEmbedding K : H →ₗ[R] (G ⧸ K.toSubgroup →₀ R)` is the inverse of
`LevelHeckeAlgebra.ofHeckeSpace` followed by the inclusion of fixed vectors.
`heckeEmbedding_injective` composes injectivity of those two maps. The
embedding and its injectivity need only a topology, since `OpenSubgroup`
is part of their data; the group-topology compatibility instance is omitted
from those declarations.

`categoricalCenter_hecke K z` proves that every
`z : CatCenter (SmoothRep.{uR,uG,max uG uR} R G)` has a value `c : H`
in `Subring.center H` such that

```text
SmoothRep.hom (z.app D) (heckeEmbedding K h)
  = heckeEmbedding K (c * h)
```

for all `h : H`. It takes `c` to be `z_D` applied to the unit vector
`δ_K`, which is `K`-fixed because `z_D` is equivariant.
The published `fixedVectorsMap_heckeAct` and
`heckeAct_permRep_unitElement` give `z_D(h) = h*c`.
For each `h`, the published Frobenius intertwiner with value `h` at
`δ_K` is right multiplication by `h` on the Hecke algebra.
`CatCenter.naturality` with respect to this endomorphism of `D`,
evaluated at `δ_K`, gives `z_D(h) = c*h`.
Injectivity of the embedding then proves `h*c = c*h` for every `h`.
No compactness, local-field, reductivity, or finiteness premise is used.

`finite_center_of_categorical_generators` takes exactly an explicit finite
family generating `H` under this categorical action and concludes
`Module.Finite (Subring.center H) H`. For each categorical coefficient it
chooses the central element furnished by the previous theorem. The same
generators consequently span `H` over its ring centre. This proof uses
`Submodule.fg_iff_exists_fin_generating_family` and closure of a submodule
under sums and scalar multiplication.

## Cyclicity and the exact corollary reduction

`permRep_finite L` works for any subgroup of any group over any
commutative ring, with independent coefficient and group universes. It
needs no topology. It proves
`Module.Finite (MonoidAlgebra R G) (permRep R L).asModule` by taking
the singleton generator `δ_L`. For every coset represented by `g` and
every `r : R`, the vector `r δ_{gL}` is the action of
`MonoidAlgebra.single g r` on `δ_L`. Finitely supported functions are
sums of these vectors, so induction on finitely supported functions
proves that this singleton spans the complete group-algebra module.
`Representation.asModuleEquiv` keeps the two module structures explicit.

In namespace `Langlands.Aubert.General.RepresentedParabolic`, the derived
Prop-valued definition `HeckeAlgebraCenterFiniteReductionStatement.{u}` is

```text
FiniteTypeCenterAdmissibleStatement.{u,u} →
  HeckeAlgebraCenterFiniteStatement.{u}
```

`heckeAlgebraCenterFinite_of_finiteTypeCenterAdmissible` proves this
implication. At the unchanged field, connected reductive group and compact
open subgroup of the target, it applies the premise to `D`, using
`permRep_finite` for finite type. The resulting fixed generators become
Hecke elements through `ofHeckeSpace`. They give the first conjunct.
`categoricalCenter_hecke` gives the second conjunct, and
`finite_center_of_categorical_generators` gives the third.

The target's single universe `u` is retained. The premise is specialized
to field universe `u` and representation-carrier universe `u`; no
comparison of centres of differently sized categories is assumed.
Neither the target's Lean/Markdown pair nor any of its imports is edited.
The exact unconditional target remains open until the separately owned
finite-type centre-admissibility theorem is available.
