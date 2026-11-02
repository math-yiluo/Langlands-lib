# Actual noetherian models over an affine base

`Modules.HasAffineNoetherianModel p M N` is a predicate on a morphism
`p : Y → Spec R` and two actual module sheaves on `Y`. It consists of a
commutative noetherian ring `R₀` in the same universe, a ring map
`φ : R₀ → R`, a scheme `Y₀`, a proper locally finitely presented morphism
`p₀ : Y₀ → Spec R₀`, a morphism `q : Y → Y₀`, and two finitely presented
module sheaves `M₀, N₀` on `Y₀`. The required square, with horizontal maps
`q` and `Spec.map φ`, is Cartesian. The target `N₀` is flat over `p₀` in
the actual stalkwise sense of `Modules.IsFlatOver`. Ordinary module
pullback along `q` identifies `M₀` with `M` and `N₀` with `N` by actual
module isomorphisms.

No flatness of `M₀` or of the ambient scheme morphism is required. The
base `Spec R` is affine, and no global model over an arbitrary
non-quasi-compact base is asserted. The module comparisons retain the
actual sheaves and their ordinary pullbacks; they are not comparisons
only of geometric fibres, classes, or global sections.

The lemma `HasAffineNoetherianModel.of_iso` preserves the same ring,
scheme, Cartesian square, and model modules when either given module is
replaced by an isomorphic one. Its proof composes the two specified
pullback isomorphisms with the supplied isomorphisms.

This is an internal interface for separating noetherian approximation
from the geometric finite-linear-model argument in proper-Hom
representability. Its provenance is the explicit packaging of the actual
scheme pullback and module data already defined in the Library. It does
not assert that such models exist. The motivating approximation results
are Stacks Project, *Limits of Schemes*, Lemmas 01ZM and 01ZR, the lemma
`descend-module-flat-finite-presentation` in Section 32.10, and Lemma
081F; the retained source is `limits.tex` at commit `a04446e5`, registered
as `stacks-limits-of-schemes-a04446e5`. Existence of this package from
properness, local finite presentation, finite presentation of the two
modules, and relative flatness of the target is a separate proposition
and proof obligation.
