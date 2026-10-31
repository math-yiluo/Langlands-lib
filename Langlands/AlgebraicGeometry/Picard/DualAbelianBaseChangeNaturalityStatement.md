# Naturality of the canonical comparison of dual abelian schemes

`Langlands.AbelianScheme.DualAbelianBaseChangeNaturalityStatement` is an
internal compatibility obligation between the existing integral dual map
and the canonical comparison for base change. It is a `Prop`-valued
definition, not a proof of that obligation.

For actual abelian schemes `A`, `B` over `S : Scheme.{u}`, an actual
morphism `b : S' ⟶ S`, and `f : A ⟶ B`, write `d(f)` for
`dualAbelianSchemeMapFromEvaluation f` with the displayed endpoint
parameters. Write `E_A` and `E_B` for `dualAbelianBaseChangeIso` with those
same parameters. The conclusion is the equality of actual homomorphisms

`(baseChange b).map (d(f)) ≫ E_A.hom =
  E_B.hom ≫ d((baseChange b).map f)`.

Both sides have source the actual pullback of the constructed dual of
`B` and target the constructed dual of the actual pullback of `A`. The
order reflects contravariance of dualization. The base change of the
source morphism is the existing abelian-scheme base-change functor.
This is an equality of homomorphisms over `S'`, not only equality on
geometric points or on reduced test schemes.

The dual maps are the existing maps obtained by classifying pullback of
the actual Poincare family. The isomorphisms are the canonical comparisons
already constructed in `DualAbelianBaseChange`: their underlying maps are
prescribed by `dualSchemeBaseChangeIso`, which identifies the actual
base-changed universal family with the universal family of the changed
abelian scheme. No arbitrary dual maps or comparison isomorphisms are
supplied as data.

All seven inputs used to construct the dual group structures remain
explicit: tensor comparison preservation, Picard-zero pullback stability,
pullback composition, pullback unit coherence, pullback associativity,
the left-unitor comparison and pullback symmetry. The separate
`PicardZeroUniversalBaseChangeStatement` supplies base-change universality.
The explicit `DualAbelianBaseChangeStatement` input supplies group
compatibility of the prescribed scheme comparison. The latter has its own
published proof, but its conclusion alone does not state the naturality
square asserted here.

Each of `A`, `B`, their actual pullbacks, and their four constructed duals
uses its displayed endpoint data. For each dual these are
`HasDualScheme`, the actual parameter scheme's `DualSchemeGeometry`,
an ordinary inverse line bundle for its Poincare family, and the actual
tensor evaluation isomorphism. The chosen data at an endpoint are shared
by every occurrence of that endpoint in the square. The statement
quantifies over every such collection of choices. It does not assert
unconditional existence of any of them or definitional equality of
different choices.

The two bases are arbitrary schemes in one universe. No flatness,
noetherian, quasi-separated or field hypothesis is imposed beyond the
explicit premises giving the existing constructions. Additivity in `f`
is not required for this integral square. A later rational extension
will also need pointwise additivity at the original and changed
endpoints. The Mumford square theorem is not used in these dual-map
constructions.

The provenance is internal. Worker 57 formulated the exact target
following Worker 144's comparison and ownership analysis. The expected
proof compares the Poincare families obtained by first pulling back
along `f` and then changing the base with those obtained in the reverse
order, and applies uniqueness of classification on every test scheme.
The resulting equality of underlying scheme maps must then be lifted
to the actual constructed abelian-scheme homomorphisms. These family
and classifier comparisons remain proof obligations.

This statement supplies no naturality proof, rationalized square,
involution transport, identity or successive-base coherence for the
dual comparisons, preservation of a polarization, or polarized
Weil-level pullback. Those are separate downstream results; the
statement does not resume any paused representability or
ample-bundle-existence task.
