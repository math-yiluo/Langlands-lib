# Equivariant scalar extension and geometric pullback

The module `Langlands.Geometry.EtaleEquivariantScalarExtensionPullback`
constructs a natural isomorphism between the two orders of sheafified
scalar extension and geometric equivariant etale pullback. It identifies
both underlying sheaf maps and proves compatibility with extension units
and with identity and composite geometric pullbacks. Declarations lie in
`Langlands.Geometry.EtaleCohomologyAction`.

## Parameters and provenance

Let `R S : Type u` be arbitrary commutative rings, `φ : R →+* S`,
`X Y Z : Scheme.{u}`, and `G : Type w` a group. Module carriers use
universe `u`; the group universe is independent. The supplied actions are
`ρ : G →* (Aut X)ᵐᵒᵖ`, `τ : G →* (Aut Y)ᵐᵒᵖ`, and, for composition,
`υ : G →* (Aut Z)ᵐᵒᵖ`. The map `f : Y ⟶ X` is etale, and `hf` states

```text
f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f
```

for every `g : G`. For composition, `k : Z ⟶ Y` is etale and `hk`
states the corresponding equivariance equation with `τ` and `υ`.
No flatness assumption on the coefficient homomorphism or topology on
the group is required.

This is an internal categorical construction. It uses the actual
extension/restriction adjunction from `EtaleEquivariantScalarExtension`,
the scalar restriction/pullback interchange from `EtaleScalarRestriction`,
the ordinary sheaf comparison and its unit/geometric coherence equations
from `EtaleScalarExtensionPullback`, and the geometric equivariant
pullback comparisons from `EtaleEquivariantPullbackFunctoriality`.
No external theorem is transcribed. Equivariance of the extension
comparison is derived from the universal lift; it is not assumed.

Write `L_X`, `Q_X` for extension and scalar restriction on equivariant
sheaves on X, and similarly for Y. Write `P_R`, `P_S` for equivariant
pullback along f at the two coefficient rings. These are the existing
`equivariantPullback` functors with the supplied action data. Write `η_X`
and `η_Y` for the extension units, and

```text
δ : Q_X ⋙ P_R ≅ P_S ⋙ Q_Y
```

for `scalarRestrictionEquivariantPullbackIso`. Its underlying sheaf maps
are identity maps. Write `β` for the ordinary comparison
`sheafExtendScalarsPullbackIso φ f`, whose forward component goes from
pullback of ordinary extension to extension of ordinary pullback.
Here `⋙` applies the left functor first; `;` composes morphisms in order
of application.

## Constructing equivariance through the adjunction

For `F : EquivariantSheaf R ρ`, the composite

```text
P_R.map ((η_X)_F) ; δ.hom.app (L_X F)
  : P_R F ⟶ Q_Y (P_S (L_X F))
```

is an equivariant morphism. `scalarExtensionPullbackInv` applies
`scalarExtensionLift φ τ` to it, yielding an equivariant map

```text
L_Y (P_R F) ⟶ P_S (L_X F).
```

`scalarExtensionPullbackInv_hom` proves that its underlying sheaf map
is exactly `β.inv.app F.obj`. The proof uses the ordinary lift uniqueness
theorem `sheafExtensionLift_unique`. The unit equation required there
follows from `sheafExtensionUnit_pullback`, composed with the scalar
restriction of `β.inv`. The inverse-isomorphism law and preservation of
identity by scalar restriction reduce the equation to reflexivity.
Thus the equivariant lift recovers the previously constructed geometric
comparison on actual sheafifications, rather than positing a new
comparison map.

`scalarExtensionPullbackObjIso` uses
`TranslationAction.Equivariant.mkIso` on the inverse ordinary
isomorphism. Its equivariance is the commutation equation of the lift,
after substituting the preceding underlying-map identification. Taking
the resulting isomorphism's inverse gives

```text
P_S (L_X F) ≅ L_Y (P_R F).
```

The constructor supplies equivariance of the other direction and the
inverse identities. `scalarExtensionEquivariantPullbackIso` assembles
these components into the natural isomorphism

```text
L_X ⋙ P_S ≅ P_R ⋙ L_Y.
```

Naturality follows from that of the ordinary comparison, by
extensionality of equivariant morphisms.

The lemmas `scalarExtensionEquivariantPullbackIso_hom_app_hom` and
`scalarExtensionEquivariantPullbackIso_inv_app_hom` identify its forward
and inverse underlying sheaf maps with those of `β`. Both equalities
hold by reflexivity for the chosen isomorphism constructor.

## Unit and geometric coherence

`scalarExtensionUnit_equivariantPullback` proves the equation

```text
P_R.map ((η_X)_F) ; δ.hom.app (L_X F) ;
  Q_Y.map ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F)
  = (η_Y)_(P_R F).
```

After applying equivariant morphism extensionality, the middle map is
identity and the remaining equality is the ordinary pullback-unit law.

`scalarExtensionEquivariantPullbackIso_id` applies the extension
comparison for the identity scheme map, then extension of the geometric
identity comparison at R. The result equals the geometric identity
comparison at S evaluated on `L_X F`. The proof forgets equivariance
and applies `sheafExtendScalarsPullbackIso_id`.

`scalarExtensionEquivariantPullbackIso_comp` compares the following
maps from pullback of `L_X F` along `k ≫ f` to extension on Z of the
successive R-coefficient pullbacks of F:

- Apply the extension comparison for `k ≫ f`, then extension of the
  inverse geometric composition comparison at R.
- Apply the inverse geometric composition comparison at S, pull back
  the extension comparison for f along k, then apply the extension
  comparison for k at the R-coefficient pullback of F.

The composite equivariance witness is the existing
`equivariantMap_comp ρ τ υ f k hf hk`. The proof again uses
extensionality of equivariant morphisms and the published ordinary
comparison law `sheafExtendScalarsPullbackIso_comp`. Both geometric laws
therefore hold for the particular natural isomorphism constructed here.

## Scope

This unit concerns arbitrary etale scheme maps equipped with the stated
equivariance equation and arbitrary coefficient homomorphisms between
commutative rings in the common universe. It gives actual functors and
maps on geometrically equivariant small-etale sheaves. It does not
assert exactness, preservation of injectives, commutation of scalar
extension with global sections or higher cohomology, smoothness of
group actions, compact-support comparisons, or a Harris comparison
theorem. Coefficient identity/composition coherence is treated
separately; mixed ring/geometric coherence, coefficient diagrams,
ideal reduction, inverse systems and Harris specialization retain their
separate obligations.
