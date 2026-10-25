# Identity and composition for equivariant scalar extension

The module `Langlands.Geometry.EtaleEquivariantScalarExtensionCoherence`
constructs identity and composition isomorphisms for sheafified scalar
extension on geometrically equivariant small-etale module sheaves. It
identifies their underlying ordinary sheaf maps, proves compatibility with
the extension units, and proves both identity laws and associativity.
All declarations lie in `Langlands.Geometry.EtaleCohomologyAction`.

## Parameters and provenance

The coefficient rings `R A B C : Type u` are arbitrary commutative rings.
The maps are `φ : R →+* A`, `ψ : A →+* B`, and `χ : B →+* C`.
Let `X : Scheme.{u}`, `G : Type w` with `Group G`, and
`ρ : G →* (Aut X)ᵐᵒᵖ`. Module carriers also use universe `u`.
The group universe `w` is independent. No topology on the group or
coefficient rings, and no flatness or other condition on the ring maps,
is assumed.

This is an internal categorical construction. It uses the equivariant
extension/restriction adjunction from `EtaleEquivariantScalarExtension`,
the restriction comparisons from `EtaleScalarCoherence`, and the ordinary
extension comparisons and coherence from `EtaleScalarExtensionCoherence`.
The construction uses Mathlib's `conjugateIsoEquiv` in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`. No external theorem is
transcribed, and no comparison or coherence law is assumed as input.
Its role in the Harris framework is to make successive coefficient
extensions coherent while retaining the actual geometric action.

Write `L_φ` for `scalarExtensionFunctor φ ρ`, `Q_φ` for
`scalarRestrictionFunctor φ ρ`, and `η_φ` for
`scalarExtensionUnit φ ρ`. The underlying ordinary extension is
sectionwise tensor extension followed by sheafification on the small-etale
site. In the formulas below, `⋙` applies the left functor first, and `;`
composes morphisms in order of application. Let

```text
j_R : Q_id_R ≅ identity,
d_φ,ψ : Q_(ψ.comp φ) ≅ Q_ψ ⋙ Q_φ
```

be `scalarRestrictionIdIso` and `scalarRestrictionCompIso`.

## Constructed comparisons and underlying maps

`scalarExtensionIdIso ρ` constructs

```text
i_R : L_id_R ≅ identity on EquivariantSheaf R ρ.
```

It is the inverse image of `j_R.symm` under `conjugateIsoEquiv` for
the identity adjunction and `scalarExtensionRestrictionAdj (RingHom.id R) ρ`.

`scalarExtensionCompIso φ ψ ρ` constructs

```text
c_φ,ψ : L_(ψ.comp φ) ≅ L_φ ⋙ L_ψ.
```

It is the inverse image of `d_φ,ψ.symm` under the same equivalence for
the composite adjunction `(adj φ).comp (adj ψ)` and `adj (ψ.comp φ)`.
Both are natural isomorphisms in the equivariant sheaf categories, so their
components and inverse components are equivariant morphisms.

The four lemmas `scalarExtensionIdIso_hom_app_hom`,
`scalarExtensionIdIso_inv_app_hom`,
`scalarExtensionCompIso_hom_app_hom`, and
`scalarExtensionCompIso_inv_app_hom` identify the underlying sheaf maps
with the corresponding components of `sheafExtendScalarsIdIso` and
`sheafExtendScalarsCompIso`, in both directions. These equalities hold by
reflexivity: the equivariant adjunction has the ordinary unit and counit
as its underlying maps, and the restriction comparisons have the ordinary
restriction maps as their underlying maps.

`conjugate_scalarExtensionIdIso_hom` and
`conjugate_scalarExtensionCompIso_hom` identify the conjugates of the
forward extension comparisons with the inverse restriction comparisons.
Both follow from the inverse law of `conjugateEquiv`.

## Compatibility with adjunction units

For `F : EquivariantSheaf R ρ`, `scalarExtensionUnit_id` proves

```text
(η_id_R)_F ; Q_id_R.map ((i_R).hom.app F) = (j_R).inv.app F.
```

`scalarExtensionUnit_comp` proves

```text
(η_(ψ.comp φ))_F ; Q_(ψ.comp φ).map ((c_φ,ψ).hom.app F)
  = (η_φ)_F ; Q_φ.map ((η_ψ)_(L_φ F)) ; (d_φ,ψ).inv.app (L_ψ (L_φ F)).
```

These are equations of equivariant morphisms. Their proofs apply
`TranslationAction.Equivariant.Hom.ext` and then the corresponding
ordinary unit equation. The identified underlying maps ensure that the
ordinary equations apply directly.

## Identity and associativity laws

`scalarExtensionCompIso_id_left` splits extension along `φ` by
`c_id_R,φ`, applies `L_φ` to `i_R`, and removes the identity functor by
the left unitor. The resulting natural transformation is the identity
of `L_φ`.

`scalarExtensionCompIso_id_right` splits extension along `φ` by
`c_φ,id_A`, evaluates `i_A` after `L_φ`, and removes the identity
functor by the right unitor. The resulting transformation is again the
identity of `L_φ`.

`scalarExtensionCompIso_assoc` equates the following two natural
transformations from `L_(χ.comp (ψ.comp φ))` to `L_φ ⋙ (L_ψ ⋙ L_χ)`:

- First split by `c_(ψ.comp φ),χ`, apply `L_χ` to `c_φ,ψ`, then apply
  the functor associator.
- First split by `c_φ,(χ.comp ψ)`, then evaluate `c_ψ,χ` after `L_φ`.

Each proof applies extensionality for natural transformations and then
for equivariant morphisms. The resulting ordinary sheaf equality is the
component of the corresponding published ordinary coherence law at
`F.obj`. The identity and associative composites of ring maps have
matching source functors in these formulas.

## Scope

The scheme and geometric action stay fixed throughout. This unit supplies
coefficient identity/composition coherence for equivariant scalar
extension. It does not assert exactness, preservation of injectives,
commutation with global sections or higher cohomology, smoothness of
group actions, or a Harris comparison theorem. Equivariant geometric
pullback comparisons, varying-scheme coefficient diagrams, ideal
reduction, inverse systems, and the broader Harris specialization remain
separate constructions.
