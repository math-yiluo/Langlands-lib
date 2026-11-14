# Integral conjugacy of split tori with maximal residue fibres

This internal unit constructs a conjugator between two supplied split integral
tori from maximality of their residue maps. Its provenance is the composition
of the published integral character-coordinate maps, exact Henselian transporter
lifting, and maximal-torus conjugacy over algebraically closed fields. It does
not transcribe a new external result or assert an integral torus existence
theorem. The construction supports the integral conjugacy step in an eventual
proof of apartment containment for supplied integral models.

## Statement

`Langlands.GroupScheme.HenselianSplitTorusConjugacyStatement.{u}` is a closed
proposition. Let `R : Type u` be a commutative Henselian local ring, and let
`k : Type u` be an algebraically closed field with an `R`-algebra structure
whose algebra map `R → k` is surjective. This allows any supplied presentation
of the residue field. Let `G` be a smooth affine group scheme over `Spec R`.
Assume that its actual pullback `G_k` has connected underlying space. Let
`T₁` and `T₂` be split commutative group schemes over `Spec R`, and let
`j₁ : T₁ → G` and `j₂ : T₂ → G` be actual group-scheme homomorphisms.
Assume that each pulled-back map `(j₁)_k`, `(j₂)_k` is a maximal torus in
`G_k`, using the published `IsMaximalTorus` predicate. Then there are an actual
section `g ∈ G(R)` and an actual isomorphism `e : T₁ ≅ T₂` such that

```
j₁ ≫ int(g) = e.hom ≫ j₂.
```

The displayed equation is an equality of group-scheme homomorphisms. In Lean,
the right side uses `CommGroupScheme.groupHom e.hom`. Thus the assertion
includes all scheme-valued test points, not only rational points. No
characteristic restriction is imposed. No domain, valuation, Noetherian,
connectedness of the integral total space, or reductivity hypothesis is added.
A separate closed-immersion hypothesis on the integral maps is unnecessary
for this conclusion; closedness of the residue maps is part of their supplied
maximality. The integral tori and their residue maximality remain inputs.

`henselianSplitTorusConjugacy` proves this proposition. The helper
`exists_henselian_splitTorus_conjugacy` has the corresponding local signature.

## Exact lifting of a prescribed residue conjugacy

The stronger helper `exists_henselian_splitTorus_conjugacy_lift` does not need
an algebraically closed residue field, connected residue group, maximality,
or closed immersions. It retains smoothness and affineness of `G`, splitness
of both sources, Henselianity of `R`, and surjectivity of `R → k`. Its inputs
are a specified actual point `g₀ ∈ G_k(k)` and a specified actual isomorphism
`e₀ : (T₁)_k ≅ (T₂)_k` satisfying the conjugation equation over `k`.
It constructs `g ∈ G(R)` and `e : T₁ ≅ T₂` with the integral conjugation
equation and both exact recovery equalities:

```
baseChangeSectionHom (Spec.algebraMap R k) G g = g₀
(CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso e = e₀.
```

No choice of a different residue conjugator or residue source isomorphism is
substituted for the inputs. There is no uniqueness assertion.

## Implemented proof

First, `splitTorus.exists_fieldIsomorphismExtension` treats two coordinate
tori indexed by arbitrary finite types `I` and `J`. The two maps of a supplied
field isomorphism induce integral linear character maps through the published
`characterMap`. Their actual extensions over any base scheme use
`exponentHom`. The equations `characterMap_comp`, `characterMap_id`,
`exponentHom_comp`, and `exponentHom_id` show that the extended maps are
inverse. The canonical pullback comparison is exactly
`exponentHom_baseChange`; `exponentHom_characterMap` recovers the original
field homomorphism. No equality of the index types or prior integral source
isomorphism is assumed.

`IsSplitTorus.isomorphism_fieldBaseChange_surjective` chooses splittings of
the two original tori. It conjugates the supplied fibre isomorphism into
coordinate tori using the actual split-torus pullback isomorphisms, applies
the preceding extension, and conjugates back. Functoriality and cancellation
of those actual isomorphisms prove equality of the complete pulled-back
isomorphism with its prescribed value. This works over any base scheme and
any field point, independently of the Henselian hypotheses.

`PointwiseSchemeAction.isTransporter_iff_conjugation_eq` identifies the
published all-refinement transporter relation `IsTransporter j₂ j₁ g`
with `j₁ ≫ int(g) = j₂` for an actual section. Its proof evaluates the
homomorphism equation on every scheme point, uses the group law to multiply
by `g⁻¹`, and identifies the pullback of the section with `constantPoint`.

For exact lifting, extend `e₀` to `e` by the preceding surjectivity theorem.
The residue conjugation equation is then the transporter equation for the
two integral maps `e.hom ≫ j₂` and `j₁`, which have the same split source
`T₁`. The actual pullback-point equivalence transfers this residue point
to an `R`-scheme test point. The published
`PointwiseSchemeAction.exists_henselian_transporter_of_split` constructs an
integral transporter with exact recovery. That published theorem uses the
actual smooth transporter scheme and
`HenselianSections.exists_section_of_smooth_of_surjective`. The equivalence
with the conjugation equation gives the asserted integral equality; injectivity
of the pullback-point equivalence gives exact recovery of `g₀`.

Finally, `exists_henselian_splitTorus_conjugacy` applies the published
`maximalTorusConjugacy` to the actual smooth connected affine residue group.
It obtains a residue point and a source isomorphism, then applies the exact
lifting helper. The closed proposition packages this conclusion without any
additional inputs.

## Scope

This unit does not construct an integral torus or an integral model, derive
residue maximality from generic maximal splitness, descend models or tori,
or locate a prescribed building point in an apartment. Those are separate
obligations in the application. In particular,
`UnramifiedFixedPointSplitTorusStatement` remains open. The unit neither imports
nor uses the barred unramified building-descent statements.
