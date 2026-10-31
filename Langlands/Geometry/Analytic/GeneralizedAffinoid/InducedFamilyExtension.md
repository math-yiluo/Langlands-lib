# Bounded extension into actual affinoid-family actions

Author: Worker 56.

This module constructs the extension of a bounded subgroup-equivariant map
from a genuine affinoid action into an actual group action on affinoid
families. Restriction along the existing normalized identity-coset unit and
copywise extension are inverse, natural operations on complete equivariant
family morphisms. Their equations retain both component indices and the
original bounded algebra maps.

The Lean namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Inputs and scope of the correspondence

Let `K : Type u` be a normed ultrametric field, `G : Type v` a group with a
topology, and `H` a subgroup. Let `X : NormContinuousSpace K H`. This is the
geometric opposite of an action on an actual finite positive-polyradius
closed-ideal quotient algebra with norm-continuous element orbits. Write
`A_X` for `X.unop.obj.V`. The existing `localFunctor H` regards this action
as an actual one-component affinoid-family action of `H`, with component
index `PUnit.{v+1}` and algebra `A_X`. The existing `functor H` constructs
its induced action on the `G/H`-indexed family of copies of this same algebra.

The target `Y : Action (AffinoidFamily.{u,v} K) G` is an actual categorical
action on a family of genuine presented affinoid algebras. Its arrows choose
a target component for every source component and retain an actual bounded
algebra pullback. Components with empty spectra are retained, with their
algebras and index data. No point-faithfulness, reducedness, normalized
radius, finite index, completeness, openness of `H`, or topological-group
hypothesis is needed for this algebraic family construction. The two coset
identities and `familyAction_comp` even omit the topology on `G`.

The target action is not required here to satisfy any additional joint
continuity or analytic automorphism-topology condition. The correspondence
is between the displayed concrete family-action Hom types, relative to
`localFunctor`; it does not assert an adjunction in a completed category of
analytic spaces.

## Actual bounded copy inclusions and assembly

`copyMap H X c` includes the one-component family into coset `c` with the
bounded identity of `A_X`. `assembleFamilyMap H f` assembles any family of
bounded maps from the one-component family into a target family. At `c` it
uses exactly the component index and bounded pullback of `f c` at
`PUnit.unit`. This constructs the full family map even when the source
spectrum or some component spectra are empty.

`copyMap_assembleFamilyMap` proves that restriction to a copy recovers the
supplied complete map. `familyHom_ext` proves that restrictions to every
copy determine the complete family map. Its proof first obtains equality of
the component-index functions, then equality of the dependent bounded
pullbacks. It extracts the latter from equality of the sigma pairs of an
index and its pullback. It does not infer any algebra equality from values
on spectrum points.

`copyMap_action` compares the complete maps

```text
copy(c) ≫ action(g) = localAction(correction(g,c)) ≫ copy(g • c).
```

The component indices agree, and composing the bounded identity with the
original inverse correction operator gives the same bounded pullback on
each side. `familyAction_comp` records the categorical order
`Y.ρ(k) ≫ Y.ρ(g) = Y.ρ(g*k)`.

## Extension and its full-group equivariance

For an actual subgroup-equivariant bounded map

```text
f : (localFunctor H).obj X ⟶ (Action.res _ H.subtype).obj Y,
```

`extendFamilyMap H f` assembles the complete maps
`f.hom ≫ Y.ρ(c.out)`. Thus `copyMap_extendFamilyMap` gives the explicit
restriction to every coset copy. `extendFamilyMap_indexMap` states that its
component index is the input component followed by the target action's
component map. `extendFamilyMap_pullback` states that its bounded pullback
is the input pullback composed with the target action's pullback. Both
projection formulas are definitional.

`extendFamilyMap_equivariant` proves

```text
actionMap(g) ≫ extendFamilyMap(f) = extendFamilyMap(f) ≫ Y.ρ(g).
```

It suffices by `familyHom_ext` to precompose with every `copyMap(c)`.
The correction equation moves the source action onto the original local
copy. Subgroup equivariance of `f` moves that correction through `f`.
The target action law and
`g*c.out = (g • c).out * correction(g,c)` identify the two composites.
Every step is an equation of complete bounded family maps.
`extendFamily H f` bundles this constructed equivariant extension.

## Normalized unit and inverse laws

Write `r : H` for `identityRepresentative H`. The chosen representative of
the identity coset need not be `1`. `unitFamilyMap_eq` expresses the
existing unit as `localAction(r⁻¹)` followed by the identity-coset copy.
The local geometric action at `r⁻¹` has the forward bounded operator at
`r`, by the original algebra action's inverse law.

`out_smul_identityCoset` proves that `c.out` translates the identity coset
to `c`. `correction_out_identityCoset` computes the corresponding correction
as `r`. Consequently `unitFamilyMap_action` proves

```text
unitFamilyMap ≫ actionMap(c.out) = copyMap(c).
```

Its proof cancels the actual inverse local actions at `r⁻¹` and `r`.
It requires no normalization of chosen representatives.

`unitFamilyMap_extendFamilyMap` proves that extension precomposed with the
normalized unit equals `f.hom`. The extension on the identity copy is
`f.hom ≫ Y.ρ(r)`; subgroup equivariance moves `localAction(r⁻¹)` through
`f`, and the target action laws cancel `r⁻¹` with `r`.

`restrictFamily H p` precomposes a full-group equivariant map with the
existing subgroup-equivariant `familyUnit`, using action restriction on
`p`. `restrictFamily_extendFamily` follows from the preceding normalized
unit equation. In the other direction, `extendFamily_restrictFamily`
restricts both maps to each copy, uses full-group equivariance of `p`, and
uses `unitFamilyMap_action`. Thus the inverse law compares entire family
arrows, including bounded pullbacks and data on empty components.

## Natural Hom correspondence and uniqueness

`familyExtensionEquiv` packages the two constructed operations as

```text
((functor H).obj X ⟶ Y) ≃
  ((localFunctor H).obj X ⟶ (Action.res _ H.subtype).obj Y).
```

Its forward operation is restriction and its inverse is extension.
`extendFamily_unique` states that any full-group equivariant family map
whose complete composite with the unit is `f.hom` equals `extendFamily H f`.
It follows by injectivity of this equivalence and the first inverse law.

`familyExtensionEquiv_naturality_left` proves naturality in every original
subgroup-equivariant bounded input arrow `X' ⟶ X`, using the existing
complete naturality equation for `unitFamilyMap` and associativity.
`familyExtensionEquiv_naturality_right` proves naturality in every bounded
equivariant target-family arrow `Y ⟶ Z`, by associativity. Both statements
compare entire morphisms in the relevant action categories.

## Original source and internally derived content

The motivating original is Vladimir G. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces*, unfinished 1995–1996 manuscript,
Construction 1.1.2, printed/PDF page 2. Registered source identifier:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
The publication-folder SHA256 is
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The exact member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

That construction uses an open subgroup, an analytic subgroup-space and its
coset copies. It extends a morphism on copy `c` by applying the target action
at the chosen representative. This module internally implements that
copywise formula for genuine affinoid input actions and actual bounded
family-action targets. The copy assembly, dependent-map extensionality,
unnormalized identity-representative corrections, complete equivariance,
inverse laws and natural Hom-equivalence packaging are internally derived
implementation results, rather than additional quoted manuscript claims.

The analytic automorphism-topology comparison, arbitrary overlapping-atlas
induction, extension to arbitrary analytic targets, analytic adjunction,
actual analytic sites and Harris specialization remain separate construction
obligations. The algebraic correspondence here does not discharge those
analytic obligations.
