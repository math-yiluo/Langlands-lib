# Central isogenies in actual affine descent

This internal module combines actual affine group-scheme effectivity and
compatible-morphism descent with preservation and fpqc reflection of central
isogenies. It works in arbitrary universe `u`. The groups may be
noncommutative, and the schemes and tests may be nonreduced.

## Morphisms between solutions

Let `p : S ⟶ B` be flat, surjective and quasi-compact. For actual data
`D` and `E`, solutions `s` and `t`, and a compatible actual homomorphism
`f : G ⟶ H`, `Solution.descendHom_isCentralIsogeny_iff` proves

```text
IsCentralIsogeny (Solution.descendHom s t f hf) ↔ IsCentralIsogeny f.
```

The recovery equation identifies the base change of the descended map,
postcomposed with `t.iso.hom`, with `s.iso.hom ≫ f`. For the forward
implication, base-change preservation and transport under the target
isomorphism give centrality of the latter composite. Transport under the
source isomorphism then gives the assertion for `f`. For the reverse
implication, transport under the source isomorphism, the same recovery
equation, and transport under the target isomorphism show that the actual
base-changed descended map is a central isogeny. The implemented
`centralIsogenyFpqcReflection` proves the assertion for the descended map.
Reflection is a proved theorem, not an effectivity or reflection hypothesis
added to this interface.

`Solution.descendTo_isCentralIsogeny_iff` specializes this result to the
canonical solution of a target already defined over `B`.

## Constructed affine central isogenies

Now suppose `B`, `S`, and the underlying scheme of `G` are affine and
`p` is flat and surjective. Quasi-compactness follows from the affine
hypotheses. `D.affineSolution` constructs the source solution from the datum;
no solution or descended source is an input.

For any group scheme `C` over `B` and any compatible arrow
`f : G ⟶ (baseChange p).obj C`,
`Datum.affineHomTo_isCentralIsogeny_iff` proves that the constructed
`D.affineHomTo C f hf` is a central isogeny precisely when `f` is.
The target `C` need not be affine. The analogous result
`affineHom_isCentralIsogeny_iff` treats two affine data, constructing both
solutions.

Given `hcentral : IsCentralIsogeny f`, `Datum.affineCentralIsogenyTo`
packages the actual arrow to `C` and its central-isogeny proof.
`baseChange_affineCentralIsogenyTo` states the exact recovery equation

```text
(baseChange p).map (D.affineCentralIsogenyTo C f hf hcentral).val
  = D.affineSolution.iso.hom ≫ f.
```

`existsUnique_affineCentralIsogenyTo` gives exactly one arrow satisfying
both the central-isogeny predicate and this equation. Its proof uses
the implemented unique affine arrow, the equivalence above, and uniqueness
among all arrows satisfying the recovery equation.

Every occurrence of `IsCentralIsogeny` retains the unchanged finite, flat,
surjective and locally finitely presented underlying map, and the full
scheme-theoretic kernel centrality on all test schemes and all their
restrictions. There is no field, finite-type, smoothness or reducedness
assumption, and no centre representability assumption.

## Provenance and scope

All claims are derived from `Descent.AffineDatumMorphisms`,
`CentralIsogeny.BaseChange`, `CentralIsogeny.FpqcReflection`, and
`CentralIsogeny.Transport`. The module uses their actual recovery equation
and proved preservation, reflection and isomorphism-transport laws. It
asserts no new literature theorem and invokes no unproved statement as a
premise.

For the simply connected cover-existence construction, a compatible
central covering arrow can therefore be descended once its actual affine
source datum has been constructed. Construction of that datum,
semisimplicity and simple connectedness of the descended group, and the
central-cover universal property remain separate obligations.
