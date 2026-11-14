# Actual stalk and Pi-quotient u squares under base change

This module supplies derived compatibility results for the actual preliminary
Deligne datum and its constructed pullback. It identifies the two actual routes
from the original total eta stalk through `u` to the extended tangent stalk,
and then to the extended tangent Pi quotient.

## Source and scope

The source is V. G. Drinfeld, *Coverings of p-adic Symmetric Regions* (1976),
Section 2 A, printed pp.109–110 (PDF pp.3–4). The four preliminary sheaf data
are introduced at the end of p.109. Condition (b), at the beginning of p.110,
uses the actual map from the total eta stalk modulo Pi to the total tangent
stalk modulo Pi tensored with the residue field. Both total stalks, their Pi
operators, and the map `u` are the previously constructed objects in
`DeligneAdmissibility`. The pullback is the construction in
`DelignePreDatumBaseChange`.

Registered source: `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
These compatibility formulas are derived infrastructure; they are not claimed
to be separate statements in Drinfeld's text. No source-specific errata file
was present in the pinned Library at preparation.

The actual u square through the residue fibre, injectivity preservation for
condition (b), full admissibility, the moduli functor and representability
remain subsequent obligations. In particular this module does not prove
Proposition 2.4 or the basic theorem.

## Parameters and actual objects

For the Deligne specialization, let `O` be a commutative ring, `d` a nonzero
natural number, `π : O`, and `F` a field with an `O`-algebra structure. Let
`φ : O →+* Γ(S, ⊤)`, let `D : SheafPreDatum d π F φ`, and let
`f : S' ⟶ S` be an arbitrary morphism of schemes. All schemes, rings and
modules use the displayed common universe. No flatness of `f` or admissibility
of `D` is assumed. The hypotheses already belonging to `SheafPreDatum` remain
in force. No representing object, universal object or comparison isomorphism
is taken as additional input.

For `x : S'`, write `y = f x` and `ρ : O_{S,y} → O_{S',x}` for the actual
stalk map. Write `Eρ` for `ModuleCat.extendScalars ρ` and `ιρ` for its
extension/restriction adjunction unit, on underlying elements.
The previously constructed comparisons have directions

- `etaStalkPullbackIso : eta_y ≅ eta'_x`;
- `tangentStalkPullbackIso : T'_x ≅ Eρ(T_y)`;
- `tangentPiQuotientPullbackIso : T'_x/Pi ≅ Eρ(T_y/Pi)`.

The quotients mean quotient by the actual linear range of the corresponding
Pi endomorphism. The tangent stalks carry their canonical local-ring module
structures; the eta stalks carry their integral `O`-module structures.

## Compatibility with actual adjunction units

`structuralPullbackStalkIso_unit_germ` applies to any scheme morphism and
structural module sheaf. The actual structural stalk comparison carries the
germ of the pullback adjunction unit of a section to `ιρ` of the original
germ. The proof uses the two adjunctions defining the existing
`StalkPullback.pullbackStalkIso`, and the uniqueness formula for left adjoints.
Evaluation on a section and its neighborhood-membership witness reduces the
right-adjoint skyscraper comparison to its actual pointwise identity.

`inverseImagePullbackIso_unit` compares the actual sheaf pullback unit with
the presheaf pullback unit followed by sheafification. It follows from the
same uniqueness formula, now for Mathlib's chosen sheaf pullback and its
constructed presheaf-pullback/sheafification adjunction.

`inverseImageStalkIso_germ` proves the germ formula for the existing three-factor
`inverseImageStalkIso` itself. Its factors are the presheaf stalk comparison,
the stalk of the sheafification unit, and the inverse stalk of the actual
sheaf-pullback comparison. The proof uses the preceding unit identity,
the presheaf pullback germ formula, and naturality of germs. The forward and
inverse sheaf-pullback comparisons cancel at the end.

`etaStalkPullbackIso_germ` specializes this identity to the total eta sheaf,
then applies the actual coefficient-restriction comparison on stalks. Thus it
identifies the eta comparison on a germ with the actual inverse-image unit
on its representing section, followed by that coefficient comparison.

## The actual u square and its quotient

`uStalkPullback_square` proves, for every `e : eta_y`,

```
tangentStalkPullbackIso.hom (u'_x (etaStalkPullbackIso.hom e)) = ιρ (u_y e).
```

The proof writes `e` as an actual germ, applies the eta germ formula and the
two existing `uStalkAdd_germ` formulas, and evaluates the existing sheaf
identity `pullbackU_unit` on that section. The structural unit-germ identity
then gives the result. This compares the actual constructed maps throughout.

`tangentPiQuotientPullbackIso_hom_mkQ` is the forward quotient projection
formula. It is obtained from the existing inverse projection square by
composition with the stalk and quotient comparisons and cancellation of their
inverse laws.

`uPiQuotientPullbackMap` packages the additive composite from `eta_y` through
the actual eta comparison, `u'_x`, the pulled tangent quotient projection, and
the tangent quotient comparison. `uPiQuotientPullback_square` proves that this
same composite, displayed explicitly in its statement, sends `e` to
`ιρ(mkQ(u_y e))`. It follows from the forward projection formula, the actual
stalk u square, and naturality of the scalar-extension unit. It asserts no
injectivity or residue-fibre conclusion.

## Scalar-extension unit helpers

`extendScalars_unit_map` is naturality of the extension unit on elements for
an arbitrary ring homomorphism and module morphism.
`extendScalarsComp_unit` and `extendScalarsComp_inv_unit` describe how the
actual composition comparison carries the composite unit to the two
successive units and back. They use Mathlib's formula on `1 ⊗ m` and the
comparison's inverse law. `extendScalars_eqToIso_unit` transports the actual
unit when two ring homomorphisms are equal; its proof eliminates that equality.
These helpers have arbitrary commutative rings and no field or flatness
hypothesis. They prepare the subsequent residue-field compatibility step.
