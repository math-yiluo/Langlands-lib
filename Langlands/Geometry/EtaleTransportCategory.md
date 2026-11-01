# The group-labelled small-etale category

This internal construction starts with an actual scheme `Y : Scheme.{u}`,
a group `G : Type w`, and the existing action convention
`ρ : G →* (Aut Y)ᵐᵒᵖ`. Write `σ(g) = EtaleCohomologyAction.aut ρ g`.
Thus `σ(g * h) = σ(g) ≪≫ σ(h)`. It uses Mathlib's actual small-etale
objects and scheme morphisms.

`EtaleTransport.Object ρ` wraps an object of `Y.Etale`. A morphism from
`U` to `V` consists of a specified label `g : G` and a scheme map
`f : U.etale.left ⟶ V.etale.left` satisfying

```text
f ≫ V.etale.hom = U.etale.hom ≫ σ(g).hom.
```

Different group labels are retained even when they give the same scheme
automorphism. The identity has label one and identity scheme map.
Composition of maps labelled `g`, `h` has label `g * h` and the ordinary
composite scheme map. The semilinearity equation follows by associativity
and the existing automorphism product law; category laws follow by
extensionality in both the label and the scheme map. The four `id_` and
`comp_` formulas expose these operations.

`inclusion ρ : Y.Etale ⥤ Object ρ` takes ordinary small-etale maps to
maps labelled one. It is faithful. `Object.ordinaryMap f h` recovers the
ordinary map when `h : f.label = 1`, and `inclusion_ordinaryMap` proves
that its inclusion is exactly `f`. `toScheme` retains the source schemes
and actual scheme maps. No faithfulness assertion is made for `toScheme`.

`Object.translate g U` uses `EtaleAutomorphism.siteMap σ(g)` to
postcompose `U`'s structure map with `σ(g).hom`. Its scheme is still
`U.etale.left`. `translationIso g U` is an isomorphism in the new
category from `U` to this translated object: both scheme maps are
identities, with labels `g` and `g⁻¹`. The inverse semilinearity equation
uses the automorphism product and unit laws. The inverse equations use
the group inverse laws and the identity scheme maps.

Every arrow `f : U ⟶ V` has a canonical ordinary part

```text
ordinaryPart f : (translate f.label U).etale ⟶ V.etale.
```

Its scheme map is `f.left`, and its structural equation is precisely the
input semilinearity equation. `translationIso_hom_comp_ordinaryPart`
proves that `f` is translation followed by the included ordinary part.
`translationIso_inv_comp` proves the converse formula after undoing
translation. Both equations are proved as equalities of full labelled
morphisms.

The scheme universe is `u`; the group universe `w` is independent.
No topology on `G` is assumed. This is a derived categorical construction
from the imported automorphism action and Mathlib's small-etale category,
not a new assertion attributed to Harris or Berkovich. It is a
prerequisite for an equivariant small-etale site. Covering sieves, sheaf
categories, their comparison with translation-equivariant sheaves,
derived representation-valued sections, compact supports, smoothness,
analytic sites and arithmetic specialization remain separate
construction obligations.
