# Extension by zero and functors

Author: Worker 61. Integrator moved the generic `ExtendMap` section unchanged
from `Langlands.Cohomology.DivisibleSystem.InvariantComparison` into this
module. Its declarations remain in `Langlands.Cohomology` with their original
names, types, definitions and proofs. The module imports only
`Langlands.Cohomology.DerivedPlus`.

This shared location supplies both the divisible-system comparisons and
`DerivedPlusNaturality` without a duplicate inverse-naturality lemma.

`C`, `D` are categories with zero morphisms and zero objects,
`F, G : C ⥤ D` preserve zero morphisms, and `e : c.Embedding c'` is an
embedding of complex shapes. The Library's `DerivedPlus.mapExtendIso F K e` is
an isomorphism from the extension of `F` applied to `K` to `F` applied to the
extension of `K`. Its components `DerivedPlus.extendXMapIso F K i` are the
identity in the degrees coming from `c`, and the unique isomorphism of zero
objects elsewhere.

- `extendMapIso e F K`: the inverse isomorphism
  `(F.mapHomologicalComplex c').obj (K.extend e) ≅
  ((F.mapHomologicalComplex c).obj K).extend e`. By `extendMapIso_hom_f`, its
  component in degree `i'` is the inverse of `DerivedPlus.extendXMapIso F K (e.r i')`.
- `extendXMapIso_inv_mapX` and `extendMapIso_hom_naturality`: `extendMapIso`
  is natural in `K` with respect to Mathlib's `extendMap`. In degrees coming
  from `c` both sides equal `F` of the component. In the other degrees the
  target is zero.
- `extendXMapIso_inv_app` and `extendMapIso_hom_app`: `extendMapIso` is
  natural in the functor. For `α : F ⟶ G`, `α` applied degreewise to `K.extend e`,
  followed by `extendMapIso e G K`, equals `extendMapIso e F K` followed by the
  extension of `α` applied degreewise to `K`. The proof is the same.

## Scope

These are categorical comparison maps and their naturality identities. They
require zero objects and zero morphisms, with the functors preserving zero
morphisms; they make no claim about derived-functor exact sequences or the
geometric cohomology of Harris's spaces.
