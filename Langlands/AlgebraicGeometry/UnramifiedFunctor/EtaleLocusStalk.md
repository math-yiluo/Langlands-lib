# Points of a scheme over `Spec D` through its stalks

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusStalk`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusBasic`.

## Stalks (section `Stalk`)

Let `X` be a scheme.

- `specMap_fromSpecStalk_injective`: two local ring maps `χ₁ χ₂` from the stalk
  `𝒪_{X,x}` to a local ring `C` with
  `Spec χ₁ ≫ X.fromSpecStalk x = Spec χ₂ ≫ X.fromSpecStalk x` are equal. Proof:
  Mathlib's bijection `SpecToEquivOfLocalRing` between morphisms
  `Spec C ⟶ X` and pairs of a point and a local map out of its stalk.
- `exists_eq_specMap_fromSpecStalk`: a morphism `h : Spec C ⟶ X` from the
  spectrum of a local ring sending the closed point to `x` is
  `Spec χ ≫ X.fromSpecStalk x` for a local map `χ`. Take
  `χ = Scheme.stalkClosedPointTo h`.

Now let `q : X ⟶ Spec D`.

- `toStalkAt q x : D → 𝒪_{Spec D, q x}` is the canonical map,
  `(ΓSpecIso D).inv ≫ germ ⊤ (q x)`.
- `structMap q x : D → 𝒪_{X,x}` is `toStalkAt q x` followed by the stalk map of
  `q`.
- `specMap_structMap`: `Spec (structMap q x) = X.fromSpecStalk x ≫ q`. Uses
  `Spec.fromSpecStalk_eq` and `Scheme.SpecMap_stalkMap_fromSpecStalk`.
- `structMap_comp_eq`: if `Spec χ ≫ X.fromSpecStalk x ≫ q = Spec δ`, then
  `structMap q x ≫ χ = δ`. Both sides have the same `Spec`, and `Spec` is
  faithful.
- `structMap_stalkSpecializes`: for a specialization `x ⤳ y`, `structMap q x`
  is `structMap q y` followed by the specialization map of stalks.
- `toStalkAt_formallyUnramified`: `toStalkAt q x` is formally unramified,
  being a localization map (`StructureSheaf.IsLocalization.to_stalk`).
- `structMap_formallyUnramified`: if `q` is formally unramified, so is
  `structMap q x`. It is a composite of `toStalkAt q x` with the stalk map of
  `q`, which is formally unramified by `FormallyUnramified.stalkMap`.

## Elements and morphisms (section `Rep`)

Let `g : S' ⟶ S`, and let `e` represent the base change of `F` along `g` by
`Y'`. The published `Charts.elemEquiv g e T t ht` identifies morphisms
`Over.mk t ⟶ Y'` with `F(T)` for `T` over `S` with structure morphism `t ≫ g`.

- `elemEquiv_naturality'`: restriction of elements along `h : T₁ ⟶ T₂`
  corresponds to precomposition with `h.left`. This is the published
  `Charts.elemEquiv_naturality` with the compatibility `h.left ≫ t₂ = t₁` as an
  explicit hypothesis instead of `Mono g`.
- `elemEquiv_symm_naturality`: the same statement for the inverse bijection.
