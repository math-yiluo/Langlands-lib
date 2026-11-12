# Field points over the integers

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`
(`SpaceUniformLangWeilOfFamilyProof.lean`). Provenance: internal. The module contains standard
facts about points of schemes with values in fields; it states nothing new.

## Contents

- `S0` is `Spec (ULift ℤ)`, the terminal scheme of the universe. `toOver T` is a scheme `T`
  regarded over `S0`, `toOverHom` a morphism of schemes regarded over `S0`, and
  `isoToOver T : T ≅ toOver T.left` identifies every scheme over `S0` with its underlying
  scheme. Since `S0` is terminal, all structure morphisms agree (`specULiftZIsTerminal.hom_ext`).
- `exists_lift_of_mem_range`, `exists_lift_of_surjective`: for `f : Z → T` locally of finite type
  and `v : Spec Ω → T` with `Ω` algebraically closed and the image of the closed point in the
  range of `f`, there is `p : Spec Ω → Z` with `p ≫ f = v`. Proof: the fibre product
  `Z ×_T Spec Ω` is nonempty and locally of finite type over `Ω`, so it has a closed point
  (`FieldSchemePoints.exists_closed_specialization`), whose residue field is `Ω` by the
  Nullstellensatz (`pointOfClosedPoint`).
- `exists_lift_at_point`: if moreover `f` is locally quasi-finite, the lift can be chosen
  through any prescribed point `z` of `Z` over the image of `v`. The fibre product is discrete
  (`isDiscrete_preimage_singleton`), so every point of it is closed.
- `spec_hom_ext`: two morphisms `Spec κ → V` to an affine scheme agree when they agree after a
  field extension `κ → Ω`, because `κ → Ω` is injective.
- `exists_desc_of_aut_invariant`: for a Galois extension `Ω / κ` (possibly infinite) and an
  affine scheme `V`, a point `w : Spec Ω → V` invariant under every `κ`-automorphism of `Ω`
  descends to `Spec κ`. Its ring map takes values in the fixed field, which is `κ`
  (`InfiniteGalois.mem_range_algebraMap_iff_fixed`).
- `specMap κ Ω : Spec Ω → Spec κ`, `specMap_comp_apply` (the unique point goes to the unique
  point) and `specMap_aut_comp` (automorphisms of `Ω` over `κ` commute with `specMap`).
- `exists_lift_of_isClosedImmersion`: a point `y : Spec κ → T` lifts along a closed immersion
  `i : R → T` once `specMap κ Ω ≫ y` does: the pullback of `i` along `y` is a nonempty closed
  subscheme of `Spec κ`, hence `Spec κ` itself (`isIso_of_isClosedImmersion_of_surjective`).
- `finite_hom_of_isAffine`: an affine scheme locally of finite type over `ℤ` has finitely
  many points with values in a finite field (`FiniteFieldPoints.finite_ringPoint`).
