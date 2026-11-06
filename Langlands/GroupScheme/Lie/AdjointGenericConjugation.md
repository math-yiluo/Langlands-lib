# Generic conjugation into an adjoint slice

Author: Worker 1630.

This derived helper module turns dominance of the adjoint slice map
`G × 𝔸^e → 𝔤`, `(g, t) ↦ Ad(g) (B t)`, into a pointwise statement about the
generic Lie element. Let `K` be the function field of `𝔸^d` and `X_gen` the Lie
element over `K` whose coordinates are the coordinate functions. Then over
some field extension `L` of `K`, `X_gen` is conjugate to an element of the
slice by a point of `G` that hits the generic point of `G`. This is the
generic-point form of the standard dominance argument for conjugation maps. It
is used in the project's route to unirationality of the scheme of maximal tori
(SGA 3, Exposé XIV). The proof is written out here from Mathlib's
residue-field, stalk and generic-point API, the companion module
`AdjointDominance` (submitted together with this one) and the Library's
`RationalFunctionFieldAlgebra`. No external
theorem is asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`.

## Residue fields over a generic point

Here `X` and `Y` are schemes, `Y` irreducible, `f : X ⟶ Y`, and `ξ` a point
of `X` whose image specializes to the generic point of `Y`.

- `functionFieldToResidueField f ξ h` (definition): the ring map from the
  function field of `Y` to the residue field `κ(ξ)`. It is the composite of
  the specialization map of stalks, the stalk map of `f` at `ξ`, and the
  residue map.
- `SpecMap_functionFieldToResidueField`: its spectrum, followed by the
  canonical morphism `Spec K(Y) ⟶ Y`, is the residue-field point
  `Spec κ(ξ) ⟶ X` followed by `f`. Proof: Mathlib's compatibilities of
  `fromSpecStalk` with specialization and stalk maps.
- `ΓSpecIso_hom_fromSpecStalk_appTop`: on global sections, the canonical
  morphism `Spec 𝒪_{X,x} ⟶ X` is the germ at `x`.

## The generic Lie element

Throughout, `k` is a field and `G` is a group scheme over `Spec k` with affine
structure morphism and finite Lie coordinates `c : FiniteCoordinates G d`. `K`
is the function field of `𝔸(ULift (Fin d); Spec k)` with the `k`-algebra
structure `rationalFunctionFieldAlgebra`, and `B : Matrix (Fin d) e k`.

- `genericLieElement c` (definition): the Lie element over `K` whose
  coordinates in `c` are the coordinate functions
  `rationalFunctionFieldCoordinate`.
- `irreducibleSpace_tensor_coefficientSpace` (instance): if `G` is
  irreducible, so is `G × 𝔸^e`. Mathlib's instance for products with a
  geometrically irreducible, universally open factor applies.
- `fst_genericPoint_tensor_coefficientSpace`: the projection to `G` sends the
  generic point of `G × 𝔸^e` to the generic point of `G`, since the projection
  is surjective.
- `equiv_adjoint_sliceMap_of_factor`: let `σ = (g, t)` be a point of
  `G × 𝔸^e` over an algebra `S`. Suppose its image under the adjoint slice map
  factors through the generic point of `𝔸^d` by a ring map `ψ : K → S`. Then
  the coordinates of `Ad(g) (B t)` are the images under `ψ` of the
  coordinate functions. Proof: the Library identity
  `adjointRepresentation_affineAction` and `affineCoordinates_sliceMap`
  express these coordinates as the coordinates of the image point. The
  factorization computes them as germs at the generic point.

## Main results

- `exists_adjoint_eq_genericLieElement_of_denseRange`: let `G` be
  irreducible and suppose the adjoint slice map
  `sliceMap (adjointRepresentation c) B` has dense range. Then there are a
  field `L` with a `k`-algebra structure, a `k`-algebra map `φ : K → L`, a
  point `g` of `G` over `L`, and a Lie element `Z` over `L`, such that:
  - the generic point of `G` lies in the image of `g`;
  - the coordinates of `Z` lie in the column space of `B` over `L`;
  - `Ad(g) Z` is the image of the generic Lie element under `φ`.

  Proof: let `ξ` be the generic point of `G × 𝔸^e` and `L = κ(ξ)`, with the
  `k`-algebra structure of its structure morphism. Dense range sends `ξ` to
  the generic point of `𝔸^d`, which gives `φ` by
  `functionFieldToResidueField`; `φ` is a `k`-algebra map because both
  structure maps are recovered from morphisms to `Spec k`. The residue-field
  point gives `g` and `t`. `Z` is the Lie element with coordinates `B t`. The
  conjugation identity is `equiv_adjoint_sliceMap_of_factor` together with
  the naturality of `c`. The image of `g` contains the generic point of `G`
  by `fst_genericPoint_tensor_coefficientSpace`.
- `exists_adjoint_eq_genericLieElement`: the same conclusion if `G` is
  moreover smooth and, for some `t₀` with `Y₀` the Lie element of coordinates
  `B t₀`, the image of `ad(Y₀)` and the column space of `B` together span
  `k^d`. Proof: `denseRange_adjointSliceMap`.

No hypothesis is placed on the field `k`. The module does not prove
unirationality of any scheme.
