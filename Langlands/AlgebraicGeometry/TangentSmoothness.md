# Smoothness and dense range from surjectivity on rational tangent vectors

Author: Worker 1630.

This derived helper module proves the standard tangent-space criterion: a
morphism from a smooth scheme over a field `K` is smooth at a rational point
when it is surjective on tangent vectors there, and so it has dense image in
an irreducible target. The argument is the usual Jacobi–Zariski argument,
written out in this module. It uses Mathlib's commutative algebra and scheme
API and the Library's rational stalk derivation correspondence
`Picard.rationalStalkDerivationTangentEquiv`. No external theorem is
asserted.

All declarations live in the namespace
`Langlands.AlgebraicGeometry.TangentSmoothness`.

## A split-injectivity criterion over a local ring

`exists_leftInverse_of_forall_extend`: let `B` be a local ring and
`B → K` a surjection onto a field. Let `l : M → N` be a `B`-linear map,
with `M` finite and `N` finite free. If every linear map `M → K` extends
along `l` to a linear map `N → K`, then `l` has a linear left inverse.

Proof: by Mathlib's `IsLocalRing.split_injective_iff_lTensor_residueField_injective`,
it suffices to show that `l` becomes injective after tensoring with the residue
field. The kernel of `B → K` is the maximal ideal, so `K` is identified with
the residue field as a `B`-algebra. A vector killed by `l ⊗ 1` is killed by
every linear form on the residue-field fiber of `M`. Each such form, restricted
along `M → κ ⊗ M`, extends along `l` by hypothesis. Its base change then
factors the form through `l ⊗ 1`.

## The Jacobi–Zariski split criterion

`formallySmooth_of_mapBaseChange_split`: let `k → A → B` be ring maps with
`B` formally smooth over `k`. Suppose the first map
`B ⊗[A] Ω[A/k] → Ω[B/k]` of the Jacobi–Zariski sequence has a left inverse.
Then `B` is formally smooth over `A`.

Proof: the split exact sequence `B ⊗ Ω[A/k] → Ω[B/k] → Ω[B/A] → 0` makes
`Ω[B/A]` a direct summand of the projective module `Ω[B/k]`, so it is
projective. In the sequence `H¹(L_{B/k}) → H¹(L_{B/A}) → B ⊗ Ω[A/k] → Ω[B/k]`,
the first group is zero because `B` is formally smooth over `k`, so `δ` is
injective. The last map is injective, so `δ` is zero. Hence `H¹(L_{B/A})`
vanishes. Mathlib's characterization of formal smoothness by a projective
module of differentials together with vanishing `H¹` finishes the proof.

## Smoothness from extension of derivations

`formallySmooth_of_forall_derivation_extend`: let `k → A → B` be ring maps
with `B` local and formally smooth over `k`. Assume `Ω[A/k]` is finite over
`A`, `Ω[B/k]` is finite over `B`, and `B → K` is a surjection onto a field
compatible with `A → K`. If every `k`-derivation `A → K` is the restriction
of a `k`-derivation `B → K`, then `B` is formally smooth over `A`.

Proof: `Ω[B/k]` is flat (formal smoothness) and finite over a local ring, so
it is free. A linear form `B ⊗ Ω[A/k] → K` gives a derivation `A → K`. An
extension to `B` gives a form on `Ω[B/k]` that restricts to the original form
along the Jacobi–Zariski map. The split-injectivity criterion gives a left
inverse, and the Jacobi–Zariski split criterion concludes.

## The scheme criterion

Throughout, `K` is a field, `X` and `Y` are schemes in one universe, `p` and
`q` are their structure morphisms to `Spec K`, and `x : Spec K ⟶ X` is a
`K`-point. Stalks carry the Library algebra structure `stalkAlgebraOver`.
`IsRationalPoint` and `IsTangentVectorAt` are the Library predicates from
`Picard.PointTangentSeparation`: a `K`-point is a section of the structure
morphism, and a tangent vector at `x` is a `K[ε]`-point over `K` whose
restriction along `ε ↦ 0` is `x`.

- `IsTangentSurjectiveAt p q f x` (definition): every tangent vector of `Y`
  at `x ≫ f` is `s ≫ f` for some tangent vector `s` of `X` at `x`. The
  definition imposes no further condition on `f`.

Supporting lemmas:

- `formallySmooth_toStalk` and `essFiniteType_toStalk`: the map from `K` to
  a stalk of the structure sheaf of `Spec K` is formally smooth and
  essentially of finite type, being a localization.
- `stalkAlgebraOver_algebraMap`: the structure map `K → 𝒪_{X,z}` is the
  composite of `K → 𝒪_{Spec K, p z}` with the stalk map of `p`.
- `formallySmooth_stalkAlgebraOver`: if `p` is smooth, every stalk of `X` is
  formally smooth over `K`.
- `essFiniteType_stalkAlgebraOver`: if `p` is locally of finite type, every
  stalk of `X` is essentially of finite type over `K`.
- `stalkMap_comp_stalkAlgebraOver_algebraMap`: if `f ≫ q = p`, the stalk
  maps of `f` are `K`-algebra maps.
- `rationalStalkAugmentation_comp_stalkMap`: the augmentation of the stalk of
  `Y` at the rational point `x ≫ f` is the stalk map of `f` followed by the
  augmentation of the stalk of `X` at `x`.
- `locallyOfFinitePresentation_of_comp_eq`: if `f ≫ q = p` and `p`, `q` are
  locally of finite type, then `f` is locally of finite presentation. `Y` is
  locally Noetherian.

Main results. Assume `f ≫ q = p`, `p` smooth, `q` locally of finite type,
`x` a rational point of `X` and `IsTangentSurjectiveAt p q f x`.

- `formallySmooth_stalkMap_of_isTangentSurjectiveAt`: the stalk map of `f`
  at the image point of `x` is formally smooth. Proof: apply the derivation
  criterion with `k = K`, `A` the stalk of `Y`, `B` the stalk of `X` and the
  augmentation of `B` onto `K`. Differentials are finite because both stalks
  are essentially of finite type over `K`. A `K`-derivation of `A` into `K`
  corresponds to a tangent vector of `Y` at `x ≫ f` under
  `rationalStalkDerivationTangentEquiv`. By hypothesis this is `s ≫ f` for a
  tangent vector `s` at `x`, which corresponds to a derivation of `B`. The
  derivation of `B` restricts to the given derivation of `A`. Both
  correspond to the same tangent vector, and the equivalence is injective.
- `mem_smoothLocus_of_isTangentSurjectiveAt`: if moreover `f` is locally of
  finite presentation, the image point of `x` lies in Mathlib's smooth locus
  `f.smoothLocus`.
- `denseRange_of_isTangentSurjectiveAt`: if moreover `Y` is irreducible, then
  `f` has dense range. Proof: `f` is locally of finite presentation by the
  lemma above. Its restriction to the open smooth locus is smooth, hence
  flat and locally of finite presentation, hence universally open. So its
  image is a nonempty open subset of the irreducible space `Y`, which is
  dense.

No irreducibility, reducedness or finite-type hypothesis is placed on `X`
beyond smoothness over `K`, and no hypothesis is placed on `K`.
