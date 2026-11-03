# Homomorphisms from tori to unipotent group schemes are trivial

Worker 1395 wrote this module. It proves Milne, *Algebraic Groups* (2017), Corollary 14.18(b) for
tori: over a field there are no nontrivial homomorphisms from a torus to a unipotent group. Here
the target only needs to be affine, and any homomorphism is allowed (no closed-subgroup
hypothesis).

## Statements (namespace `Langlands.GroupScheme`)

Let `k : Type u` be a field and `S U : GroupScheme (Spec (CommRingCat.of k))`, with
`[IsAffineHom U.X.hom]`.

* `IsTorus.hom_eq_zero_of_isUnipotent (hS : IsTorus S) (hU : IsUnipotent U) (j : S ⟶ U) :
  j = 0`.
* `IsUnipotent.range_eq_bot_of_isTorus (hU : IsUnipotent U) (hS : IsTorus S) (j : S ⟶ U) :
  SubgroupFunctor.range j = ⊥`, the pointwise image subgroup functor being trivial on every test
  scheme.

`IsTorus` is the Library's definition: split after base change to some field extension `K` of `k`
(Milne 12.14). `S` is any group scheme, so the results apply to `T.toGrp` for a commutative group
scheme `T`.

## Proof

Choose `K` with `S_K` split, and write `b : Spec K ⟶ Spec k`. The base change `U_K` is affine over
`Spec K`, since affine morphisms are stable under pullback. `U_K` is unipotent by
`IsUnipotent.baseChange` (module `Unipotent.BaseChange`). So
`IsSplitTorus.hom_eq_zero_of_isUnipotent` (module `Unipotent.SplitTorusHom`) shows that
`j_K = (GroupScheme.baseChange b).map j` is `0`.

To descend, forget the group structure: `Grp.forget` is faithful. The underlying morphism of `j`
then has to be compared with the identity morphism `1 : S.X ⟶ U.X`. Pullback of objects over
`Spec k` along `b` is faithful, by the Library's theorem
`GaloisCocharacterDescent.faithful_algebraPullback k K`. Pullback is monoidal, so it sends `1`
to `1` (`Functor.map_one`), and the underlying morphism of `j_K = 0` is that image of `1`. Hence
`j = 0`. The range statement then follows from `SubgroupFunctor.range_zero` (module
`Unipotent.SplitTorusHom`).
