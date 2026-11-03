# Forward implication of maximal-torus base change: reduction to central tori

Worker 1379.

## Statements

`MaximalTorusBaseChangeForwardStatement.{u}` is the forward implication of
Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Theorem 17.82, printed p.379 (one-based PDF p.395): "Let G be a group
variety over k and let k' be a field containing k. A torus T in G is
maximal if and only if T_{k'} is maximal in G_{k'}." In Lean: for fields
`k K : Type u` with `Algebra k K`, a smooth affine group scheme `G` over
`Spec k`, a commutative group scheme `T` and `i : T.toGrp ⟶ G` with
`IsMaximalTorus i`, the base-changed homomorphism `T_K.toGrp ⟶ G_K` is
`IsMaximalTorus`. Its hypotheses and its conclusion are those of the
published `MaximalTorusBaseChangeStatement`, but it states only the
implication from `k` to `K`. The base change uses the same commutative and
ordinary group-scheme base-change functors along `Spec K ⟶ Spec k`.

`MaximalTorusBaseChangeForwardReductionStatement.{u}` says that the
forward implication follows from two premises at the same universe:

- `TorusCentralizerSmoothStatement.{u}`: every closed representative of
  the centralizer `torusCentralizer i` of a closed torus in a smooth
  affine group over a field is smooth (Milne, Corollary 13.10, printed
  p.257, one-based PDF p.273).
- `CentralMaximalTorusBaseChangeStatement.{u}`: the forward implication
  for a central maximal torus (Milne, Theorem 17.82, central case).

Neither premise is proved here. The reduction is the first step of
Milne's own proof of 17.82, which replaces `G` by `C_G(T)`, a smooth
group in which `T` is central and still maximal.

## Base change of torus centralizers

`torusCentralizer_baseChange` shows, for any morphism of schemes
`b : S' ⟶ S`, that the centralizer of the base-changed homomorphism
`i_{S'} : T_{S'} ⟶ G_{S'}` equals the published base change
`(torusCentralizer i).baseChange b`. A point of `G_{S'}` over an
`S'`-scheme `T'` corresponds, under `baseChangePointsEquiv`, to a point of
`G` over `T'` viewed as an `S`-scheme. By
`mem_torusCentralizer_iff_universal` both memberships say that the point
commutes with the universal point of `T` (resp. `T_{S'}`) after pulling back
to `T' × T` (resp. `T' × T_{S'}`). The isomorphism
`Dynamic.mapTensorPullbackIso` identifies these two products, and the
private lemma `commute_iso_comp_iff` (precomposition with an isomorphism
preserves and reflects commutation) together with the injective group
homomorphism `baseChangePointsEquiv` and `commute_map_iff` transfers the
commutation.

## Proof of the reduction

`maximalTorusBaseChangeForwardReduction` proves the reduction statement.
Let `i : T ⟶ G` be a maximal torus over `k`, so `T` is a torus and `i` is
a closed subgroup.

1. The published `fieldCentralizerRepresentability` gives a closed
   subgroup `c : C ⟶ G` representing `torusCentralizer i`. The smoothness
   premise makes `C` smooth, and `C` is affine because `c` is a closed
   subgroup of an affine group.
2. The published `torusCentralizerFactor i hc : T ⟶ C` is central
   (`isCentral_torusCentralizerFactor`) and maximal
   (`IsMaximalTorus.isMaximalTorus_torusCentralizerFactor`). The central
   premise, applied to `C`, makes its base change `T_K ⟶ C_K` maximal.
3. The base change `i_K` is a closed torus by `IsTorus.baseChange` and
   `IsClosedSubgroup.baseChange`. For maximality, let `i' : T' ⟶ G_K` be a
   closed torus and `f : T_K ⟶ T'` with `f ≫ i' = i_K`. Base change of
   represented subgroups (`IsRepresentedBy.baseChange`) and
   `torusCentralizer_baseChange` show that `c_K` represents the centralizer
   of `i_K`. The range of `i'` lies in that centralizer: `T'` is
   commutative and `i_K` factors through `i'`, so
   `range_le_torusCentralizer` applies. Hence `i'` factors as
   `i'_C ≫ c_K` (`factorHom`), and `i'_C` is a closed subgroup by
   `IsClosedSubgroup.of_comp`. Since `c_K` is a monomorphism on points
   (`IsRepresentedBy.hom_ext`), `f ≫ i'_C` is the base change of
   `torusCentralizerFactor i hc`. Maximality of the latter in `C_K` then
   makes `f` an isomorphism.
