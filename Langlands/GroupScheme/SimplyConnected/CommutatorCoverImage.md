# Commutators lift to the simply connected cover of the derived subgroup

This module proves that, for a connected reductive group `G` over a field `k`, the commutator
of any two points of `G` is the image of a point of the simply connected cover of the derived
subgroup. Precisely, `IsSimplyConnectedDerivedCover.exists_comp_eq_commutator` states the
following. Let `h : IsSimplyConnectedDerivedCover d π`, with `d : D ⟶ G` the derived subgroup
and `π : C ⟶ D` its simply connected central cover. Then for every test object `T` over
`Spec k` and all `x y : T ⟶ G.X` there is `c : T ⟶ C.X` with

    c ≫ (π ≫ d).hom.hom = x * y * x⁻¹ * y⁻¹.

For `T = Spec k` this says that every commutator of `G(k)` lies in `G(k)^♮`, the image of
`G_sc(k) → G(k)` (KP Definition 2.6.20). Points over an arbitrary `T` are allowed, so no
reducedness or separability hypothesis on the base field is needed.

## The central product `R × C → G`

The published `reductiveCentralTorusSurjectivity` supplies a closed central torus
`i : R ⟶ G`, affine and locally of finite type, for which the multiplication map
`subgroupProductMap i d : R × D ⟶ G` is surjective on underlying schemes. The supplied derived
subgroup `d` itself is used; no other representative is chosen.

`CommutatorCoverImage.coverMultiplication i hi` is the homomorphism `R × C ⟶ G`,
`(r, c) ↦ i(r) · d(π(c))`. It is the published `commutingSubgroupMultiplicationHom`, which
applies because `i` is central (`commute_of_isCentral`). The proof establishes the hypotheses of
the published `CommutatorDescent` for this homomorphism `q`.

* **Surjectivity.** The underlying map of `q` factors as `(R ◁ π)` followed by
  `subgroupProductMap i d`. The first map is a base change of the surjective `π` (a central
  isogeny), so it is surjective by `MorphismProperty.pullbackMap`. The second map is
  surjective by the choice of `R`.
* **Flatness.** The published `subgroupMultiplication_flat_of_surjective` gives flatness. Its
  inputs are that `R` and `C` are quasi-compact and locally of finite type, that `G` is smooth,
  that the two factors commute, and the surjectivity just shown.
* **Quasi-compactness.** `R × C` and `G` are affine schemes, so `q` is quasi-compact.
* **Central kernel** (`isCentral_kernel_coverMultiplication`). Let `(r, c)` be a `T`-point of
  the kernel. Then `d(π(c)) = i(r)⁻¹` is central in `G`. For every later point `c'` of `C`, the
  commutator `c c' c⁻¹ c'⁻¹` therefore maps to `1` in `G`, so it lies in the kernel of `π`
  (`IsSimplyConnectedDerivedCover.comp_eq_one_iff`, as `d` is a monomorphism). That kernel is
  central because `π` is a central isogeny. Thus every commutator with `c` is central. The
  cover `C` is connected reductive, so the published
  `SecondCenter.secondCenterTrivial_of_centralDerivedProduct` puts `c` in the centre of `C`.
  The `R`-component is central since `R` is commutative. A point of `R × C` whose two
  components are central is central, by comparing both projections with
  `CartesianMonoidalCategory.hom_ext`.

## Descent of the commutator

`CommutatorDescent.hom q hq : G × G ⟶ R × C` sends `(q a, q b)` to the commutator of `a` and
`b` in `R × C`. Its composite with `q` is the commutator morphism of `G`
(`CommutatorDescent.hom_comp`). Its `R`-component is trivial: after precomposition with the
epimorphism `q × q`, it is the `R`-component of the commutator in `R × C`. That component is a
commutator in the commutative group `R`, so it equals `1`. Cancelling the epimorphism
(`CommutatorDescent.epi_tensorHom`) gives `φ ≫ fst = 1`.

For `x y : T ⟶ G.X`, put `c = lift x y ≫ φ ≫ snd`. Then
`x * y * x⁻¹ * y⁻¹ = lift x y ≫ φ ≫ q = i(1) · d(π(c)) = d(π(c))`, which is the claim.

## Provenance

This is internal derived content. The fact itself is classical: the commutator morphism
of a connected reductive group factors through its simply connected cover, so `G(k)/G(k)^♮` is
abelian. The proof here is assembled only from the published Library results named above:
central torus surjectivity, flatness of commuting multiplication, commutator descent through a
homomorphism with central kernel, and triviality of the second centre of connected reductive
groups. The module asserts nothing about local fields or buildings. Its consumer
`Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality` uses it to prove normality of
`G(F)^0` (part of KP Lemma 2.6.24) without the independence of choices in KP Lemma 2.6.24.
