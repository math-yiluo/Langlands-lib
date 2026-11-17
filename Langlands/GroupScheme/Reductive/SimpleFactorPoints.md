# Point-level helpers for the semisimple decomposition theorem

Author: Worker 161 (Task 6631, with Worker 162).

This module is an internal step toward the proof of
[`SimpleFactorDecompositionStatement`](SimpleFactorDecompositionStatement.md), Conrad's
decomposition theorem for semisimple groups (*Reductive group schemes*, Theorem 5.1.19). It
is not a formalization of a numbered result. It collects general facts about points of
group schemes, subgroup functors, fppf-type lifting and finite products that the companion
modules [`SimpleFactorPresentation`](SimpleFactorPresentation.md),
[`SimpleFactorCover`](SimpleFactorCover.md), [`SimpleFactorSubgroups`](SimpleFactorSubgroups.md)
and [`SimpleFactorDecompositionProof`](SimpleFactorDecompositionProof.md) use. All
declarations are in the namespace `Langlands.GroupScheme.SimpleFactor`. Unless stated
otherwise, group schemes are over an arbitrary base scheme `S : Scheme.{u}`, and test points
are morphisms `T ⟶ G.X` in `Over S`. "Range", "normal", `≤` and `⊥` refer to
`SubgroupFunctor.range`, `SubgroupFunctor.IsNormal` and the order on `SubgroupFunctor G`,
all of which are tested on every test scheme.

## Lifting along quasi-compact, flat, surjective morphisms

- `exists_refinement_lift m g`: for a morphism `m : P ⟶ G` in `Over S` whose underlying
  morphism is quasi-compact, flat and surjective, and a point `g : T ⟶ G`, there are
  `w : W ⟶ T` (quasi-compact, flat, surjective) and `z : W ⟶ P` with `w ≫ g = z ≫ m`.
  Proof: take `W` the fibre product of `g` and `m`; these properties are stable under base
  change.
- `effectiveEpi_comp_left w w'`: a composite of two such refinements is an effective
  epimorphism of schemes (Mathlib's fpqc instance on quasi-compact, flat, surjective
  morphisms, which are stable under composition).
- `commute_of_epi w h`: if `w ≫ x` and `w ≫ y` commute and `w.left` is an epimorphism,
  then `x` and `y` commute.
- `commute_of_lift m x h g`: for a quasi-compact, flat, surjective homomorphism
  `m : P ⟶ G`, a point `x` of `G` commutes with every point `g` over the same `T` if, after
  every refinement `w : W ⟶ T`, `w ≫ x` commutes with all points `z ≫ m` with `z` a point
  of `P`.
- `isNormal_range_of_lift m n h`: for such an `m` and a monomorphic homomorphism
  `n : N ⟶ G`, the range of `n` is normal if it is stable under conjugation by all points
  `z ≫ m`. Proof: lift the conjugating point along `m` after a refinement and descend
  membership with the published `SubgroupFunctor.mem_range_of_comp_mem_range`.

## Derived subgroups and central isogenies

- `comp_mem_derivedSubgroup φ hx`: a homomorphism `φ : H ⟶ G` sends points of
  `derivedSubgroup H` to points of `derivedSubgroup G`. Proof: pull back a closed subgroup
  of `G` containing all commutators along `φ` with the published
  `subgroupIntersectionFst`.
- `derivedSubgroup_pi_eq_top A hA`: a finite product `pi A` of groups with
  `derivedSubgroup (A i) = ⊤` has `derivedSubgroup (pi A) = ⊤`. Proof: every point of
  `pi A` is a finite product of points of the factors (published
  `pi_point_eq_coordinate_prod`), each in the derived subgroup by the previous item.
- `isPullback_id_tensorHom f Z`: `𝟙 Z ⊗ₘ f` is the base change of `f` along the second
  projection.
- `IsCentralIsogeny.id_tensor hf K`: if `f` is a central isogeny, so is `𝟙 K ⊗ₘ f`.
  Finiteness, flatness, surjectivity and local finite presentation come from the base
  change square. A kernel point has trivial `K`-coordinate and a `C`-coordinate in the
  kernel of `f`, hence is central.

## Commuting multiplication

For `j : H ⟶ G`, `i : K ⟶ G` with commuting points (`hc`):

- `comp_commutingSubgroupMultiplicationHom j i hc z`: the published multiplication
  `commutingSubgroupMultiplicationHom j i hc` sends a point `z` of `H ⊗ K` to
  `((z ≫ fst) ≫ j) * ((z ≫ snd) ≫ i)`.
- `isNormal_range_comp_left` and `isNormal_range_comp_right`: if this multiplication is
  quasi-compact, flat and surjective and `r : R ⟶ H` (or `r : R ⟶ K`) has normal range with
  `r ≫ j` (or `r ≫ i`) monomorphic, then the range of `r ≫ j` (or `r ≫ i`) is normal in
  `G`. Proof by `isNormal_range_of_lift`: conjugation by `(a ≫ j) * (b ≫ i)` acts on
  `R` through the factor containing it, since the other factor commutes with it.

## Commutants

- `commutant F`: for a subgroup functor `F` of `G`, the subgroup functor whose `T`-points
  are the `g : T ⟶ G.X` such that for every `a : T' ⟶ T` the restriction `a ≫ g` commutes
  with every `T'`-point of `F`. It is closed under restriction by construction. The
  definition is internal to this proof (the restriction condition makes it a subgroup
  functor). It is not the scheme-theoretic centralizer and is used only as a notation for
  "commutes with all points of `F`".
- `mem_commutant`, `commute_of_mem_commutant`, `le_commutant_comm` (`F ≤ commutant F'`
  implies `F' ≤ commutant F`), `commutant_anti` (the commutant reverses `≤`), and
  `range_le_commutant_iff n F` (the range of `n` lies in `commutant F` if and only if
  every `x ≫ n` commutes with every point of `F` over the same test scheme).
- `range_le_commutant_of_comp fac inc F h` and `range_le_of_comp_le fac inc n h`: for a
  quasi-compact, flat, surjective homomorphism `fac : P ⟶ B` and `inc : B ⟶ G`, if the
  range of `fac ≫ inc` lies in `commutant F` (or in the range of a monomorphic `n`), then
  so does the range of `inc`.
- `isNormal_range_of_image mul fac r hr inc h`: if `fac ≫ inc = r ≫ mul` with `mul` and
  `fac` quasi-compact, flat and surjective, `r` of normal range and `inc` monomorphic, then
  `inc` has normal range (the image of a normal subgroup under a flat surjection is
  normal).
- `range_comp_eq_of_range_eq inc h`, `range_comp_le_iff a b F`
  (`range (a ≫ b) ≤ F ↔ range a ≤ F.comap b`) and `range_comp_le_range a b`.
- `range_le_of_derivedSubgroup_eq_top n hK b hb h`: if `derivedSubgroup K = ⊤`, `b` is a
  closed subgroup of `G`, and `(x * y * x⁻¹ * y⁻¹) ≫ n` lies in the range of `b` for all
  points `x, y` of `K`, then the range of `n` lies in the range of `b`. Proof: the pullback
  of `b` along `n` is a closed subgroup of `K` containing all commutators, so it contains
  `derivedSubgroup K`.
- `commutator_mul_mul_eq g c h d hc hd`: in any group, `[g c, h d] = [g, h]` when `c`
  commutes with `h d` and `d` commutes with `g` (here `[x, y] = x y x⁻¹ y⁻¹`).

## Finite products

For a finite family `A : I → GroupScheme S` (with `I : Type u`), using the published
subproduct inclusion `piSubsetInclusionHom A s`, projection `piSubsetProjectionHom A s`
and factor inclusion `piFactorInclusionHom A i`:

- `range_piSubsetInclusionHom_comp_le_iff φ s F`: the range of
  `piSubsetInclusionHom A s ≫ φ` lies in `F` if and only if the ranges of
  `piFactorInclusionHom A i ≫ φ` do for all `i ∈ s`.
- `range_le_of_forall_factor φ F h`: the range of `φ : pi A ⟶ G` lies in `F` when the
  ranges of all `piFactorInclusionHom A i ≫ φ` do.
- `piSubset_points_mem`, `piSubset_points_notMem`, `pi_point_eq_mul_compl`: every point
  `u` of `pi A` is the product of its restriction to the coordinates in `s` and its
  restriction to the coordinates in `sᶜ`.
- `exists_mul_mem_range_piSubset φ s u`: hence `u ≫ φ = a * c` with `a` in the range of
  `piSubsetInclusionHom A s ≫ φ` and `c` in the range of `piSubsetInclusionHom A sᶜ ≫ φ`.
- `commute_piFactorInclusionHom A h x y`: points of distinct factors commute in `pi A`.
- `piFactorInclusionHom_comp_piSubsetInclusionHom A s i`: inserting the factor `i ∈ s`
  into the subproduct on `s` and then into `pi A` is inserting it into `pi A`.

## Provenance

All results are standard facts about group functors and fppf-type descent, stated and
proved here because the decomposition proof needs them in the Library's point-based
language. The module proves nothing about semisimple groups. It imports the published
modules `Reductive.CommutingMultiplication`, `SubgroupFunctor.FpqcDescent`,
`SubgroupIntersectionKernelComparison`, `Derived.Basic`,
`SimplyConnected.AlmostSimpleSubproducts`, `SimplyConnected.DirectFactors` and Mathlib's
`AlgebraicGeometry.Sites.Fpqc`.
