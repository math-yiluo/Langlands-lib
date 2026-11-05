# Proof of existence of the actual maximal-torus parameter scheme

Author: Worker 1534.

This module proves the published proposition
`Langlands.GroupScheme.MaximalTorusParameterExistenceStatement.{u}` from
`Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceStatement`, in
arbitrary universe `u`. The main theorem is
`Langlands.GroupScheme.maximalTorusParameterExistence`. It depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement module is imported unchanged. The proof keeps every field `k`,
every group scheme `G` over `Spec k` with smooth affine structure map and
connected underlying space, and every maximal torus `j₀ : T₀.toGrp ⟶ G`. It
adds no hypothesis. The connectedness instance is part of the statement but the
proof never uses it. The proof also uses only two parts of maximality: `T₀` is
a torus (`hmax.1`) and `j₀` is a closed subgroup (`hmax.2.1`).

## The parameter scheme and the projection

1. The published theorem `torusNormalizerSmoothClosed`
   (`Torus.NormalizerSmoothProof`) is applied to `G`, `T₀` and `j₀`. It gives
   a smooth group scheme `H` over `Spec k` and a closed subgroup `i : H ⟶ G`
   that represents `torusNormalizer j₀`: `i.hom.hom` is a monomorphism and
   `SubgroupFunctor.range i = torusNormalizer j₀`.
2. The published theorem `smoothSubgroupQuotientExistence`
   (`HomogeneousQuotientProof`) is applied to `G`, `H` and `i`. It gives the
   actual `Q : Over (Spec k)` and `q : G.X ⟶ Q` used in the conclusion.
   `Q.hom` is separated, locally of finite type and quasi-compact. `q.left` is
   smooth, surjective and quasi-compact. For every test `U` and all
   `g h : U ⟶ G.X`, `g ≫ q = h ≫ q` holds iff
   `g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier U`.
3. Rewriting with `SubgroupFunctor.range i = torusNormalizer j₀` turns this
   into the exact right-normalizer-coset fiber condition of
   `IsMaximalTorusParameter`, on all scheme tests.
4. Smoothness of `Q.hom`: `Over.w q` gives `q.left ≫ Q.hom = G.X.hom`, which is
   smooth. Since `q.left` is smooth, surjective and quasi-compact, the
   published theorem
   `AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`
   (imported from the Anthropic FLT theorem module of the same name) gives
   `Smooth Q.hom`. That theorem also needs `LocallyOfFinitePresentation Q.hom`.
   Instance search derives it from `LocallyOfFiniteType Q.hom`, because the
   base `Spec k` is Noetherian.

The theorem returns these `Q` and `q` with every conjunct of
`IsMaximalTorusParameter j₀ q`. The last conjunct is
`conjugationCompatible_of_fiber` below, applied to the forward direction of the
fiber condition.

## Ground-field torus compatibility

`MaximalTorusParameterExistence.conjugationCompatible_of_fiber` proves
`TorusParameterConjugationCompatible j₀ q` for any `q : G.X ⟶ Q`, given that
`T₀` is a torus, `j₀` is a closed subgroup, `G` is affine over `k`, and every
pair `a₁ a₂ : U ⟶ G.X` with `a₁ ≫ q = a₂ ≫ q` satisfies
`a₁⁻¹ * a₂ ∈ (torusNormalizer j₀).carrier U`. Write `K = AlgebraicClosure k`
and `b = toAlgebraicClosure k`, and fix a rational point `x` of `Q`. The
torus is chosen after `x` and before the quantifier over `g`, which is the
quantifier order of the definition.

First, a short computation (`hleft`) uses `geometricRationalPoint_fst`. It
shows that if `g ≫ (Over.pullback b).map q = geometricRationalPoint Q x`, then
the ground point `g.left ≫ pullback.fst G.X.hom b` of `G` maps under `q.left`
to `b ≫ x.left`.

The proof then splits on whether some `K`-point `g` of `G_K` lies over the
extended parameter.

- **No lift.** The universally quantified implication is vacuous, and the
  proof takes `T₀` and `j₀` themselves.
- **A lift `g` exists.** Let `i := (baseChange b).map j₀ ≫ (innerIso g).hom`,
  the base change of the torus followed by the inner automorphism of `G_K`
  defined by `g`. It is a closed subgroup by `IsClosedSubgroup.baseChange` and
  `IsClosedSubgroup.comp_iso`. The lemma `overlap_range_eq` shows that its
  range is invariant on the fpqc overlap. The published
  `IsClosedSubgroup.exists_descent_of_overlap_range_eq`
  (`Descent.ClosedSubgroups`) then gives an actual closed subgroup
  `j : H₀ ⟶ G` over `k`, an isomorphism `e : (baseChange b).obj H₀ ≅ T₀_K`, and
  `(baseChange b).map j = e.hom ≫ i`. The base field is affine and flat
  surjective over `k` by `fieldExtension_fpqc`, and `G.X.left` is affine by
  `isAffine_of_isAffineHom`. `H₀` is a torus by
  `IsTorus.of_baseChange (IsTorus.of_iso e (hT₀.baseChange))`. Its
  commutativity instance `hH.isCommMonObj` makes it the commutative group
  scheme `{ H₀ with comm := hH.isCommMonObj }`.
  For any other lift `g'`, `SubgroupFunctor.range_iso_comp` reduces
  `range ((baseChange b).map j)` to `range i`. Then
  `range_conj_eq_of_mem_torusNormalizer` reduces the equality of the
  `g`-conjugate and the `g'`-conjugate to the fact that the two ground points
  differ by a normalizer point. That fact follows from the fiber hypothesis,
  because both ground points map to `b ≫ x.left` by `hleft`.

## Helper lemmas

All helpers are in namespace
`Langlands.GroupScheme.MaximalTorusParameterExistence`.

- `conj_mem_iff_of_inv_mul_mem_normalizer`: if `a₁⁻¹ * a₂` lies in the
  normalizer of a subgroup functor `F`, then `a₁⁻¹ * z * a₁ ∈ F` iff
  `a₂⁻¹ * z * a₂ ∈ F`. Proof: the identity
  `a₂⁻¹ z a₂ = (a₁⁻¹a₂)⁻¹ (a₁⁻¹ z a₁) (a₁⁻¹a₂)`, together with both clauses of
  normalizer membership at the identity refinement.
- `mem_range_comp_innerIso_iff`: `y` lies in the range of
  `f ≫ (innerIso g).hom` iff `g⁻¹ y g` (with the constant point of `g`) lies in
  the range of `f`. It uses the published `comp_innerIso_hom`.
- `mem_range_comp_iso_iff`: `y` lies in the range of `f ≫ e.hom` iff
  `y ≫ e.inv` lies in the range of `f`.
- `baseMap`, `baseChangePointsEquiv_constantPoint_eq`: under
  `baseChangePointsEquiv`, the constant family of a base-changed point `g` is
  the ground point of `g` restricted along the structure map of the test. This
  is `baseChangePointsEquiv_naturality`.
- `mem_range_baseChange_comp_innerIso_iff`: membership in the range of
  `(baseChange b).map j ≫ (innerIso g).hom`, written on ground points. It
  combines the two lemmas above with `SubgroupFunctor.range_baseChangeHom` and
  `SubgroupFunctor.mem_baseChange`.
- `range_conj_eq_of_mem_torusNormalizer`: if the ground quotient
  `g₁⁻¹ g₂` of two base-changed points lies in `torusNormalizer j`, then the
  `g₁`-conjugate and the `g₂`-conjugate of the base-changed torus have the same
  range on every test.
- `overlap_range_eq`: this is the descent hypothesis for the conjugated torus
  `i`. Suppose `g`'s ground point maps to `b ≫ x` under `q.left` and parameter
  fibers lie in normalizer cosets. Then the ranges of the two pullbacks of `i`
  to `K ⊗_k K` agree after the canonical overlap isomorphism. On each test `V`
  the two memberships become conjugation conditions for two ground points of
  `G`. The proof identifies the two test objects over `Spec k` by an `Over`
  isomorphism `w`, using `pullback.condition`, and transports range membership
  along it. It matches the conjugated points using `canonicalOverlap_fst`. Both
  conjugating ground points lie over the same parameter, so the fiber
  hypothesis and `conj_mem_iff_of_inv_mul_mem_normalizer` finish the proof.

## Relation to the literature

The statement's Markdown cites SGA3, Exposé XII, Théorème 1.7 and
Corollaire 1.10, and Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.,
proof of Proposition A.2.11, which identify the scheme of maximal tori with
`G/N_G(T₀)`. The implemented route differs from those sources. It does not
build a universal torus over `Q`. It takes `Q = G/N_G(T₀)` from the published
smooth homogeneous-quotient theorem. It then obtains the ground-field torus
for each rational parameter by fpqc descent from `AlgebraicClosure k`, using
the published closed-subgroup descent theorem. Overlap invariance and
independence of the lift both come from the fact that two lifts differ by a
normalizer point.
