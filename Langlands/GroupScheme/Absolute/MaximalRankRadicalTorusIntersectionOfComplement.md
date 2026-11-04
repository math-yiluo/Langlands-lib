# Radical torus intersections from a unipotent-by-torus decomposition

Worker 1496. This module composes published Library results. It proves
`MaximalRankRadicalTorusIntersectionStatement` from four structural premises,
which stay explicit hypotheses of the final theorem. It does not prove the
proposition unconditionally. Accepting this module discharges none of the
premises and does not complete the proof task for the target.

## Declarations

- `SubgroupFunctor.IsRepresentedBy.conjugateIso hr hn g : R ≅ R`. Let `r : R ⟶ P`
  represent a normal subgroup functor `F` of `P`, and let `g` be a base point of `P`.
  This is the automorphism of the representative `R` given by conjugation by `g`. Its
  hom and inverse are the published factorizations `hr.conjugateFactor hn (𝟙 R) g`
  and `hr.conjugateFactor hn (𝟙 R) g⁻¹`. The inverse laws follow from
  `conjugateFactor_comp`, from `innerIso_inv_hom`, and from `hr.hom_ext`, which says
  that `r` is a monomorphism.
- `conjugateIso_hom_comp`: `(hr.conjugateIso hn g).hom ≫ r = r ≫ (P.innerIso g).hom`.
- `conjugateFactor_eq_comp_conjugateIso`: every factorization
  `hr.conjugateFactor hn b g` equals `b ≫ (hr.conjugateIso hn g).hom`. The proof uses
  the published uniqueness `conjugateFactor_unique`.
- `IsClosedSubgroup.isRepresentedBy_range`: a closed subgroup `i` over a field
  represents its own range. A closed immersion is a monomorphism of schemes, and
  `Over.mono_of_mono_left` makes it a monomorphism over the base.
- `exists_radicalTorusIntersection_of_complement`, the core local result, described
  below.
- `maximalRankRadicalTorusIntersectionStatement_of_complement`, the assembly of the
  target proposition from the four premises.

## The core local result

Work over a field `k`. Let `H` be affine and locally of finite type, and suppose its
maximal tori are conjugate (`MaximalToriAreConjugate H`). Let `f : T → H` be a maximal
torus with `T` split. Let `r : R → H` be a closed subgroup whose range is normal on
every test scheme. Assume `hcomp`: for every maximal torus `s : S → R` there is a
closed subgroup `u : U → R` with `U` unipotent such that
`subgroupMultiplication u s : U × S → R`, `(n, x) ↦ n * x`, is an isomorphism of
schemes. Assume also the global premise `UnipotentClosedSubgroupStatement`.

Under these hypotheses the theorem gives a commutative group scheme `S`, a closed
subgroup `sT : S → T` and a maximal torus `sR : S → R` with `sT ≫ f = sR ≫ r`. It
also gives `range (sT ≫ f) = range f ⊓ range r` as subgroup functors, that is, on
every test scheme over `k`.

The Lean proof runs as follows.

1. `exists_isMaximalTorus` gives a maximal torus `s₀ : S₀ → R`; `R` is affine and
   locally of finite type because it is closed in `H`. The composite `s₀ ≫ r` is a
   closed torus of `H`. `exists_maximalTorus_extension_of_finiteType` puts it inside a
   maximal torus `t₁ : T₁ → H`, with `a ≫ t₁ = s₀ ≫ r`.
2. Conjugacy in `H` gives a base point `g` and an isomorphism `e : T₁ ≅ T` with
   `t₁ ≫ int(g) = e ≫ f`.
3. Since the range of `r` is normal and represented by `r`, conjugation by `g`
   restricts to the automorphism `c := conjugateIso` of `R`. Set `sR := s₀ ≫ c` and
   `sT := a ≫ e`. Then `sR` is a maximal torus by `IsMaximalTorus.comp_iso`.
   A short computation gives `sT ≫ f = s₀ ≫ r ≫ int(g) = sR ≫ r`. The map `sT` is
   closed by `IsClosedSubgroup.of_comp`, since `f` and `sR ≫ r` are closed.
4. Trivial intersection. Let `u : U → R` be the complement that `hcomp` gives for
   `sR`. The scheme intersection `W := subgroupIntersection f (u ≫ r)` maps to `U` by
   a closed immersion, the base change of the closed immersion `f`. So
   `UnipotentClosedSubgroupStatement` makes `W` unipotent. Its projection to the
   split torus `T` is therefore trivial on points, by
   `IsUnipotent.comp_eq_one_of_isSplitTorus`. Using `range_subgroupIntersectionHom`,
   every test point in both `range f` and `range (u ≫ r)` equals `1`.
5. Range equality. The inclusion `range (sT ≫ f) ≤ range f ⊓ range r` holds because
   `sT ≫ f = sR ≫ r`. Conversely, let a test point `x` lie in `range f` and in
   `range r`, say `x = z ≫ r`. Write `w := z ≫ (subgroupMultiplication u sR)⁻¹`. Then
   `x = n * t`, where `n` is the `U`-component of `w` composed with `u ≫ r` and `t` is
   the `S`-component of `w` composed with `sT ≫ f`. Here `t ∈ range f`, so
   `n = x * t⁻¹` lies in both `range f` and `range (u ≫ r)`. Step 4 then gives `n = 1`,
   so `x = t ∈ range (sT ≫ f)`.

The proof never uses smoothness or connectedness of `H` or `R`. They enter only
through the premises: conjugacy of maximal tori of `H`, and `hcomp` for `R`.

## Assembly of the target proposition

`maximalRankRadicalTorusIntersectionStatement_of_complement` takes four premises:

- `MaximalTorusConjugacyStatement.{u}`, conjugacy of maximal tori in smooth connected
  affine groups over algebraically closed fields (Milne 2017, Theorem 17.10, as
  formalized in `Absolute/BorelStatement.lean`);
- `UnipotentClosedSubgroupStatement.{u}`;
- `TorusFiniteGaloisSplittingStatement.{u}`;
- `hcomp`, stated inline. Over every algebraically closed field `k`, let `R` be a
  smooth, affine, connected and solvable group, and let `s : S → R` be a maximal
  torus. Then there is a closed unipotent `u : U → R` with
  `IsIso (subgroupMultiplication u s)`.

From these it proves the published proposition
`MaximalRankRadicalTorusIntersectionStatement.{u}` exactly. Given the target's data
`G`, `j : H → G`, `t`, `f` with `f ≫ j = t`, and `r` with `IsSolvableRadical r`, the
proof runs as follows:

- `H` is affine because it is closed in the affine group `G`;
- `f` is a maximal torus of `H` by `IsMaximalTorus.of_comp`;
- `T` is split by `IsTorus.isSplitTorus_of_finiteGaloisSplitting`;
- `R` is smooth, connected, affine, solvable and normal, by the fields of
  `IsSolvableRadical`;
- the core result above applies.

The proof uses neither the reductivity of `G` nor the maximality field `greatest` of
`IsSolvableRadical`.

## Provenance

This is derived content: an internal composition of Library results. The inline
premise `hcomp` is the decomposition `H = H_u ⋊ T` of Milne 2017, Theorem 16.33(d),
printed pp.335–336, with factor order `(n, t)`. That reference is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. It is weaker
than the separately staged proposition `SolvableMaximalTorusSemidirectStatement`,
which also asserts smoothness, connectedness, normality and maximality of `U`. The
module does not import that proposition. The argument follows the classical
pattern: conjugate a maximal torus of the radical into the given maximal torus, then
use that a torus and a unipotent group intersect trivially. Here it is carried out on
all test schemes rather than on geometric points.
