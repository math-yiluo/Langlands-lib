# Pushout-side facts for finite-set affine neighborhoods

This helper module collects the pushout-side steps of the proof that finite
pinching preserves finite-set affine neighborhoods
(`Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutStatement`).
The declarations live in the namespace
`Langlands.AlgebraicGeometry.FinitePinching`. Throughout, `i : Z ⟶ X`,
`j : Z ⟶ Y`, `a : X ⟶ P` and `b : Y ⟶ P` are actual morphisms of
`Scheme.{u}`. `PointTopology.HasFiniteAffineNeighborhoods S` is the Library
property that every finite set of points of `S` is contained in an affine open.

The module does not prove the target statement by itself. The final assembly
takes two inputs as explicit hypotheses, `hpair : HasCompatibleAffinePairs i j`
and `hchart : HasAffineCharts i j a b`, for the two predicates defined below.

## Provenance

This is derived work following the first paragraph of the proof of Theorem
5.4(a) in Ferrand, *Conducteur, descente et pincement* (2003), printed
pp. 570–571 (one-based PDF pages 18–19), registered as
`ferrand-conducteur-descente-pincement-2003`.

There, the ringed-space pushout `X` of `X' ← Y' → Y` is shown to satisfy (AF)
as follows:

1. A finite set `E` is split into its trace `F` on `Y` and the rest, which is
   identified with a finite set `E'` of `X' − Y'`.
2. Affine opens `V ⊇ F` and `U' ⊇ E' ∪ g⁻¹(F)` are found with
   `g⁻¹(V) = U' ∩ Y'`.
3. Ferrand's Theorem 5.1 then identifies the affine scheme
   `Spec(Γ(V) ×_{Γ(U'∩Y')} Γ(U'))` with an open of `X` containing `E`.

`hasFiniteAffineNeighborhoods_of_compatibleCharts` formalizes the reduction
from (AF) on the pushout to steps 2 and 3, with the roles of the letters
changed. Ferrand's `X'`, `Y'`, `Y` and `X` are `X`, `Z`, `Y` and `P` here, and
Ferrand's `f` and `u` are `a` and `b`. Step 2 is the hypothesis `hpair`;
step 3 is the hypothesis `hchart`. The two predicates
`HasCompatibleAffinePairs` and `HasAffineCharts` name exactly these two inputs.

Ferrand works with the ringed-space pushout, where the description of points
is immediate. Here `P` is an arbitrary scheme pushout. The joint surjectivity
of the legs (`closure_range_union_closure_range_eq_univ`,
`mem_range_or_mem_range_of_isPushout`) is therefore an internal derivation
from the universal property in schemes and does not appear in Ferrand.

The following are internal infrastructure that adapts the statements to the
Library's formulation:

- `hasFiniteAffineNeighborhoods_of_iso`;
- `exists_affineOpen_fibre`;
- `exists_eq_of_isPullback`;
- `hasFiniteAffineNeighborhoods_of_model`;
- `isAffine_of_isPushout`.

## Definitions

`HasCompatibleAffinePairs i j` (for `i : Z ⟶ X`, `j : Z ⟶ Y`) is the
proposition: for all finite sets `E ⊆ X` and `F ⊆ Y` with `E` disjoint from
`Set.range i`, there are affine opens `U` of `X` and `V` of `Y` with `E ⊆ U`,
`F ⊆ V` and `i ⁻¹ᵁ U = j ⁻¹ᵁ V`. This is the conclusion of step 2 above
(Ferrand: `F ⊂ V`, `E' ∪ g⁻¹(F) ⊂ U'`, `g⁻¹(V) = U' ∩ Y'`; the inclusion of
the image of `j ⁻¹' F` in `U` follows from the equality of inverse images).

`HasAffineCharts i j a b` (for a further `a : X ⟶ P`, `b : Y ⟶ P`) is the
proposition: for all affine opens `U` of `X` and `V` of `Y` with
`i ⁻¹ᵁ U = j ⁻¹ᵁ V`, there is an affine open `W` of `P` with `U ≤ a ⁻¹ᵁ W`
and `V ≤ b ⁻¹ᵁ W`. This is the part of step 3 that the assembly uses: Ferrand
identifies the affine pushout of such a pair with an open `W` of the pushout,
whose inverse images are then `U` and `V`. Only the inclusions are required
here.

## Theorems

`hasFiniteAffineNeighborhoods_of_iso e h`: if `e : P₀ ≅ P` and `P₀` has
finite-set affine neighborhoods, so does `P`. A finite set `S ⊆ P` has finite
image under `e.inv`; the preimage under `e.inv` of an affine open of `P₀`
containing that image is affine (`IsAffineOpen.preimage_of_isIso`) and
contains `S`.

`exists_affineOpen_fibre i j hX y`: for `[IsFinite j]` and `X` with finite-set
affine neighborhoods, every `y : Y` has an affine open `U` of `X` with
`i z ∈ U` for every `z : Z` with `j z = y`. This is exactly the fibre
hypothesis of `IntegralSchemePushoutStatement`. The fibre `j ⁻¹' {y}` is
finite (`Scheme.Hom.finite_preimage_singleton`), so its image under `i` is a
finite subset of `X`.

`exists_eq_of_isPullback h x y hxy`: for `h : IsPullback i j a b` and points
`x : X`, `y : Y` with `a x = b y`, there is `z : Z` with `i z = x` and
`j z = y`. It uses `Scheme.Pullback.exists_preimage_pullback` and the
isomorphism `h.isoPullback`.

`closure_range_union_closure_range_eq_univ h`: for `h : IsPushout i j a b`
with `a` and `b` quasi-compact, the closures of `Set.range a` and
`Set.range b` cover `P`. The proof works as follows.

1. Let `I = a.ker * b.ker` be the product of the kernel ideal sheaves. Since
   `I ≤ a.ker` and `I ≤ b.ker`, both legs factor through the closed subscheme
   `I.subscheme`, via `a.toImage ≫ inclusion` and `b.toImage ≫ inclusion`.
2. These factorizations agree on `Z`, because `I.subschemeι` is a
   monomorphism.
3. The pushout property then yields a section `P ⟶ I.subscheme` of
   `I.subschemeι`. Hence `I.subschemeι` is surjective.
4. Its range is the support of `I`. That support is the union of the supports
   of `a.ker` and `b.ker`, which are the closures of the ranges
   (`Scheme.Hom.support_ker`, using quasi-compactness).

`mem_range_or_mem_range_of_isPushout h ha hb p`: if moreover `a` and `b` are
closed maps, every `p : P` lies in `Set.range a` or in `Set.range b`. The
ranges are then closed, so the previous result applies.

`hasFiniteAffineNeighborhoods_of_compatibleCharts hw hsurj hpair hchart`: the
final assembly. It assumes:

- `i ≫ a = j ≫ b`;
- every point of `P` lies in the range of `a` or of `b`;
- `hpair : HasCompatibleAffinePairs i j`;
- `hchart : HasAffineCharts i j a b`.

Under these hypotheses `P` has finite-set affine neighborhoods. Given a finite
`S ⊆ P`, each point in the range of `b` gets a chosen preimage in `Y`, which
forms `F`. Each remaining point gets a chosen preimage in `X`, which forms
`E`. `E` is disjoint from the range of `i`, since `a (i z) = b (j z)`. Applying
`hpair` and then `hchart` gives `W`, and each point of `S` lies in `W` through
its chosen preimage.

`hasFiniteAffineNeighborhoods_of_model hpair h₀ hchart h` transfers the
property between pushouts of the same span. Its inputs are:

- `hpair : HasCompatibleAffinePairs i j`;
- a model pushout `h₀ : IsPushout i j a₀ b₀` with `[IsIntegralHom a₀]` and
  `[IsClosedImmersion b₀]`;
- `hchart : HasAffineCharts i j a₀ b₀`.

From these, every scheme pushout `h : IsPushout i j a b` of the same span has
finite-set affine neighborhoods. The joint surjectivity for the model comes
from `mem_range_or_mem_range_of_isPushout`: integral morphisms and closed
immersions are quasi-compact and universally closed, hence closed maps. The
assembly then applies to `P₀`, and the result transfers along
`h₀.isoIsPushout _ _ h`.

`isAffine_of_isPushout hA h`: assume `AffineSchemePushoutStatement.{u}` as the
hypothesis `hA` (not proved here). Then a scheme pushout
`h : IsPushout i j a b` with `[IsClosedImmersion i]`, `X` and `Y` affine has
`P` affine. The proof runs as follows.

1. `Z` is affine and `i.appTop` is surjective
   (`IsClosedImmersion.isAffine_surjective_of_isAffine`).
2. `hA`, applied to the ring pullback of `i.appTop` and `j.appTop`, gives a
   pushout square with corner `Spec` of the pullback ring.
3. Transported along `Scheme.isoSpec`, it is a pushout of `i` and `j`.
4. The comparison isomorphism with `P` then shows that `P` is affine.
