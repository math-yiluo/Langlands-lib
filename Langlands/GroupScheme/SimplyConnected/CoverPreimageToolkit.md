# Torus centralizers, character descent and maximal tori: general helpers

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit`. Internal
helpers for the reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
They are derived from published Library interfaces and assert nothing from the
literature. All declarations are in namespace `Langlands.GroupScheme`.

## Over an arbitrary base scheme `S`

- `torusCentralizer_comp_of_fpqc`. Let `T₁`, `T₂` be commutative group
  schemes, `q : T₁ ⟶ T₂` a homomorphism whose underlying morphism is
  quasi-compact, flat and surjective, and `x : T₂ ⟶ G` a homomorphism. Then
  `torusCentralizer (q ≫ x) = torusCentralizer x` as subgroup functors of `G`.
  One inclusion composes test points with `q`. For the other, take a test point
  `s : V ⟶ T₂` and pull `q` back along `s`. This gives a quasi-compact,
  flat, surjective `w : W ⟶ V` and a point `r` of `T₁` with
  `w ≫ s = r ≫ q`. Such a `w` is an epimorphism over `S`. The required
  commutation holds after `w`, so it holds over `V`. This is the refinement
  step of the published `IsCentralIsogeny.mem_torusCentralizer_iff`.
- `torusCentralizer_eq_of_hom_eq_mul_central`. If
  `y.hom.hom = c * x.hom.hom` for a morphism `c : T.X ⟶ G.X` whose points all
  lie in the centre of `G`, then `torusCentralizer y = torusCentralizer x`.
- `torusCentralizer_comp_comap_of_mono`. For a homomorphism `d : H ⟶ G` with
  monomorphic underlying morphism,
  `(torusCentralizer (x ≫ d)).comap d = torusCentralizer x`.
- `rationalCharacters.comp_nsmul`: on points, `n • χ` takes `n`-th powers.
- `exists_characterRestrict_eq_nsmul_of_fpqc`. Let `q : H ⟶ Q` be quasi-compact,
  flat and surjective, and let `N` kill every point `x` of `H` with
  `x ≫ q = 1`. Then for every `χ : rationalCharacters H` there is
  `ψ : rationalCharacters Q` with `characterRestrict q ψ = N • χ`. The
  character `N • χ` kills the scheme-theoretic kernel, because the universal
  kernel point is killed by `N`. The published `FpqcHomDescent.hom`
  (module `Langlands.GroupScheme.HomDescent`) descends it through `q`.
- `IsCentralFppfCover q` is a structure on a homomorphism `q : H ⟶ Q`. Its
  fields say that the underlying morphism is quasi-compact, flat, surjective
  and locally of finite presentation, that every point killed by `q` lies in
  the centre of `H`, and that some positive integer `N` kills every point
  killed by `q`. A central isogeny over a field has these properties
  (`CoverPreimage.isCentralFppfCover_of_isCentralIsogeny`, in
  [`CoverPreimageCharacters`](CoverPreimageCharacters.md)).
  `IsCentralFppfCover` does not require finiteness.
- `IsCentralFppfCover.of_isPullback`. Let `i ≫ q = p ≫ j` be a commutative
  square of homomorphisms with `i` monomorphic. If the underlying square of
  schemes is cartesian and `q` is a central fppf cover, then so is `p`. The
  four morphism properties are stable under base change. A point killed by
  `p` maps under `i` to a point killed by `q`, and `i` reflects centrality
  and torsion.

## Over a field

- `IsMaximalTorus.exists_factor_of_commute`. Let `M` be smooth and affine, let
  `j : T ⟶ M` be a maximal torus, `B` a torus and `b : B ⟶ M` a
  homomorphism whose values commute with those of `j`. Then `b` factors
  through `j`. The published `torusImageClosedTorusStatement` gives a closed
  torus `Z` of `M` through which the product homomorphism `B × T ⟶ M`
  factors. Since `j` factors through `Z`, maximality makes `T ⟶ Z` an
  isomorphism, and `b` factors through `Z ≅ T`. This is the torus version of
  the published `IsMaximalSplitTorus.exists_factor_of_commute`.
