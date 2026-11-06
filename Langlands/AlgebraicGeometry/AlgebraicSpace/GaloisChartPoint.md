# Galois points of étale charts over a field

Internal infrastructure for the proof of `RationalPointEtaleLiftStatement` (Knutson,
*Algebraic Spaces*, II.6.4; Stacks Project, Tag 0BBP). The module collects three standard
steps of the Galois-descent argument. The rest of the argument (fibre powers of the chart,
the Galois twist, the quotient by the finite group action, and the final assembly) lives in
other modules. All statements are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint`. Throughout, `k` is a field
and `Spec k` means `Spec (CommRingCat.of k)`.

## Statements

- `exists_galois_of_separable`: a finite separable extension `L/k` has a `k`-algebra map
  into a finite Galois extension `K/k` in the same universe. `K` is the normal closure of `L`
  inside the separable closure `SeparableClosure k`. It is Galois by Mathlib's
  `IsGalois.normalClosure` and finite by `normalClosure.is_finiteDimensional`.
- `ringTest_self_hom`, `ringTest_self_left`, `ringTest_self_hom_ext`: the structure morphism
  of `ringTest k k` (that is, `Spec k` over itself) is the identity. A morphism `f : T ⟶ ringTest k k`
  over `Spec k` therefore has `f.left = T.hom`, and any two such morphisms are equal.
- `exists_separable_point`: let `T` be a nonempty scheme over `Spec k` whose structure
  morphism is étale. Then for some finite separable extension `L/k`, there is a morphism
  `specOver k L ⟶ T` over `Spec k`.
- `exists_galois_chart`: let `X` be an algebraic space over `Spec k` and `x : RingPoints k X k`
  a `k`-point. Then there exist:
  - a finite Galois extension `K/k`;
  - `V : Over (Spec k)` with `V.left` affine and `V.hom` separated;
  - a morphism `a : (schemeYoneda _).obj V ⟶ X.presheaf` that is relatively representable and
    étale (`IsEtale a`);
  - a morphism `v : specOver k K ⟶ V` with
    `(schemeYoneda _).map v ≫ a = (schemeYoneda _).map (specOverMap (Algebra.ofId k K)) ≫ x̂`.

  Here `x̂ = uliftYonedaEquiv.symm x : (schemeYoneda (Spec k)).obj (ringTest k k) ⟶ X.presheaf`
  is the Yoneda morphism classifying `x`.
- `exists_desc_of_galois_invariant`: let `V` be over `Spec k` with `V.left` affine, and let
  `K/k` be finite Galois. Let `w : specOver k K ⟶ V` satisfy `specOverMap σ.toAlgHom ≫ w = w`
  for every `σ : K ≃ₐ[k] K`. Then `w = specOverMap (Algebra.ofId k K) ≫ u` for some
  `u : ringTest k k ⟶ V`.
- `changeRing_injective`: for a finite extension `K/k`, the map
  `RingPoints.changeRing (Algebra.ofId k K)` from `k`-points to `K`-points of an algebraic
  space `X` over `Spec k` is injective.

## Proofs

- `exists_separable_point`: choose a point of `T.left` and an affine open `W` containing it.
  The composite `Spec Γ(T.left, W) → T.left → Spec k` is `Spec` of a ring map `k → Γ(T.left, W)`.
  This ring map is étale by `HasRingHomProperty.Spec_iff` and `RingHom.etale_algebraMap`, and
  the ring is nonzero because `W` is nonempty. Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod`
  writes the ring as a finite product of finite separable field extensions of `k`. There is at
  least one factor because the ring is nonzero. Projecting onto a factor `L` gives a
  `k`-algebra map, and hence a morphism `specOver k L ⟶ T` through `W`.
- `exists_galois_chart`: take an atlas `a₀ : U₀ → X` from `X.exists_atlas`, and the represented
  base change `P` of `a₀` along `x̂`, with projections `p : P ⟶ ringTest k k` and `q : P ⟶ U₀`.
  The projection `p` is étale and surjective because `a₀` is. Hence `P` is nonempty and étale
  over `Spec k`, because `P.hom = p.left` (`ringTest_self_left`). `exists_separable_point`
  gives an `L`-point of `P`, and `exists_galois_of_separable` gives a Galois `K` with
  `L → K`. The composite `K`-point `v₁` of `U₀` satisfies the required equation for `a₀`.
  This follows from the pullback square and from the uniqueness of morphisms to
  `ringTest k k`. `Spec K` has a single point, so the image of `v₁` lies in an affine open `O`
  of `U₀.left`. Then `V` is `O` over `Spec k`, `a` is the open immersion followed by `a₀`
  (étale by `isEtale_map` and `IsEtale.comp`), and `v` is the factorization of `v₁` through `O`
  (`IsOpenImmersion.lift`). `V.hom` is separated because a morphism from an affine scheme to an
  affine scheme is affine.
- `exists_desc_of_galois_invariant`: identify `V.left` with `Spec Γ(V.left, ⊤)` via
  `isoSpec`. The morphism `w` corresponds to a ring map `φ : Γ(V.left, ⊤) → K`. Invariance
  under every `σ` and the injectivity of `Spec.map` show that `σ ∘ φ = φ`. So `φ` lands in the
  fixed field, which is `k` by `IsGalois.mem_range_algebraMap_iff_fixed`. The resulting ring
  map `Γ(V.left, ⊤) → k` defines `u`. To see that `u` lies over `Spec k`, precompose with
  `Spec K → Spec k`. Two endomorphisms of `Spec k` that agree after this precomposition are
  equal, because `k → K` is injective.
- `changeRing_injective`: `Spec K → Spec k` is flat, locally of finite presentation and
  surjective. So the sieve it generates is an fppf covering
  (`generate_singleton_mem_fppfTopology`). The underlying presheaf of `X` is separated for
  this covering, and two `k`-points with equal pullbacks to `Spec K` agree on every arrow of
  the sieve (`AlgebraicSpace.pullback_comp`).

Quasi-separatedness of `X` is not used in this module.
