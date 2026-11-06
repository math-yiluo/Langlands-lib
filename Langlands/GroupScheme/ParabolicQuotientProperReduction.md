# Reduction of parabolic quotient properness to a Borel quotient over `k̄`

Module `Langlands.GroupScheme.ParabolicQuotientProperReduction`, namespace
`Langlands.GroupScheme.ParabolicQuotient`.

This module proves `ParabolicSubgroupQuotientProperStatement`
(`Langlands.GroupScheme.HomogeneousQuotientStatement`) from three hypotheses:

- `SomeBorelQuotientProperStatement` (`Langlands.GroupScheme.Absolute.BorelProperQuotientStatement`):
  over an algebraically closed field, a connected smooth affine group has a Borel subgroup `B₀`
  whose homogeneous quotients are all proper;
- `BorelConjugacyStatement` (`Langlands.GroupScheme.Absolute.BorelStatement`), of which only the
  conjugacy part (the second conjunct) is used;
- `SmoothSubgroupQuotientExistenceStatement` (`Langlands.GroupScheme.HomogeneousQuotientStatement`),
  used only to get a quotient by `B₀`.

The mathematical route is the "if" direction of Milne, *Algebraic Groups* (2017), Theorem 17.16
(printed p. 356 / PDF p. 372). There, if `P` contains a Borel subgroup `B`, the map `G → G/P` factors through
`G/B`. Then `G/P` is complete, because `G/B` is complete and `G/B → G/P` is surjective.
The Lean proof adds two steps that Milne leaves implicit: it passes to the algebraic closure and
descends back, and it conjugates the Borel subgroup in `P_{k̄}` to the fixed Borel subgroup `B₀`.
No quotient by the Borel subgroup in `P_{k̄}` itself is ever built.

## Factoring through a quotient

- `exists_factor`: let `j : H ⟶ G` be a homomorphism of group schemes over `S`, and let
  `q₁ : G.X ⟶ Q₁` and `q₂ : G.X ⟶ Q₂` be morphisms over `S`. Suppose `q₁.left` is flat,
  surjective and quasi-compact. Suppose also that `q₁` identifies `T`-points only when
  `g⁻¹ * h ∈ range j`, and that `q₂` identifies all such `T`-points. Then some `φ : Q₁ ⟶ Q₂`
  satisfies `q₁ ≫ φ = q₂`. Proof: two scheme morphisms `a, b : Z ⟶ G.X.left` that agree after
  `q₁.left` lift to points over `T = Over.mk (a ≫ G.X.hom)`. The hypotheses then show that they
  agree after `q₂.left`. Mathlib's `EffectiveEpi` instance for flat surjective quasi-compact
  morphisms (`Mathlib.AlgebraicGeometry.Sites.Fpqc`) gives `φ.left` via `EffectiveEpi.desc`.
  Its compatibility with the structure maps follows by cancelling the epimorphism `q₁.left`.
- `universallyClosed_of_surjective`: if `φ : Q₁ ⟶ Q₂` is a morphism over `S` with `φ.left`
  surjective and `Q₁.hom` universally closed, then `Q₂.hom` is universally closed. This is
  `UniversallyClosed.of_comp_surjective` applied to `φ.left ≫ Q₂.hom = Q₁.hom`.

## Base change

For `b : S' ⟶ S`:

- `baseChangePointsEquiv_comp_map`: under the pullback adjunction `Over.mapPullbackAdj b`,
  composing a point `g` of the base-changed group with `(Over.pullback b).map q` corresponds to
  composing `baseChangePointsEquiv b G T g` with `q`. This is
  `Adjunction.homEquiv_naturality_right_symm`.
- `baseChange_coset`: suppose `q : G.X ⟶ Q` is constant on the cosets `g · range i`, that is,
  `g ≫ q = h ≫ q` whenever `g⁻¹ * h ∈ range i`. Then `(Over.pullback b).map q` is constant on
  the cosets of `range` of the base-changed homomorphism. The proof transports points along `baseChangePointsEquiv`, which is
  multiplicative (`map_mul`, `map_inv`). It uses the Library lemma `baseChangePointsEquiv_comp`.
- `surjective_baseChange_map`: base change preserves surjectivity of `q.left`
  (`MorphismProperty.overPullbackMap`).

## The algebraic closure

For a field `k`, the morphism `toAlgebraicClosure k : Spec k̄ ⟶ Spec k` gets instances for
`Surjective` (its target is a point), `IsIntegralHom` (`IsIntegralHom.SpecMap_iff` and
integrality of `k̄` over `k`, so Mathlib makes it universally closed) and `Flat`
(`Flat.SpecMap_iff` and `RingHom.flat_algebraMap_iff`).

- `universallyClosed_of_baseChange`: if the base change of `Q` to `k̄` is universally closed over
  `k̄`, then `Q.hom` is universally closed. Proof:
  `MorphismProperty.of_pullback_snd_of_descendsAlong`, which descends universal closedness along
  surjective flat quasi-compact morphisms (`Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`).

## Connectedness after base change

- `isConnected_preimage_range_section`: let `f : X ⟶ Spec K` have a section `e`, and let
  `g : Spec L ⟶ Spec K` be a morphism of field spectra. Then the preimage of `range e` under
  `pullback.fst f g` is connected. The proof identifies `pullback (pullback.fst f g) e` with
  `Spec L` by an explicit isomorphism and uses `Scheme.Pullback.range_fst`. This lemma and its
  proof copy the private lemma `connected_rational_fibre` of the Library module
  `Langlands.AlgebraicGeometry.AlgClosedConnectedProof`. That lemma is private, so it can't be
  imported.
- `connectedSpace_pullback_of_section`: if moreover `X` is connected and `g` is universally
  closed, then `pullback f g` is connected. The projection `pullback.fst f g` is open (Mathlib makes
  every morphism to the spectrum of a field universally open) and closed (`g` is universally
  closed). So every
  nonempty clopen subset of the pullback maps onto `X` and meets the connected fibre over the
  rational point. Two complementary nonempty clopen sets would then split that fibre.

The assembly applies this lemma with `g = toAlgebraicClosure k` and `e` the unit section of `G`.
That shows `G_{k̄}` is connected, as `SomeBorelQuotientProperStatement` and
`BorelConjugacyStatement` require.

## Conjugation

- `innerIso_coset`: suppose `i₀ ≫ Int(g) = f ≫ i` and `q` is constant on the cosets
  `x · range i`. Then `Int(g) ≫ q` is constant on the cosets `x · range i₀`. Here
  `Int(g) = (G.innerIso g).hom`. Proof: if `x⁻¹ * y = z ≫ i₀`, then
  `(x ≫ Int(g))⁻¹ * (y ≫ Int(g)) = z ≫ f ≫ i` by the Library lemma `comp_innerIso_hom` and
  `group`.

## Assembly

`parabolicSubgroupQuotientProper_of (hB) (hC) (hE) : ParabolicSubgroupQuotientProperStatement`.
Given `k`, `G`, a parabolic `i : P ⟶ G` and a homogeneous quotient `q : G.X ⟶ Q` by `range i`,
let `G' = G_{k̄}`.

1. `G'` is smooth and affine (base change), and connected (previous section).
2. `hB` gives a Borel subgroup `i₀ : B₀ ⟶ G'` whose homogeneous quotients are proper. `hE`
   gives a homogeneous quotient `q₀ : G'.X ⟶ Q₀` by `range i₀`, so `Q₀` is proper over `k̄`.
3. By `IsParabolicSubgroup.exists_isBorelSubgroup` there is a Borel subgroup `j : B ⟶ G'` with
   `j = f ≫ i_{k̄}` for some `f : B ⟶ P_{k̄}`. Conjugacy from `hC` gives `g ∈ G'(k̄)` and
   `φ : B₀ ≅ B` with `i₀ ≫ Int(g) = φ.hom ≫ j = (φ.hom ≫ f) ≫ i_{k̄}`.
4. `baseChange_coset` and `innerIso_coset` show that `Int(g) ≫ q_{k̄}` is constant on the
   cosets `x · range i₀`. `exists_factor` (applied to `q₀`, which is smooth, hence flat) gives
   `ψ : Q₀ ⟶ Q_{k̄}` with `q₀ ≫ ψ = Int(g) ≫ q_{k̄}`.
5. `Int(g)` is an isomorphism and `q_{k̄}` is surjective, so `q₀.left ≫ ψ.left` is surjective,
   hence `ψ.left` is surjective. `universallyClosed_of_surjective` makes `Q_{k̄}` universally
   closed over `k̄`. `universallyClosed_of_baseChange` makes `Q` universally closed over `k`.
6. With the hypotheses that `Q.hom` is separated and locally of finite type, `Q.hom` is proper.

Only the `⇒` direction of the coset condition for `q₀` and the `⇐` direction for `q` are
used. The smoothness of `q` and the quasi-compactness of `Q.hom` and `q.left` are not used.
