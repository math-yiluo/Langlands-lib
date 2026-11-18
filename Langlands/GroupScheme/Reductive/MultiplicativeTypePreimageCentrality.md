# The preimage of a central subgroup of multiplicative type is central

Worker 5698.

This module proves the centrality claim of part 2 of Conrad, *Reductive group schemes* (2014),
Lemma 3.3.1 (pp.96–97). Let `G` be a smooth `S`-affine group over `S` with connected fibres,
`H ⊆ G` a normal closed subgroup of multiplicative type, and `q : G ⟶ Ḡ` an fppf quotient of `G`
by `H`. If `h' : H̄' ⟶ Ḡ` is a central subgroup of multiplicative type, the preimage `P` of `H̄'`
in `G` is central in `G`. The multiplicative type of `P`, the other half of Conrad's part 2, is
not proved here. All declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypePreimageCentral`.

Conrad's proof sends `g` to the homomorphism `H̄' → H` given by `x ↦ g y g⁻¹ y⁻¹` for an
fppf-local lift `y` of `x` to `P`. He then reduces to the finite subgroups `H̄'[n]` and uses
that the Hom functor between them is finite étale. The Lean proof builds the same family of
homomorphisms `H̄' → H` parametrized by `G`. It then applies the rigidity theorem of
[`Torus.MultiplicativeTypeRelativeRigidity`](../Torus/MultiplicativeTypeRelativeRigidity.md)
directly, with no reduction to `H̄'[n]` and no Hom scheme.

## Group-theoretic lemmas

These use Mathlib's commutator `⁅g, x⁆ = g * x * g⁻¹ * x⁻¹` (scoped notation
`commutatorElement`), in an arbitrary group `M`.

- `commutatorElement_mul_of_commute_right`: if `c` commutes with `g`, then
  `⁅g, x * c⁆ = ⁅g, x⁆`.
- `commutatorElement_mul_of_commute` uses `RationalDensity.commutatorElement_mul_of_commute`. If `⁅g, x₂⁆` commutes with every element, then
  `⁅g, x₁ * x₂⁆ = ⁅g, x₁⁆ * ⁅g, x₂⁆`.

## Covers

- `over_ext_of_epi`: two morphisms `V ⟶ Y` in `Over S` are equal if they agree after
  precomposition with `f : U ⟶ V` whose underlying morphism of schemes is an epimorphism.
- For `q : G ⟶ Q`, `h' : H' ⟶ Q` and a point `z : V ⟶ H'.X`: `coverObj q h' z` is the
  `S`-scheme `G ×_Q V`, the fibre product of `q` and `z ≫ h'`. `coverMap` is its projection to
  `V` and `coverPt` its tautological point of `G`. `coverPt_comp` states
  `coverPt ≫ q = coverMap ≫ z ≫ h'`.

## The hypotheses

`Hyp h q h' p` (a `structure` valued in `Prop`) collects the hypotheses for `h : H ⟶ G`,
`q : G ⟶ Q`, `h' : H' ⟶ Q` and `p : P ⟶ G`:

- `mono`: `h.hom.hom` is a monomorphism;
- `central`: `IsCentral h`;
- `flat`, `surjective`, `lfp`: `q.hom.hom.left` is flat, surjective and locally of finite
  presentation;
- `ker`: `SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range h`;
- `central'`: `IsCentral h'`;
- `range`: `SubgroupFunctor.range p = (SubgroupFunctor.range h').comap q`.

`flat`, `surjective`, `lfp` and `ker` are the four components of
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`. `range` is the second component of
`IsRepresentedBy p`.

## The commutator map

Assume `hD : Hyp h q h' p`.

- `commute_comp`: points `k ≫ h` of the image of `h` commute with all points of `G`.
- `exists_preimage`: every point `y` of `P` has image `y ≫ p ≫ q` in the image of `h'`.
- `exists_lift`: a point `x` of `G` with `x ≫ q = z ≫ h'` lifts to `P`.
- `commutator_comp`: `⁅g, y ≫ p⁆ ≫ q = 1` for points `g` of `G` and `y` of `P`, because the
  image of `y ≫ p` in `Q` lies in the central image of `h'`.
- `exists_commutator`, `commH`, `commH_comp`: hence `⁅g, y ≫ p⁆` lies in the kernel of `q`,
  which is the image of `h`. `commH g y : T ⟶ H.X` is the chosen point with
  `commH g y ≫ h = ⁅g, y ≫ p⁆`. It is unique because `h` is a monomorphism.
- `comp_commH`: `commH` is natural in the test scheme.
- `commH_eq`: `commH g y` depends only on `y ≫ p ≫ q`. If `y₁` and `y₂` have the same image in
  `Q`, then `y₂ ≫ p = (y₁ ≫ p) * (k ≫ h)` for a point `k` of `H`. Since `k ≫ h` is central,
  `commutatorElement_mul_of_commute_right` applies.
- `commH_mul`: `commH g (y₁ * y₂) = commH g y₁ * commH g y₂`, by
  `commutatorElement_mul_of_commute`, since the values of `commH` are central.
- `commH_one_left`: `commH 1 y = 1`.

## Descent of the commutator map

Fix `z : V ⟶ H'.X` and `g : V ⟶ G.X`.

- `coverLift z`: a lift to `P` of the tautological point of `G` over `G ×_Q V`, which exists by
  `exists_lift`. `coverLift_q` states that its image in `Q` is `coverMap ≫ z ≫ h'`.
- `descFun z g`: the morphism of schemes underlying `commH (coverMap ≫ g) (coverLift z)`. By
  `commH_eq`, its two pullbacks to `(G ×_Q V) ×_V (G ×_Q V)` agree (`descFun_compat`).
- `K V g z : V ⟶ H.X`: the descent of `descFun z g` along `G ×_Q V ⟶ V`. That map is the base
  change of `q`, so it is flat, surjective and locally of finite presentation, hence an
  effective epimorphism of schemes (Mathlib, `AlgebraicGeometry.Sites.Fpqc`). `K` is
  constructed by `EffectiveEpi.desc`.
- `coverMap_K`: `coverMap ≫ K V g z = commH (coverMap ≫ g) (coverLift z)`.
- `cover_ext`: morphisms out of `V` are determined by their composites with `coverMap`.
- `comp_K`, the characterization: for `f : U ⟶ V` and any point `y` of `P` over `U` with
  `y ≫ p ≫ q = f ≫ z ≫ h'`, we have `f ≫ K V g z = commH (f ≫ g) y`. Both sides are compared
  on the fibre product of `f` and `coverMap`, whose projection to `U` is an epimorphism, and
  `commH_eq` is applied there.
- `K_naturality`: `K W (f ≫ g) (f ≫ z) = f ≫ K V g z`.
- `K_mul`: `K V g (z₁ * z₂) = K V g z₁ * K V g z₂`. Both sides are compared on the fibre
  product of the covers for `z₁` and `z₂`, using `comp_K` and `commH_mul`.
- `K_one`: `K V 1 z = 1`, from `commH_one_left`.

Thus `K` is a family of homomorphisms `H' → H` parametrized by `G.X`, natural in the test
scheme.

## Centrality

- `Hyp.isCentral`: if moreover `G.X.hom` is geometrically connected and `H`, `H'` are of
  multiplicative type, then `IsCentral p`. Proof: by
  `MultiplicativeTypeRigidity.eq_of_isMultiplicativeType`, applied to `K` with parameter
  scheme `G.X`, `K V g z = K V 1 z = 1` for all points `g` and `z`. Given points `g` of `G` and
  `y` of `P`, let `z` be a point of `H'` with `z ≫ h' = y ≫ p ≫ q`. Then `comp_K` with
  `f = 𝟙` gives `commH g y = K g z = 1`, so `⁅g, y ≫ p⁆ = 1`: `g` commutes with `y ≫ p`.
- `isCentral_preimage`: the centrality in part 2 of Conrad, Lemma 3.3.1, with the hypotheses
  of `Langlands.GroupScheme.MultiplicativeTypeNormalCentralStatement`. These are: `G` smooth
  and affine over `S` with connected residue fibres; `h : H ⟶ G` a closed subgroup of
  multiplicative type with normal image; `q` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`; `h' : H' ⟶ Q` central of
  multiplicative type; and `p : P ⟶ G` with
  `((SubgroupFunctor.range h').comap q).IsRepresentedBy p`. The conclusion is `IsCentral p`.
  Geometric connectedness of `G.X.hom` is
  `MultiplicativeTypeNormalCentral.geometricallyConnected_of_residueFiber`. Centrality of `h`
  is part 1, `MultiplicativeTypeNormalCentral.isCentral_of_isNormal_of_isClosedSubgroup`
  (module [`MultiplicativeTypeNormalCentrality`](MultiplicativeTypeNormalCentrality.md)).
  `isCentral_preimage` does not need `h'` to be a closed subgroup.
