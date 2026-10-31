# Characters of finite étale group schemes over an algebraically closed field

Throughout, `K` is an algebraically closed field and schemes are over `Spec K`.

## Results

- `finiteEtale_hom_ext`: two morphisms `f g : Y ⟶ Z` of schemes over `Spec K`, with finite
  étale structure morphisms, are equal as soon as `x ≫ f = x ≫ g` for every rational point
  `x : Over.mk (𝟙 (Spec K)) ⟶ Y`.
- `hom_eq_zero_of_points`: take a commutative group scheme `H` over `Spec K` with finite étale
  structure morphism, and `n` with `(n : K) ≠ 0` and `(𝟙 H.X) ^ n = 1`. A homomorphism
  `φ : H ⟶ Gm` is zero as soon as `σ ≫ φ = 1` for every rational point `σ` of `H`.
- `characters_eq_zero_of_evaluation`: take `G` with finite étale structure morphism and
  `multiplication G.toGrp n = 1` with `(n : K) ≠ 0`. A character
  `χ ∈ Cartier.characters G` over the identity test object `Over.mk (𝟙 (Spec K))` is zero as
  soon as `Cartier.characterEvaluation χ x = 1` for every rational point `x` of `G`.

## Proofs

`finiteEtale_hom_ext` regards `Y` and `Z` as objects of the Library's category `Cover` of
finite étale schemes. The published `geometricGaloisFiberFunctor`, applied to the geometric
point `𝟙 (Spec K)` with `geometricFiberFinite`, makes `Cover (Spec K)` a Galois category whose
fibre functor is the rational-point functor. `Spec K` is connected and Noetherian. Mathlib
shows fibre functors are faithful, so the two morphisms agree once their actions on fibres
agree, which is the hypothesis.

`hom_eq_zero_of_points` uses the `n`-torsion hypothesis to show that the morphism `ψ`
underlying `φ` satisfies `ψ ≫ [n] = ψ ^ n = 1`. So `ψ` factors through the kernel `μ_n` of
`[n]` on `Gm` (`kernelPointsEquiv`). Because `n` is a unit in `Γ(Spec K, ⊤)`, the published
`muFiniteEtale` says `μ_n` is finite étale. The factored morphism and the constant `1` agree
on rational points, because `σ ≫ ψ = 1` and the kernel inclusion is a monomorphism. Then
`finiteEtale_hom_ext` makes them equal, so `ψ = 1` and `φ = 0`.

`characters_eq_zero_of_evaluation` takes the base change `H` of `G` to the identity test
object. `H` is again finite étale and `n`-torsion; torsion is checked through
`baseChangePointsEquiv` and `points_multiplication`. It applies `hom_eq_zero_of_points` to
the homomorphism `Cartier.characterHomEquiv G T χ`. Its rational points are the images of
rational points of `G` under `Cartier.sectionPointsEquiv`, and on them
`Cartier.characterEvaluation_section` turns the hypothesis into the required equations.

## Provenance

This is derived infrastructure for the geometric-point nondegeneracy of the finite Weil
pairing. Over an algebraically closed field a finite étale scheme is a finite disjoint union
of rational points. So morphisms out of it, and characters of a finite étale group scheme,
are determined by their values on rational points. The Lean proof gets this from the
Library's Galois-category theory instead of an explicit decomposition.
