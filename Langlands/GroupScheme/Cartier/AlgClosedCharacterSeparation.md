# Cartier characters separate rational points over an algebraically closed field

This helper module proves the following. Let `K` be an algebraically closed field and
`G` a finite étale commutative group scheme over `Spec K`, killed by an integer `n`
that is invertible in `K`. Then every nontrivial `K`-point of `G` is detected by an
actual Cartier character of `G`. Here a Cartier character is an element of the
Library's character functor `Langlands.GroupScheme.Cartier.characters G`, taken at
the identity test scheme `Over.mk (𝟙 (Spec K))`. The module is one input to the
finite-level geometric Weil nondegeneracy proof (task `c063e112`), and it has the
interface agreed with Worker 989 for that assembly.

This is the standard fact that a finite étale group scheme over an algebraically
closed field is constant, and that the Cartier dual of a constant finite abelian
group `Γ` of order invertible in `K` is the constant group `Hom(Γ, K^×)`. The module
does not use either fact as stated. It proves directly the one consequence needed
(characters separate points), so the proof is internal and is not quoted from a
source. The only external input is Mathlib's duality for finite abelian groups,
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`.

Throughout, `X : Over (Spec K)` is a scheme over `K`, and a rational point is a
morphism `Over.mk (𝟙 (Spec K)) ⟶ X`. Everything is in the namespace
`Langlands.GroupScheme.Cartier`.

## Values of functions at rational points

- `pointValue a : Γ(X.left, ⊤) →+* K` is evaluation at the rational point `a`. It
  is `a.left.appTop` followed by the isomorphism `Γ(Spec K, ⊤) ≅ K`
  (`Scheme.ΓSpecIso`).
- `constants X : K →+* Γ(X.left, ⊤)` is the structure map: `X.hom.appTop` preceded
  by the inverse of `Scheme.ΓSpecIso`.
- `pointValue_constants`: `pointValue a (constants X k) = k`. This holds because
  `a.left ≫ X.hom = 𝟙` (`Over.w`), and `appTop` is functorial.
- `exists_pointValue_ne`: on an affine `X`, distinct rational points `a ≠ b` are
  told apart by some global function. Otherwise `a.left.appTop` and
  `b.left.appTop` agree after the isomorphism with `K`. They are then equal, and
  `ext_of_isAffine` gives `a = b`.
- `finite_points`: if `X.hom` is finite, there are finitely many rational points.
  A rational point gives a section of `X.hom`, injectively, and the Library lemma
  `Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite` says there
  are finitely many sections.

## Interpolation and reducedness

- `exists_section_pointValue`: on an affine `X` with finitely many rational points,
  any function `c` from rational points to `K` is realized by a global function `s`,
  with `pointValue a s = c a` for all `a`. For `a ≠ b`, rescale a function that
  separates them (`exists_pointValue_ne`) using constants, to get `e a b` with
  value `1` at `a` and `0` at `b`. The product over `b ≠ a` of `e a b` is `1` at
  `a` and `0` at every other rational point. Then
  `s = ∑ a, constants X (c a) * ∏_{b ≠ a} e a b`.
- `section_ext_of_pointValue`: if `K` is algebraically closed and `X.hom` is étale,
  two global functions with the same values at all rational points are equal. `X`
  is reduced, by the Library lemma
  `Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`.
  So it suffices that the basic open set of `s - t` is empty
  (`eq_zero_of_basicOpen_eq_bot`). Mathlib's
  `Scheme.exists_fac_of_etale_of_isSepClosed` lifts every point `x` of `X` to a
  rational point `l` with `x` in its image. The function `s - t` vanishes at `l`,
  so the pullback of the basic open set along `l` is the basic open set of `0` in
  `Spec K`, which is empty. Therefore `x` is not in the basic open set of `s - t`.

## Morphisms to the multiplicative group

`Gm.pointsEquiv` identifies morphisms `X ⟶ 𝔾_m` with units of `Γ(X.left, ⊤)`.

- `pointValue_pointsEquiv`: the value of the unit of `f : X ⟶ 𝔾_m` at `a` is the
  value, in `K`, of the unit of `a ≫ f` (`Gm.pointsEquiv_naturality`).
- `gm_hom_ext`: over an algebraically closed field, morphisms from a finite étale
  `X` to `𝔾_m` that agree after composing with every rational point are equal. This
  follows from the previous item and `section_ext_of_pointValue`.
- `exists_unit_pointValue`: if `X.hom` is finite and étale, every function from
  rational points to `K^×` is the family of values of a unit of `Γ(X.left, ⊤)`.
  Interpolate the values and their inverses (`exists_section_pointValue`; `X` is
  affine since `X.hom` is affine). The product of the two functions has value `1`
  everywhere, so it is `1` by `section_ext_of_pointValue`.
- `exists_gm_hom_of_points`: for a finite étale commutative group scheme `G` over
  algebraically closed `K` and a homomorphism `φ` from the group of rational points
  to `K^×`, there is `f : G.X ⟶ 𝔾_m` whose values at rational points are given by
  `φ`. Moreover `f` is multiplicative: `μ[G.X] ≫ f = (fst ≫ f) * (snd ≫ f)`. Take
  `f` from the unit of `exists_unit_pointValue`. `G.X ⊗ G.X` is again finite étale
  over `K`. So by `gm_hom_ext` it suffices to compare both sides at the rational
  points of `G.X ⊗ G.X`, that is at pairs of rational points of `G.X`. There
  multiplicativity is that of `φ`.

## Main theorem

`exists_characterEvaluation_ne_one_of_isAlgClosed`. Let `K : Type u` be an
algebraically closed field and `G : CommGroupScheme (Spec K)` with `G.X.hom`
finite and étale. Let `n : ℕ` with `(n : K) ≠ 0` and
`multiplication G.toGrp (n : ℤ) = 1`, and let `x` be a rational point of `G.X` with
`x ≠ 1`. Then some
`χ : (characters G).obj (op (Over.mk (𝟙 (Spec K))))` has
`characterEvaluation χ x ≠ 1`.

Proof. The group of rational points is finite (`finite_points`). Its exponent
divides `n`, because every point is killed by `n` (`points_zpow_eq_one`). So the
exponent is invertible in `K`, and `K` has enough roots of unity for it (Mathlib's
instance for separably closed fields, which covers algebraically closed ones). By
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` there is a homomorphism
`φ` from rational points to `K^×` with `φ x ≠ 1`. Let `f` be the multiplicative
morphism to `𝔾_m` from `exists_gm_hom_of_points`. Composition with `f` is a natural
family of homomorphisms on points of every test scheme. The Library's
`homOfPoints` turns it into a group-scheme homomorphism `ψ : G ⟶ 𝔾_m` with
`x ≫ ψ = x ≫ f` (`comp_homOfPoints`). The character is the base change of `ψ` to
the identity test scheme. Its evaluation at `x` is `x ≫ ψ`
(`evaluation_baseChange`), that is `x ≫ f`. If this were `1`, then the value of
`f` at `x` would be `1`, so `φ x = 1`, a contradiction.
