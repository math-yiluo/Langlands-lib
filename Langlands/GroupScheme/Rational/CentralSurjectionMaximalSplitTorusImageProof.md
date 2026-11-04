# Maximality of split-torus images under central fppf surjections: proof

Author: Worker 1387.

The theorem `Langlands.GroupScheme.centralSurjectionMaximalSplitTorusImage`
proves `Langlands.GroupScheme.CentralSurjectionMaximalSplitTorusImageStatement.{u}`,
imported unchanged from
[`CentralSurjectionMaximalSplitTorusImageStatement`](CentralSurjectionMaximalSplitTorusImageStatement.md),
for every universe `u` and every field `k : Type u`. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. It adds no hypothesis: no
finiteness or smoothness of either kernel, and no condition on the
characteristic, separability or perfectness.

The statement is Borel–Tits, *Compléments à l'article « Groupes réductifs »*,
Théorème (2.20)(ii) (registered source
`borel-tits-1972-complements-groupes-reductifs`). Their proof reduces to the
rational conjugacy of maximal split tori. The Lean proof does not use
conjugacy. It argues inside the preimage of a larger split torus, as follows.

## Hypotheses actually used

Of the hypotheses of the statement, the proof uses the following.

- `IsConnectedReductive G`: only its affine and smooth structure morphism.
- `IsConnectedReductive H`: only its affine structure morphism.
- Flatness and surjectivity of `q`.
- Centrality of the scheme-theoretic kernel `kernelι q`.
- `IsMaximalSplitTorus i` and `IsSplitSubtorus j`.
- The commuting square `groupHom p ≫ j = i ≫ q`.

Local finite presentation of `q` and the three fppf hypotheses on `p` are not
needed.

## The argument

Let `j' : T''.toGrp ⟶ H` be a split subtorus and `f : T'.toGrp ⟶ T''.toGrp`
with `f ≫ j' = j`; we must show that `f` is an isomorphism.

1. *Reduction to characters.* `f.hom.hom.left` is a monomorphism, since
   `j.hom.hom.left` is a closed immersion. Its target and source are split
   tori. `CentralSurjectionImage.isIso_of_characterRestrict_injective` shows
   such an `f` is an isomorphism once restriction of rational characters
   `characterRestrict f` is injective. Restriction along a monomorphism of
   split tori is surjective (published
   `IsSplitTorus.characterRestrict_surjective_of_mono`), so the character
   lattices `ℤ^J ≅ ℤ^I` have equal ranks. The published
   `splitTorus.isIso_of_mono_of_card_eq` then applies.
2. *Key step*, `CentralSurjectionImage.characterRestrict_eq_zero_imp`. Let
   `α` be a character of `T''` with `characterRestrict f α = 0`; we show
   `α = 0`. Suppose `α ≠ 0`.
   - The preimage `M = G ×_H T''` is a commutative group scheme
     (`preimageComm`, from
     [`PreimageCommutative`](../CentralSurjectionImage/PreimageCommutative.md)).
     Its projection to `T''` is a base change of `q`, hence flat, surjective and
     quasi-compact. Its inclusion into `G` is a closed immersion, so `M` is
     affine and locally of finite type. The maximal split torus maps into `M`
     by `tM = pullback.lift i (groupHom p ≫ f)`.
   - `χ = α ∘ (M → T'')` has surjective underlying morphism, since nonzero
     characters of split tori are fpqc (published `RelativeRoot.characterFpqc`).
     So
     `exists_gm_characterRestrict_ne_zero_of_surjective` (from
     [`SurjectiveCharacterPoint`](../CentralSurjectionImage/SurjectiveCharacterPoint.md))
     gives a cocharacter `cμ : 𝔾_m ⟶ M` over `k` with
     `characterRestrict cμ χ ≠ 0`.
   - As `M` is commutative, `ψ = μ_M ∘ (tM ⊗ cμ)` is a homomorphism
     `T ⊗ 𝔾_m ⟶ M` from a split torus (`IsSplitTorus.tensor`). The published
     `IsSplitTorus.exists_factor_isSplitSubtorus` factors `ψ ≫ preι` through a
     split subtorus `D'` of `G`. The first inclusion `T → T ⊗ 𝔾_m` followed by
     `T ⊗ 𝔾_m → D'` factors `i` through `D'`. By maximality of `i` this
     composite `T → D'` is an isomorphism, so `cμ ≫ preι = ν ≫ i` for a
     cocharacter `ν` of `T`.
   - Composing with `q` and cancelling the monomorphism `j'` gives
     `cμ ≫ (M → T'') = ν ≫ groupHom p ≫ f`. Then
     `characterRestrict cμ χ = characterRestrict ν (characterRestrict p
     (characterRestrict f α)) = 0`, a contradiction.

## Dependencies

The helper modules are in `Langlands.GroupScheme.CentralSurjectionImage`, all by
Worker 1387:

- [`GroupAlgebraCoeff`](../CentralSurjectionImage/GroupAlgebraCoeff.md):
  coefficient formulas in `S[Λ × Λ]`.
- [`PointWeights`](../CentralSurjectionImage/PointWeights.md): coordinates of
  points, multiplicative points `IsMultG` and their convolution-idempotent
  weights.
- [`InseparableRigidity`](../CentralSurjectionImage/InseparableRigidity.md):
  rigidity of multiplicative points modulo nilpotents and purely inseparable
  descent of cocharacter data for arbitrary affine commutative groups.
- [`EigenGrading`](../CentralSurjectionImage/EigenGrading.md): the grading of
  `K ⊗ B` by generalized eigenspaces of a right translation, over an
  algebraically closed `K`.
- [`EigenDatum`](../CentralSurjectionImage/EigenDatum.md): a cocharacter datum
  over `K[Kˣ]` from one point.
- [`CocharacterFromPoint`](../CentralSurjectionImage/CocharacterFromPoint.md):
  restriction to a finitely generated exponent group and descent to `k`.
- [`SurjectiveCharacterPoint`](../CentralSurjectionImage/SurjectiveCharacterPoint.md):
  points of infinite order for surjective characters, and the resulting
  cocharacter theorem.
- [`BimultRigidity`](../CentralSurjectionImage/BimultRigidity.md): bimultiplicative
  maps out of split tori are trivial.
- [`PreimageCommutative`](../CentralSurjectionImage/PreimageCommutative.md):
  commutativity of the preimage.

Published Library inputs include the cocharacter-datum descent pipeline of
`Torus.CocharacterDetection` and its supporting modules, `Rational.SplitTorusImage`,
`Rational.SplitTorusMonomorphism`, `Rational.SplitTorusCharacterRestriction`,
`Rational.CharacterFpqcProof`, `Torus.Diagonalizable`, `AffineLinearEmbedding`,
`AbelianScheme.Kernel` and Mathlib's fpqc effective-epimorphism theorem.
