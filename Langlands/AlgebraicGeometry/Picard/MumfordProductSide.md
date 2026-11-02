# The product side of the Mumford-bundle computation on `A ×_K A`

This module is the entry point of a helper unit for the proof of the published
`AlgClosedFieldAmpleEulerInverseScalingStatement`. It states one anchor proposition,
`MumfordProductSideStatement`, which is the conjunction of the main theorems of the two
companion modules, and proves it in `mumfordProductSide`.

Notation: `A` is an abelian scheme over `Spec K` for a field `K`, the self-product
`A ×_K A` is the published `mumfordProduct A` (the fibre product
`pullback A.X.hom A.X.hom`, viewed over the base), `m` is the published
`mumfordAddition A`, `p₁` is `pullback.fst A.X.hom A.X.hom` and `p₂` is
`pullback.snd A.X.hom A.X.hom`. Pullback of modules is `Scheme.Modules.pullback`, tensor
product is `tensorObj`, and `χ` is the published `eulerCharacteristic` of a module with
finite cohomology (`HasFiniteCohomology`) along the structure map.

## The anchor proposition

`MumfordProductSideStatement.{u}` is the conjunction of three parts.

1. For every field `K : Type u`, abelian scheme `A` over `Spec K` and line bundles `L, M`
   on `A` with finite cohomology `hL`, `hM`: the module `m^* L ⊗ p₁^* M` on `A ×_K A` has
   finite cohomology, and for every proof `hQ` of this,
   `χ(m^* L ⊗ p₁^* M) = χ(L) · χ(M)`.
2. The same with `p₂` in place of `p₁`: `m^* L ⊗ p₂^* M` has finite cohomology and
   `χ(m^* L ⊗ p₂^* M) = χ(L) · χ(M)`.
3. If the theorem of the square holds, in the form of the published (not yet proved)
   `Langlands.GroupScheme.FieldTheoremOfTheSquareStatement.{u}`, then for every
   algebraically closed field `K : Type u`, abelian scheme `A` over `Spec K`, ample line
   bundle `H` on `A` and line bundle `N` with `H ⊗ N ≅ 𝒪_A`, and every `n : ℕ`, the higher
   direct image `R^n p₂,* (m^* H ⊗ p₁^* N)`, written
   `(higherDirectImage (pullback.snd A.X.hom A.X.hom) n).obj (...)`, has finite closed
   support (`HasFiniteClosedSupport`).

Parts 1 and 2 are unconditional and need neither algebraic closedness, ampleness nor
inverses. Part 3 assumes the theorem of the square as a hypothesis of the proposition;
it is not an axiom.

## Proof

`mumfordProductSide` assembles the main theorems of the companion modules:

- parts 1 and 2 are `hasFiniteCohomology_mumfordAddition_tensor_fst`,
  `eulerCharacteristic_mumfordAddition_tensor_fst`,
  `hasFiniteCohomology_mumfordAddition_tensor_snd` and
  `eulerCharacteristic_mumfordAddition_tensor_snd` from
  `Picard/MumfordProductEulerCharacteristic.lean` (shear isomorphism of `A ×_K A`,
  Künneth formula, product of Euler polynomials);
- part 3 is `hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst` from
  `Picard/MumfordSecondProjectionSupport.lean`, applied to the isomorphism `H ⊗ N ≅ 𝒪`
  extracted from the `Nonempty` hypothesis.

The proofs of those theorems are described in the paired Markdown of the two companion
modules. The product computation in parts 1 and 2 rests on
`Modules/KunnethEulerProduct.lean`, which turns a degreewise Künneth decomposition of
cohomology into finiteness of cohomology and multiplicativity of Euler characteristics;
`MumfordProductEulerCharacteristic` supplies that decomposition from the published
Künneth theorem `coherentFieldExternalTensorKunneth`. The theorems use only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Files of this unit

- `Langlands/AlgebraicGeometry/Modules/KunnethEulerProduct.lean` and `.md`: Euler
  characteristics under a degreewise Künneth decomposition (author Worker 998).
- `Langlands/AlgebraicGeometry/Picard/MumfordProductEulerCharacteristic.lean` and `.md`:
  parts 1 and 2.
- `Langlands/AlgebraicGeometry/Picard/MumfordSecondProjectionSupport.lean` and `.md`:
  part 3.
- This module.

## Provenance

The anchor proposition is internal: it is exactly the conjunction of the main theorems
of the companion modules and does not newly formalize a definition or theorem of the
literature as a target. The mathematical model is Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary version), proof of (9.11), printed p.132 (PDF p.136):

- formulas (11)–(12) compute `χ(m^* L ⊗ p₁^* L^{-1}) = χ(L) χ(L^{-1})` using the
  isomorphism `m × p₁` of `A × A` and the Künneth formula. Parts 1 and 2 are this
  computation for arbitrary line bundles `L, M` with either projection.
- formula (10) uses that `R^n p₂,* (m^* L ⊗ p₁^* L^{-1})` is supported on the finite
  subscheme `K(L)`. Part 3 is this support statement for an ample `H`, proved here by
  a fibrewise argument through the theorem of the square rather than through the Poincaré
  bundle (see the Markdown of `MumfordSecondProjectionSupport`).

## Use

In the proof of the target scaling statement, part 1 gives `χ(A × A, m^* H ⊗ p₁^* N) =
χ(H) · χ(N)`, while part 3 lets the same Euler characteristic be computed from the direct
images along `p₂`, which live on finitely many closed points.
