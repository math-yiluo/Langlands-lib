# Product-Levi tempered sufficiency from the GL criterion and block tensors

Author: Worker 23.

This module proves

```text
theorem Langlands.glProductLeviTemperedExponentSufficiency_of_criterion
    (hcrit : GLTemperedExponentCriterionStatement.{uF, uV})
    (htensor : GLBlockTensorTemperedStatement.{uF, uV}) :
    GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV}
```

The three propositions are published Library statements:

- `GLTemperedExponentCriterionStatement`, in
  [`TemperedExponentStatement`](TemperedExponentStatement.md): for an
  admissible representation `ρ` of `GL_n(F)` on which the scalar matrices act
  through a character `ω`, `T.IsTempered ρ` holds if and only if every Jacquet
  exponent `χ` along every block shape `B` of `n` satisfies `‖χ(a)‖ ≤ 1` on
  every tuple `a` with `T.normalizedAbs (a k)` monotone in `k`.
- `GLBlockTensorTemperedStatement`, in
  [`BlockTensorAnalyticStatement`](BlockTensorAnalyticStatement.md): for
  irreducible admissible factors `ρ j` of a block shape `B`, every factor is
  tempered if and only if `B.blockTensor ρ` is tempered modulo the centre of
  `B.Levi F.Carrier` for every Borel Haar measure on the central quotient.
- `GLProductLeviTemperedExponentSufficiencyStatement`, in
  [`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md):
  the upper core form of product-Levi tempered sufficiency.

All three use the independent field and representation universes `uF` and
`uV`. The theorem uses only the direction "exponent bounds imply tempered" of
the criterion and the direction "tempered factors give a tempered tensor" of
the tensor comparison. It proves none of the three propositions; together
with proofs of the first two it proves the third.

## Notation

Fix an ordered block shape `C` of `n` and a refinement `D` of `C`. Write
`e(j,k) = C.flattenBlockEquiv D ⟨j, k⟩` for the flattened labels, and
`m_D(a)` for the image of the flattened block scalar
`(C.flatten D).blockScalarLevi F.Carrier a` under `flattenedLeviEquiv`.
Fix an outer block `i`. In most lemmas `D` refines only block `i`: the
hypothesis `hD` says `(D j).length = 1` for every `j ≠ i`.

## Declarations

The helper declarations introduced here are in the namespace
`Langlands.ProductLeviTemperedFactorization`. The coordinate identities and
open-kernel lemma noted below are reused from existing Library modules.

Linear algebra:

- `pow_apply_of_apply J P Q c h k z`: if `P (J z) = c • J (Q z)` for every
  `z`, then `(P ^ k) (J z) = c ^ k • J ((Q ^ k) z)`.

Slot insertion for an external tensor:

- `exists_slot_insertion ρ e i hne`: let `ρ j` be representations of groups
  `H j` on `V j`, indexed by a finite type, and let `e` be an equivalence of a
  representation `σ` of `∀ j, H j` on `W` with the external tensor
  `FiniteTensor.external ρ`. If `V j` is nontrivial for every `j ≠ i`, there
  are linear maps `ins : V i → W` and `con : W → V i` with
  `con (ins x) = x`, `ins (ρ i h x) = σ (Pi.mulSingle i h) (ins x)`, and
  `con (σ g w) = ρ i (g i) (con w)` whenever `g j = 1` for all `j ≠ i`.
  The proof chooses a basis of each `V j` with `j ≠ i`
  (`Basis.ofVectorSpace`) and one basis index `a j` in each, which exists
  because `V j` is nontrivial. Let `c` be the tensor basis
  `Basis.piTensorProduct`, and `E` the Mathlib equivalence
  `PiTensorProduct.equivPiTensorComplSingletonTensor` from `⨂ V j` to
  `(⨂_(j ≠ i) V j) ⊗ V i`. Then `ins x = e⁻¹ (E⁻¹ (c a ⊗ x))`, and `con`
  sends `w` to the contraction of `E (e w)` against the coordinate
  functional `c.coord a`. The intertwining identities follow from the
  published `FiniteTensor.split_map_slot` and `FiniteTensor.external_mulSingle`.

Block coordinates, for a commutative ring `R`:

- `blockScalar_of_length_eq_one B hB c`: for a shape with one block,
  `B.blockScalar R c = scalar (∏ k, c k)`.
- `innerCoords C D R i`: the homomorphism `a ↦ (k ↦ a (e(i,k)))`
  (`innerCoords_apply`).
- `otherBlockProducts C D R i`: the homomorphism sending `a` to the tuple
  whose entry `j` is `1` for `j = i` and `∏_k a (e(j,k))` for `j ≠ i`
  (`otherBlockProducts_apply`).
- `continuous_innerCoords`, `continuous_otherBlockProducts` (for a
  topological ring) and `continuous_blockScalarLevi`: these homomorphisms and
  `C.blockScalarLevi R` are continuous. The last uses the published
  `GeneralLinear.scalarContinuous` in each block.
- The existing `Geometric.flattenedLeviProductEquiv_blockScalarLevi` and
  `Geometric.flattenedLeviEquiv_blockScalarLevi_apply` in
  [`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md):
  the outer component `j` of
  `m_D(c)` is the inner block scalar of `D j` at `innerCoords C D R j c`, in
  the nested product and in `C.Levi R` respectively.
- `flattenedLeviEquiv_blockScalarLevi_val`: under `hD`,
  `(m_D(c)).val = Pi.mulSingle i ((D i).blockScalar R (innerCoords C D R i c)) *
  C.blockScalarLevi R (otherBlockProducts C D R i c)`. In a block `j ≠ i`
  this uses `blockScalar_of_length_eq_one`.
- `mulSingle_scalar_eq_blockScalarLevi`: `Pi.mulSingle i (scalar a)` equals
  `C.blockScalarLevi R (Pi.mulSingle i a)`.

Open kernels:

- The existing `Classification.HasScalarCharacter.isOpen_ker hact hf hρ` in
  [`ProductLeviCentralCharacter`](ProductLeviCentralCharacter.md): let `ρ` be a smooth
  representation on a nonzero space and `f` a continuous homomorphism through
  which `ρ` acts by the character `χ`. Then `χ` has open kernel: the kernel
  contains the preimage under `f` of an open subgroup fixing a nonzero
  vector.

Moduli and the refined Jacquet module, over a `p`-adic field with topological
data `T`:

- `leviModulus_of_length_eq_one T B hB g`: for a shape with one block,
  `T.leviModulus B g = 1`. In the published formula `leviModulus_apply` each
  factor is a product over the later blocks, and there are none.
- `refinedLeviModulus_blockScalarLevi T C D i hD c`:
  `T.refinedLeviModulus C D (m_D(c)) =
  T.leviModulus (D i) ((D i).blockScalarLevi F.Carrier (innerCoords C D F.Carrier i c))`.
  The factors of the other outer blocks are `1` by
  `leviModulus_of_length_eq_one`.
- `exists_refinedJacquet_embedding T C σ ω hω i τ ins con hci hins hcon D hD`:
  let `σ` be a representation of `C.Levi F.Carrier` on which the outer block
  scalars act through `ω`, and `τ` a representation of
  `GL_(C.size i)(F)` with maps `ins`, `con` satisfying the three identities
  of `exists_slot_insertion`. Under `hD` there is an injective linear map
  `J` from `(D i).JacquetModule τ` to `RefinedJacquetModule C D σ` with

  ```text
  T.normalizedRefinedJacquet C D σ (m_D(a)) (J y) =
    ω (otherBlockProducts C D F.Carrier i a) •
      J (T.splitCentreJacquet (D i) τ (innerCoords C D F.Carrier i a) y).
  ```

  `J` sends the class of `x` to the class of `ins x`. It is well defined
  because `Pi.mulSingle i u` lies in `refinedUnipotent F.Carrier C D` for
  every `u` in the unipotent radical of `D i`. Its left inverse sends the
  class of `w` to the class of `con w`. This is well defined because an
  element of `refinedUnipotent F.Carrier C D` is trivial in every block
  `j ≠ i`, where `(D j).unipotentSubgroup` is trivial
  (`BlockShape.singleBlock_unipotentSubgroup_eq_bot`), and lies in the
  unipotent radical of `D i` in block `i`. The displayed identity is checked
  on classes. It uses `normalizedRefinedJacquet_mk`, the factorization
  `flattenedLeviEquiv_blockScalarLevi_val`, the action of the outer block
  scalars through `ω`, the identity for `ins`, and
  `refinedLeviModulus_blockScalarLevi`. The last makes the normalizing
  factor agree with the one in `splitCentreJacquet_mk`.

Exponents of one factor:

- `jacquetExponent_bound_of_core`: assume `σ` and `ω` as above, with
  `‖ω(b)‖ = 1` for all `b` and `ω` of open kernel. Assume the core hypothesis
  of `GLProductLeviTemperedExponentSufficiencyStatement` for `σ`, and maps
  `ins`, `con` for a representation `τ` of the factor `i`. Let `D` refine
  only block `i`. Then every Jacquet exponent `χ` of `τ` along `D i`
  satisfies `‖χ(a)‖ ≤ 1` whenever `T.normalizedAbs (a k)` is monotone in `k`.

  Let `ψ = (χ ∘ innerCoords C D F.Carrier i) * (ω ∘ otherBlockProducts C D F.Carrier i)`.
  Its kernel contains the intersection of the two open preimage kernels, so
  it is open. If `y ≠ 0` and `(T.splitCentreJacquet (D i) τ b - χ(b))^k y = 0`
  for every `b`, then `J y ≠ 0`. By the embedding identity and
  `pow_apply_of_apply`, `(T.normalizedRefinedJacquet C D σ (m_D(c)) - ψ(c))^k`
  sends `J y` to `ω(otherBlockProducts C D F.Carrier i c)^k` times `J` of
  `(T.splitCentreJacquet (D i) τ (innerCoords C D F.Carrier i c) - χ(innerCoords C D F.Carrier i c))^k y`,
  which is `0`. So `ψ` is a generalized eigencharacter of the upper refined
  action. Extend `a` to the flattened tuple `a'` with `a'(e(i,k)) = a k` and
  `a'(e(j,k)) = 1` for `j ≠ i`. It satisfies the monotonicity hypothesis of
  the core: in block `i` by assumption, and in the other blocks because they
  have one inner index. The core hypothesis gives `‖ψ(a')‖ ≤ 1`, and
  `‖ψ(a')‖ = ‖χ(a)‖` because `ω` takes values of norm `1`.

## Proof of the main theorem

Fix the data of the core statement: `C`, an irreducible admissible `S` with
outer block scalars acting through a unitary `ω`, and the core hypothesis.

1. **Factorization.** The published
   `CuspidalSupport.padicLeviAdmissibleFactorization`
   ([`LeviAdmissibleFactorizationProof`](../CuspidalSupport/LeviAdmissibleFactorizationProof.md))
   gives irreducible admissible representations `A j` of
   `GL_(C.size j)(F)` and an equivalence `e` of `S` with
   `C.blockTensor (fun j => (A j).representation)`, which is the external
   tensor `FiniteTensor.external`. Each `A j` and `S` are nonzero, since they
   are simple modules over the group algebra.
2. **Open kernel.** `S` is smooth and `C.blockScalarLevi F.Carrier` is
  continuous, so `Classification.HasScalarCharacter.isOpen_ker` shows that `ω` has open
   kernel.
3. **Exponent bounds of the factors.** Fix `i` and a block shape `B` of
   `C.size i`. Let `D` be the refinement with `D i = B` and the one-block
   shape of `C.size j` in every block `j ≠ i`. With `ins` and `con` from
   `exists_slot_insertion` for `e`, `jacquetExponent_bound_of_core` bounds
   every Jacquet exponent of `A i` along `B`.
4. **Central characters of the factors.** By the identity for `ins` and
   `mulSingle_scalar_eq_blockScalarLevi`, the scalar matrix `scalar a` acts
   on `A i` by `ω (Pi.mulSingle i a)`, applying `con` after `ins`.
5. **Tempered factors.** The direction "bounds imply tempered" of `hcrit`,
   with the central character `ω ∘ MonoidHom.mulSingle _ i`, gives
   `T.IsTempered (A i).representation` for every `i`.
6. **Tempered product.** The direction "tempered factors give a tempered
   tensor" of `htensor` makes `C.blockTensor (fun j => (A j).representation)`
   tempered modulo the centre for every Borel Haar measure `μ` on the central
   quotient. The published `isTemperedModCenter_of_equiv`, applied to `e⁻¹`,
   transfers this to `S.ρ`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is a derived adapter, internal to the project. It implements the
factorization-based route to the core statement mentioned under
"Dependencies and remaining scope" in
[`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md),
which names the published Levi factorization, the GL exponent criterion and
a tensor-temperedness statement as separate inputs. The slot insertion,
the embedding of one factor's Jacquet module into the refined Jacquet module
of the product, and the extension of tuples are elementary steps written for
this module. No literature result is formalized here; the mathematical
sources of the criterion and of the tensor comparison are listed in their
statement modules.
