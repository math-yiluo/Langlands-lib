# Unitary central characters of finite external tensors

Author: Worker 189. Worker 158 authored the published complementary-tensor
contraction adapted here and specified the shared construction scope.
The center-coordinate helper boundary was coordinated with
Worker 190, who owns the separate quotient-geometry construction.

## Scope and provenance

This is an internal construction from the published actual data types
`Langlands.UnitaryCentralCharacter` in `MatrixCoefficient/ModuloCenter` and
`Langlands.FiniteTensor.external` in `Tensor/Finite`. It implements the
central-character obligation described in `Classification/BlockTensorAnalyticStatement`.
It does not assert either analytic comparison from that statement, or use any
of its six remaining obligations as hypotheses. No external theorem is cited
as proving this construction. The arguments below are finite product algebra,
subgroup topology, and algebraic tensor contraction. The contraction follows
the published basis-coordinate technique used in `Tensor/CoinvariantReflection`.

The index type `ι : Type uI`, dependent family of groups `G i : Type uG`, and
family of complex vector spaces `V i : Type uV` have independent universes.
Each factor has an arbitrary representation `ρ i : Representation ℂ (G i) (V i)`.
There is no topology on a vector-space carrier. The tensor is exactly Mathlib's
`PiTensorProduct ℂ V`, with the published action `FiniteTensor.external ρ`,
and the product group carries its actual product topology. Centers carry the
subspace topology inherited from their actual ambient group.

The finite constructions use `[Fintype ι]`; for an index supplied as `[Finite ι]`,
install `Fintype.ofFinite ι`. Coordinate insertion and restriction use
`[DecidableEq ι]`, which may be supplied classically. Assembly requires
`[∀ i, IsTopologicalGroup (G i)]` to deduce openness of a subgroup containing
an open subgroup. Restriction only requires the factor topological spaces,
because the coordinate map is continuous independently of continuity of group
operations. It also assumes `[∀ i, Nontrivial (V i)]`. The equivalence combines
these hypotheses. In particular, no scalar-endomorphism, irreducibility,
admissibility, unitarizability, countability, or finite-dimensionality assumption
is added.

## Full product-center coordinate maps

In namespace `Langlands.FiniteTensor`, `centerEval i` is the monoid homomorphism
from `Z(∏ i, G i)` to `Z(G i)` that evaluates at `i`. Its well-definedness uses
Mathlib's `Subgroup.center_pi`, so it uses the full group center.
`centerSingle i` sends `z : Z(G i)` to the product group element whose `i`th
coordinate is `z` and whose other coordinates are identity.

`centerEval_coe` and `centerSingle_coe` give these underlying formulas.
`centerEval_centerSingle_same` and `centerEval_centerSingle_ne` give evaluation
at the selected and the other coordinates. `continuous_centerEval` and
`continuous_centerSingle` prove continuity using continuous product evaluation
and `continuous_mulSingle`, followed by restriction to the subspaces.
These helpers require no finite index assumption.

For a finite index, `prod_centerSingle_centerEval` proves that every product
central element is the product of its inserted coordinates. The proof evaluates
each coordinate and reduces the finite product to its sole possibly nonidentity
factor. This is an algebraic statement with no topology assumption.

## Assembly

For supplied factor data `c i : UnitaryCentralCharacter (ρ i)`,
`tensorCentralCharacter c` is the actual monoid homomorphism

```text
Z(∏ i, G i) → ℂˣ,
z ↦ ∏ i, (c i).character (centerEval i z).
```

`tensorCentralCharacter_apply` is its representative formula.
`tensorCentralCharacter_isOpen_ker` intersects the inverse images of the factor
kernels under the continuous coordinate evaluations. This is an open subgroup
by finiteness and is contained in the product character's kernel. A subgroup
containing an open subgroup is open. The proof does not identify the product
kernel with this intersection: cancellations between factor values can make
the product kernel larger.

`externalUnitaryCentralCharacter c` packages that homomorphism into actual
`UnitaryCentralCharacter (external ρ)` data. Norm one follows by taking the
norm of a finite product of complex unit values. For scalar action, the proof
uses the published pure-tensor action formula and the factor scalar-action
laws. Multilinearity pulls out the product of scalars. Induction on sums of
scalar multiples of pure tensors extends this equality to every tensor.
`externalUnitaryCentralCharacter_character` exposes the product formula on
this constructed datum. Assembly does not require nontrivial factor carriers.

## Coordinate restriction and contraction

For `c : UnitaryCentralCharacter (external ρ)`, define the factor homomorphism
as `c.character.comp (centerSingle i)`. Its kernel is the continuous preimage
of the tensor character's open kernel, and its values have norm one by the
supplied tensor datum. These observations alone do not prove its scalar action
on `V i`; that is the content of `centralCharacter_acts_factor`.

Fix the selected coordinate `j`. Let `J = {j}ᶜ` and let `X` be the tensor of
the auxiliary factors indexed by `J`. Choose a vector-space basis `b i` in
each auxiliary factor. Nontriviality makes each basis index type nonempty,
so a choice of indices `a i` defines a basis vector `B a` of `X`, where
`B = Basis.piTensorProduct b`. The coordinate functional `B.coord a` takes
value one on `B a`; in particular this auxiliary vector is nonzero. No finite
basis is required.

The published splitting equivalence
`PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V j` identifies the full
tensor with `X ⊗[ℂ] V j`. The contraction is the actual linear map

```text
q = (TensorProduct.lid ℂ (V j)).toLinearMap
      ∘ₗ LinearMap.rTensor (V j) (B.coord a),
q(x ⊗ v) = (B.coord a x) • v.
```

Apply the tensor scalar-action law at `centerSingle j z` to the inverse image
of `B a ⊗ v`. The published `external_mulSingle` and `split_map_slot` turn
its action into identity on `X` tensored with `ρ j z` on `V j`. Apply the
splitting and then `q`. Since `(B.coord a) (B a) = 1`, the result is exactly

```text
ρ j z v = (c.character (centerSingle j z) : ℂ) • v.
```

`restrictUnitaryCentralCharacter c i` packages this proved action together with
the restricted homomorphism, its open kernel and its norm-one values.
`restrictUnitaryCentralCharacter_character` gives the composition formula.
All factor nontriviality assumptions are explicit, though the contraction
only uses them for the auxiliary factors.

## Intrinsic laws and equivalence of actual data

`tensorCentralCharacter_centerSingle` proves that an assembled character on a
central coordinate equals the original factor character. In the reverse
direction, `character_eq_prod_restrict` reconstructs a tensor character from
its restricted values using `prod_centerSingle_centerEval` and multiplicativity.

`Langlands.UnitaryCentralCharacter.ext` proves that these structures are
determined by their character field; all remaining fields are propositions.
Consequently `restrict_externalUnitaryCentralCharacter` and
`external_restrictUnitaryCentralCharacter` prove equality of the entire data,
not merely pointwise equality of values. The constructor

```text
FiniteTensor.unitaryCentralCharacterEquiv :
  (∀ i, UnitaryCentralCharacter (ρ i)) ≃
    UnitaryCentralCharacter (FiniteTensor.external ρ)
```

packages the two actual maps and the proved inverse laws under the stated
finite-index, topological-group, and nontrivial-carrier hypotheses.
`restrict_external_character` also exposes the forward inverse formula directly.

Empty and singleton index types are retained. With an empty index the product
character is the empty product, and there is no coordinate restriction to
perform. With a singleton index the auxiliary tensor uses the empty family;
its tensor basis and coordinate functional still give the contraction above.
There is no nonempty-index hypothesis or hidden positive-dimension bound.

This module supplies central-character data and their laws only. It does not
construct a quotient homeomorphism, prove smooth-dual factorization, or establish
any integrability statement.
