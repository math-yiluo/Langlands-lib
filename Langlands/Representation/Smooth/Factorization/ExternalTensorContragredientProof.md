# The contragredient of an external tensor product: proof

Worker 270 proves the unchanged published proposition
`Langlands.AdmissibleExternalTensorContragredientStatement` by the theorem
`Langlands.admissibleExternalTensorContragredient` in
`Langlands.Representation.Smooth.Factorization.ExternalTensorContragredientProof`.
The group universes `uG₁`, `uG₂` and carrier universes `uV₁`, `uV₂` remain independent.
The target statement, its paired Markdown, and its import closure are unchanged.

## Source and provenance

The result is the second assertion of the Proposition in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.1.14, printed pp.66–67 / PDF pp.72–73. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The published statement's Markdown describes the source and its scope.

The implemented proof uses a finite-dimensional currying argument in place of
Renard's tensor-product fixed-space calculation. Its private linear algebra
lemmas and constructions are internal derived content, introduced to establish
this exact statement. No further proposition is assumed.

## Canonical map and equivariance

Write `ρ = ρ₁ ⊠ ρ₂` and `ρ′ = ρ̃₁ ⊠ ρ̃₂`. The private abbreviation `external`
is the binary tensor representation formed after composition with the two
product projections.

`pairingIntertwiner` is the composite of `TensorProduct.map` on the two
`smoothDualPairing` inclusions with `TensorProduct.dualDistrib`. Thus, on pure
tensors, it sends `ℓ₁ ⊗ ℓ₂` to the functional

```text
v₁ ⊗ v₂ ↦ ℓ₁(v₁) ℓ₂(v₂).
```

Equivariance follows by extensionality on the source and evaluation tensors:
the full dual action uses inverse group elements on both factors. The tensor
product of two smooth representations is smooth, because a product of two
open stabilizing subgroups fixes a pure tensor, and smooth vectors form a
submodule. Applying `smoothLift` therefore gives `tensorMap : ρ′ → ρ̃` as an
intertwining map. The displayed pairing formula holds definitionally.

## Injectivity

The private lemma `tensorPairing_injective` treats arbitrary injective maps
`f : A → V₁*` and `g : B → V₂*`. Choose a basis `b` of `A` and use
`TensorProduct.equivFinsuppOfBasisLeft` to express `A ⊗ B` by finitely supported
`B`-valued coordinates. For `v₂ : V₂`, contract the second tensor factor with
the functional `g(−)(v₂)`, obtaining `C(v₂) : A ⊗ B → A`.

If the tensor pairing of `x` is zero, evaluating at `v₁ ⊗ v₂` shows
`f(C(v₂)x)(v₁) = 0` for every `v₁`. Injectivity of `f` gives `C(v₂)x = 0`.
For every basis index `i`, applying the coordinate `b.coord i` to this contraction
shows that `g` evaluates the `i`th `B`-coordinate of `x` to zero at every `v₂`.
Injectivity of `g` makes all coordinates zero, and hence `x = 0`.
Applying this lemma to the two smooth-dual inclusions proves
`tensorMap_injective` without admissibility assumptions.

## Surjectivity

Let `ℓ` be a smooth functional on `V₁ ⊗ V₂`, fixed by an open subgroup
`U` of `G₁ × G₂`. Pull `U` back along `g₁ ↦ (g₁,1)` and `g₂ ↦ (1,g₂)` to obtain
open subgroups `K₁` and `K₂`. Curry `ℓ` to

```text
q : V₂ → V₁*,   q(v₂)(v₁) = ℓ(v₁ ⊗ v₂).
```

The `K₁`-invariance of `ℓ` says that each `q(v₂)` is a smooth functional fixed
by `K₁`. Consequently `q` factors as a linear map `c : V₂ → F`, where
`F = fixedVectors (smoothContragredient ρ₁) K₁`. Its `K₂`-invariance says
`c(ρ₂(k⁻¹)v₂) = c(v₂)` for `k ∈ K₂`.

By `isAdmissible_smoothContragredient_of_compact_cofinal`, admissibility of `ρ₁`
makes `F` finite dimensional. Choose `b = Module.finBasis ℂ F` and define
`r_i = (b.coord i) ∘ c`. Each `r_i` is `K₂`-invariant and hence belongs to
`SmoothDual ρ₂`. The finite tensor

```text
∑ i, (b i).val ⊗ r_i
```

maps to `ℓ`: evaluation on `v₁ ⊗ v₂` reduces to the finite basis expansion
`b.sum_repr (c v₂)`. The private helper `basis_eval_sum` applies a linear
functional to that expansion and arranges the scalar factors. Extensionality
on pure evaluation tensors establishes equality of the smooth functionals.
The internal surjectivity lemma needs only first-factor admissibility;
the exported theorem retains both admissibility assumptions of the target.

## Final assembly and dependencies

`Langlands.Topology.LocallyProfiniteProof.vanDantzig`, together with
`Langlands.Topology.isLocallyProfinite_of_mathlib`, supplies compact open
subgroups cofinal among open subgroups of `G₁` from the target's Hausdorff,
locally compact, totally disconnected hypotheses. This discharges the cofinality
input used for admissibility of the first smooth dual.

`Representation.IntertwiningMap.ofBijective` combines the injective and
surjective intertwiner into a representation equivalence. Its pure-tensor
formula is `tensorMap_apply`, which proves the formula required by the exact
published target. The proof adds no hypothesis and uses no proof holes or
additional axioms.
