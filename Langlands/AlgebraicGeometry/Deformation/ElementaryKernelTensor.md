# Actual elementary kernels after flat scalar extension

This is an internal algebra construction for the Picard deformation argument.
It combines the existing actual elementary kernel and its descended residue
action with Mathlib tensor associativity, symmetry and flatness. All rings,
modules and Artinian tests range over an arbitrary universe `u`. No external
geometric assertion or Picard representability theorem is used.

For a commutative `A`-algebra `R` and an actual ideal `I` of `A`,
the imported `GroupoidCoaction.idealTensorMap` is the `R`-linear multiplication map

```text
R ⊗[A] I → R,     r ⊗ x ↦ algebraMap A R (x.val) * r.
```

The imported `GroupoidCoaction.range_idealTensorMap` proves that its range is exactly the extended ideal
`I.map (algebraMap A R)`. Tensor induction gives containment in this ideal;
the reverse containment follows from the ideal-map/comap adjunction and the
representative `1 ⊗ x`. If `R` is flat over `A`, tensoring the injective ideal
inclusion remains injective. Composition with the tensor right-unit
equivalence therefore proves `idealTensorMap_injective`.
`idealTensorEquiv` identifies the tensor with the actual extended ideal by
the injective-map/range equivalence and the proved range equality.
`idealTensorEquiv_tmul` records its multiplication formula.

The coefficient comparison works more generally for commutative `A`-algebras
`K` and `R`, with a module `M` over both `A` and `K` and a compatible scalar
tower. The fibre ring is the actual algebra tensor product `K ⊗[A] R`.
Its `K` action is the usual action on the first factor; the local `R` action
is the right algebra structure from the second factor.
`coefficientTensorEquiv` is the `R`-linear equivalence

```text
(K ⊗[A] R) ⊗[K] M ≃ R ⊗[A] M.
```

The underlying equivalence swaps the outer tensor factors, cancels the base
change by the existing heterobasic associativity and unit equivalences, and
swaps the remaining factors. The proof then verifies `R` linearity by tensor
induction on the two tensor products. Its forward and inverse formulas are

```text
(c ⊗ r) ⊗ x ↦ r ⊗ (c • x),
r ⊗ x ↦ (1 ⊗ r) ⊗ x.
```

These are `coefficientTensorEquiv_tmul` and
`coefficientTensorEquiv_symm_tmul`. Flatness and a field hypothesis are not
needed for this general coefficient comparison.

For an actual augmented Artinian arrow `q : A ⟶ B`, the elementary hypothesis
is a `Fact (IsElementarySurjection q)` instance. The coefficient module is
the unchanged actual ideal `ElementaryKernel.Kernel q`, carrying the
canonical residue-field action from `ElementaryKernel.residueModule`.
The source-to-residue algebra structure is induced by the original
augmentation `A.augmentation`. The equality
`ElementaryKernel.augmentation_smul` supplies the scalar tower. In particular,
there is no choice or assumption of a section of the augmentation, and `A`
need not be a `K`-algebra.

For a flat commutative `A.algebra`-algebra `R`, `kernelTensorEquiv` composes
the coefficient comparison with the flat ideal comparison to give

```text
(K ⊗[A.algebra] R) ⊗[K] Kernel q
  ≃ₗ[R] (Kernel q).map (algebraMap A.algebra R).
```

`kernelTensorEquiv_tmul` sends `(c ⊗ r) ⊗ x`, as an element of the target
ideal, to `algebraMap A.algebra R ((c • x).val) * r`.
`kernelTensorEquiv_one_tmul` specializes this to
`algebraMap A.algebra R x.val * r`. Zero kernels and arbitrary kernel
dimensions are included.

This contribution constructs actual algebraic coefficient identifications.
It does not yet identify a sheaf or its cohomology with a fibre-coefficient
tensor, compare Picard obstructions under coefficient quotients, construct a
formal hull, or prove the field Picard atlas statement.
