# Flat base change of square-zero reduction kernels

Namespace `Langlands.GroupScheme.Lie.NonaffineKernel`. The setting:
- `G : GroupScheme (Spec R)`, not assumed affine or separated;
- an ideal `I` of `R` with `[Fact (SqZero I)]`;
- an `R`-algebra `B`.

The kernel `kernel G J` of `G(A) → G(A ⧸ J)` and its module structure are
defined in `NonaffineKernel.lean`. The map `kernelMapAdd` along algebra
maps is defined in `NonaffineKernelMap.lean`.

## Instances and comparisons

- `fact_sqZero_map` (instance): extensions of square-zero ideals are
  square-zero. So `Additive (kernel G (I.map (algebraMap R B)))` is a
  `B`-module.
- `redStruct_unit₀`, `strMap_str`, `isGlobalLift_kernel_iff`, and
  `base_res` compare two data on `B`: the kernel data, and the kernel data
  of `R` base-changed to `B`. `liftBcEquiv` is the resulting
  `B`-linear identification of their modules of lifts.
- `kernelBcMap G I B` is restriction of kernel points from `R` to `B`. It
  is `kernelMapAdd` along `Algebra.ofId R B`.

## Main results

These assume `[Smooth G.X.hom]` and `[Module.Flat R B]`.

- `flatKernelEquiv G I B` is the `B`-linear equivalence
  `Additive (kernel G (I.map (algebraMap R B))) ≃ₗ[B]
  B ⊗[R] Additive (kernel G I)`.
- `flatKernelEquiv_symm_tmul`:
  `(flatKernelEquiv G I B).symm (b ⊗ₜ x) = b • kernelBcMap G I B x`.
- `flatKernelEquiv_kernelBcMap`:
  `flatKernelEquiv G I B (kernelBcMap G I B x) = 1 ⊗ₜ x`.
- `flatKernelEquiv_naturality` concerns an `R`-algebra map `φ : B → B'`
  between flat `R`-algebras. Restricting kernel points along `φ`
  corresponds to `φ ⊗ id`:
  `flatKernelEquiv G I B' (kernelMapAdd … φ … y) =
  LinearMap.rTensor _ φ.toLinearMap (flatKernelEquiv G I B y)`.
  The auxiliary lemmas are `map_le_map_extended` and
  `kernelMapAdd_kernelBcMap`.

`flatKernelEquivSymm` is assembled from three pieces:
1. `toLMEquiv`, which identifies kernels with modules of lifts;
2. `SmoothLifting.LiftModule.isBaseChange_resLin`, the flat base change of
   lifts;
3. `liftBcEquiv`.

All declarations use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.

Provenance: internal; an input to the cohomological lifting argument for
homomorphisms from groups of multiplicative type through nilpotent
thickenings. In Lie-algebra terms
this is `Lie(G) ⊗ I B ≅ B ⊗ (Lie(G) ⊗ I)` for flat `B`. It is stated for
the actual reduction kernels of a nonaffine smooth group scheme.
