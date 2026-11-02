# Finite cores of affine coactions

This internal algebraic construction proves coherent exhaustion for the
published ring-valued `GroupoidCoaction` interface. The rings `B` and `C`
are in one universe, and the module `M` may be in an independent universe.
The given algebra structure is the source map and `t : B →+* C` is the
target map. The relation and coaction definitions are unchanged.

For a submodule `H` of `M`, `targetMap` tensors the quotient map by `C`
while retaining the target action in `TargetModule`. The obstruction
`coreMap θ H` is the coaction followed by this tensor quotient map.
The submodule `core θ H` is its kernel. Thus `mem_core_iff` says exactly
that the coaction becomes zero in `C ⊗[B] (M ⧸ H)`.

For a ring-valued étale equivalence relation `hE`, `core_le` proves
`core θ H ≤ H`: apply the relation's identity map to the coefficient
factor and then use the coaction counit and the tensor unit equivalence.

The composable-pair ring and tensor reassociation come from
`GroupoidCoactionTensor`. The formula `pairTensorMap_tmul_mk` identifies
reassociation on a general inner tensor, and
`pairTensorMap_lTensor_coreMap` identifies the tensor of the obstruction
with the iterated coaction followed by the quotient map.
`pairComposite hE` chooses the composite arrow supplied by transitivity;
its algebra-map law and `pairComposite_comp_t` record its source and
target. Applying the cocycle identity for this composite and the
injectivity of `pairTensorMap` proves `core_stable`: the coaction of a
core element lies in the kernel of the tensor of `coreMap`.

When the source algebra is flat, `coreSemilinearMap` uses
`LinearMap.tensorKerEquiv` to lift that tensor-kernel element uniquely
to `C ⊗[B] core θ H`. The lemma `coreSemilinearMap_subtype` gives its
image in the ambient tensor module. Étaleness supplies the required
flatness for `coreCoaction`, which applies the published `ofInjective`
construction. `core_subtype_isHom` says that inclusion in `M` is a
coaction homomorphism.

If `B` is Noetherian and `H` is finite as a `B`-module, `finite_core`
deduces finiteness of the core from its injection into `H`.
`mem_core_of_tensor_range` proves that any element whose coaction lies
in the tensor extension of `H` belongs to the core, by tensor induction
and the fact that `H` maps to zero in its quotient.

Finally, `exists_finite_subcoaction` uses the finite-coefficient property
of a tensor to choose a finite submodule `H` containing the coefficients
of the coaction of an arbitrary element `m`. Its core is finite, contains
`m`, and carries the restricted coaction with equivariant inclusion.
This holds for arbitrary modules; it assumes no acyclicity, quotient
scheme, or invariant-detection conclusion.

The definitions and proofs here are derived directly from the counit,
cocycle, tensor exactness, and Noetherian module properties. This is an
internal ring-level proof of the exhaustion step, without asserting a
translation to a separate geometric theorem or proving the full
nonzero-invariant statement.
