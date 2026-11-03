# Homology after tensoring with global sections of scheme tests

For an arbitrary coefficient ring `R : CommRingCat.{u}`,
`TensorSections.sectionModules` is the contravariant functor on the full
scheme slice over `Spec R` that sends `T` to its global sections as an
`R`-module. Its scalar map and restriction maps are the published
`FiniteLinearEquations.sectionScalars` and `pullSections`, so they use the
actual structure morphism of the test scheme.

`tensorComplex K` tensors a fixed integer cochain complex `K` with a varying
module on the left. `complexes K` therefore sends `T` to the ordinary
termwise tensor complex `Γ(T,𝒪_T) ⊗[R] K`, viewed in `ModuleCat R`.
`homologyPresheaf K n` takes its degree-`n` homology, forgets its module
structure, and applies the explicit `ULift.{u+1}`. All scheme tests and all
their restriction maps occur in these functors.

This is an internal construction from the coefficient and global-section
conventions already used by `FiniteLinearEquationsScheme`, Mathlib's
monoidal module category, and its homology functor. Functoriality follows
from actual restriction of global sections and the natural transformation
of tensor functors. It asserts no geometric comparison, perfection,
vanishing, or representability. In particular, for a general complex this
ordinary tensor homology is not being identified with hypercohomology on a
nonaffine test scheme.
