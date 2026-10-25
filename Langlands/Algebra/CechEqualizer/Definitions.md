# Tensor equalizer modules and noetherian model identifications

Authors: Worker 299 and Worker 424. Worker 299 designed and implemented these
constructions in the shared fibre-criterion proof draft. Worker 424 extracted
them without changing their Lean names or mathematical content for independent
publication before their proof consumers.

These are internal constructions for the proof of
`Langlands.Algebra.SmoothEqualizerFibreCriterion`. They are derived directly
from Mathlib's actual tensor products and base-change equivalences. They are
not definitions attributed to a literature source.

For commutative rings `A₀`, `C₀`, `C₁`, with `A₀`-algebra structures on the last
two, and an `A₀`-linear map `d : C₀ →ₗ[A₀] C₁`, the proposition
`Langlands.Algebra.CechEqualizer.Good d M` says that every `y : M ⊗[A₀] C₀`
with `d.lTensor M y = 0` equals `m ⊗ 1` for some `m : M`.
Here `M` is any additive commutative group with an `A₀`-module structure.
The rings and the module may occupy independent universes. The definition
does not require flatness, noetherianity, or `d 1 = 0`; when `d 1 = 0`,
it expresses that the kernel of `M ⊗ d` is exactly the image of `m ↦ m ⊗ 1`.
Without that additional hypothesis it asserts just containment of the kernel
in that image. It does not assert uniqueness of `m`.

For a scalar tower `R → A₀ → A`, an `R`-algebra `B`, an `A`-algebra `C`, and
an `A`-algebra equivalence `ε : C ≃ₐ[A] A ⊗[R] B`, the noncomputable
construction `Langlands.Algebra.CechEqualizer.modelEquiv A₀ ε` is the
`A`-algebra equivalence
`A ⊗[A₀] (A₀ ⊗[R] B) ≃ₐ[A] C`. It is
`Algebra.TensorProduct.cancelBaseChange R A₀ A A B` followed by `ε.symm`.
No inclusion or injectivity condition on `A₀ → A` is required. Computation
lemmas and the noetherian criterion are separate proof obligations.
