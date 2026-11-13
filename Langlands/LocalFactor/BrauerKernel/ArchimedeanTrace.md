# Real components of trace additive characters

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. The archimedean epsilon
factors of the global functional equations in Deligne's argument (1973, proof of Lemma 4.12)
depend on the archimedean components of the additive character `ψ ∘ Tr` of each global field
`M ⊇ k`. This unit computes these components at real places of `M` above real places of `k`.
The facts are elementary and have no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. For a real infinite place `v`,
`ringEquivRealOfIsReal` is Mathlib's identification of the completion with `ℝ`, and
`NumberField.LiesOver.completionMap` is the completion map of a place `u` of `M` over `r` of `k`.

## Results

- `ringEquivRealOfIsReal_completionMap`: for real `u` over real `r`, the completion map is the
  identity when both completions are identified with `ℝ`. Proof: the composite is a ring
  endomorphism of `ℝ`, and `ℝ` has only one (`Real.RingHom.unique`).
- `ringEquivRealOfIsReal_localTrace`: for real `u` over real `r`, the local trace
  `InfiniteExtension.localTrace r u` is the identity when both completions are identified with
  `ℝ`. Proof: every element of `M_u` is the image of an element `y` of `k_r` (previous item), the
  local degree is `1` (`isUnramified_of_isReal`), and the trace of the image of `y` is
  `1 • y = y` (`Algebra.trace_algebraMap`).
- `infiniteAdeleTrace_single`: the infinite adelic trace of an adele supported at one infinite
  place `u` above `r` is supported at `r`, where it is the local trace. Proof: the coordinate at a
  place `p` of `k` is the sum of the local traces over the places above `p`; only the place `u`
  contributes, and only when `p = r`.
- `isRealAdditiveComponent_traceAdditiveCharacter`: if the character `ψ` of `A_k` has real component
  `x ↦ exp(2πi a x)` at a real place `r` (`IsRealAdditiveComponent ψ r hr a`), then
  `traceAdditiveCharacter ψ` has the same real component `a` at every real place `u` of `M` above
  `r`. Proof: on the adele supported at `u`, the adelic trace is the adele supported at `r` given
  by the local trace, which is read as the identity of `ℝ`.
