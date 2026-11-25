# Star-fixed weight restriction to the actual anisotropic kernel

This module specializes the kernel-comparison results of
`Reductive/TitsKernelStarRestriction` to the Library's chosen actual
anisotropic kernel `p : d.AnisotropicKernelIndex`. Here `G` is an affine,
locally finite type group scheme over `Spec k` with index data `d`. The
kernel `p.kernel`, with `p.derived : p.kernel ⟶ p.centralizer`, is the actual
derived subgroup of the actual representative `p.centralizer` of the
centralizer of the maximal split torus. It has its own index data `p.index`,
and `p.comparison` is the published `KernelComparison` of `d` with `p.index`
along `p.derived ≫ p.inclusion`. This comparison carries the actual torus
morphism and identifies the kernel Cartan matrix with the zero subdiagram of
`d`.

`AnisotropicKernelIndex.weightRestriction p` is the actual integral character
restriction. It maps the characters of the absolute torus of `G`, base changed
to `SeparableClosure k`, to the characters of the absolute torus of the
kernel. It is defined as the published `KernelComparison.weightRestriction`
of `p.comparison`, which precomposes a character with the base change of the
comparison's actual torus morphism. `weightRestriction_apply` records this
definitional unfolding.

Assume that `G` is simply connected. The Library theorem
`AnisotropicKernelIndex.isSimplyConnected` then gives simple connectedness of
the actual kernel `p.kernel`. The Library theorem
`TitsIndexData.pinning_corootSpan_eq_top` then shows that the kernel's simple
coroots span its integral cocharacter lattice. With this input:

- `weightRestriction_starAction` proves
  `p.weightRestriction (σ ⋆ x) = σ ⋆ p.weightRestriction x` for every
  absolute Galois element `σ`. Here `⋆` denotes the full absolute star action
  `(starAction σ).val.weightEquiv` of the respective pinning.
- `weightRestriction_starFixed` proves that `p.weightRestriction x` is fixed
  by every kernel star automorphism whenever `x` is fixed by every ambient
  star automorphism.

These are the specializations of `KernelComparison.weightRestriction_starAction`
and `KernelComparison.weightRestriction_starFixed`.

No characteristic, perfectness, rank, Cartan-type or inner-type hypothesis is
imposed, and the field `k` is arbitrary in universe `u`. No Tits algebra or
Brauer class is constructed or compared here.

Provenance: internal. The module only combines published Library
constructions (the anisotropic kernel, its kernel comparison, kernel simple
connectedness, the coroot-span theorem) with the star-equivariance theorem
of `Reductive/TitsKernelStarRestriction`.
