# Eigenvectors under extension of scalars

The module `Langlands.Algebra.BaseChangeEigenvectors` compares kernels, images and eigenvectors
of a linear map `f : M → N` over a field `k` with those of its scalar extension
`f.baseChange K : K ⊗[k] M → K ⊗[k] N` to a field extension `K`.

## Main results

- `ker_baseChange`: the kernel of `f.baseChange K` is the image of `K ⊗ ker f` (flatness of `K`
  over the field `k`, Mathlib's `Module.Flat.ker_lTensor_eq`).
- `range_baseChange_eq`: if the image of `f` is a submodule `W`, the image of `f.baseChange K` is
  the image of `K ⊗ W`.
- `baseChange_sub_smul`, `mem_range_of_baseChange_eigen`: an eigenvector of `T.baseChange K` with
  an eigenvalue from `k` lies in `K ⊗` (the eigenspace of `T`).
- `baseChange_tmul_eigen`, `tmul_mem_span_of_mem_span`: pure tensors of eigenvectors are
  eigenvectors, and spans of eigenvectors are compatible with pure tensors.
- `span_baseChange_eigen_eq_top`: if the eigenvectors of `T : M → M` with integer eigenvalues span
  `M`, the eigenvectors of `T.baseChange K` with integer eigenvalues span `K ⊗ M`.
- `span_baseChange_positive_eigen`: in characteristic zero, the span of the eigenvectors of
  `T.baseChange K` with eigenvalues `n + 1` (`n` a natural number) is the image of `K ⊗ W`, where
  `W` is the span of the eigenvectors of `T` with these eigenvalues.
- `eq_eigenspace_of_iSup_eq_top`: if submodules `W i`, on which `T` acts by pairwise distinct
  scalars `μ i`, together span the module, then each `W i` is the full eigenspace for `μ i`
  (independence of eigenspaces, `Module.End.eigenspaces_iSupIndep`).

## Proofs

The kernel statement is exactness of `K ⊗ -`. For the positive eigenvectors, each eigenvector of
the extension with eigenvalue `n + 1` lies in `K ⊗ ker (T - (n + 1))` by `ker_baseChange`, hence
in `K ⊗ W`; conversely `K ⊗ W` is spanned by pure tensors `z ⊗ w` with `w` a positive
eigenvector, which are themselves positive eigenvectors.
