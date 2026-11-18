# Rigidity over a set and its transport along monomorphisms

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It is internal.

- `IsRigidOn p L`, for `p : U ⟶ X` and a set `L` of points of `U`, is a local
  form of `IsRigid`. There is a finite set `E` of test triples on `U`, with
  domains contained in `L`, such that `ψ₁ ≫ p = ψ₂ ≫ p` together with
  `E`-nearness of `ψ₁` and `ψ₂` to `ψ` implies `ψ₁ = ψ₂`, provided that the
  ranges of `ψ`, `ψ₁` and `ψ₂` lie in `L`. Requiring the test domains to lie in
  `L` is what makes transport along domain embeddings possible: spaces need
  not be Hausdorff, so intersections of compact sets need not be compact.
- `TestTriple.isCompact_locus`: the domain of a test triple is compact.
- `range_map_comp_subset`: the range of a composite.
- `IsRigidOn.of_comp`: rigidity of `p ≫ h` implies rigidity of `p`.
- `IsRigidOn.precomp`: let `w` be rigid over `L` and let `j` be a
  monomorphism. Suppose that preimages under `j` of compact subsets of `L` are
  compact. Then `j ≫ w` is rigid over `j⁻¹(L)`. The new test triples come from
  `exists_isNear_postcomp`, applied to `j` and to each old triple. Equality
  after composition with `j` is cancelled because `j` is mono.
- `IsRigidOn.iso_comp`: the case of an isomorphism `j`, whose underlying map
  is a homeomorphism.
