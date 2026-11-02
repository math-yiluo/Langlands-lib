# The complex Deligne torus is a split torus of rank two

Author: Worker 207.

This module shows that the complex pullback of the real Deligne group scheme is a
split torus in the sense of `Langlands.GroupScheme.IsSplitTorus`. It adds a new
module and leaves the published Deligne modules unchanged. The declarations are
in the namespace `Langlands.Shimura.DeligneTorus`.

## Source

Milne, *Introduction to Shimura varieties*, in *Harmonic Analysis, the Trace
Formula, and Shimura Varieties*, Clay Mathematics Proceedings 4 (2005), Section 2,
paragraph "Hodge structures as representations of S", printed p.282 (PDF p.294):
"Let S be C^× regarded as a torus over R. [...] Then S(C) ≈ C^× × C^× with
complex conjugation acting by the rule [...]. We fix the isomorphism
S_C ≅ Gm × Gm so that S(R) → S(C) is z ↦ (z, z̄)". Source ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

The split-torus notion is the one documented in
`Langlands/GroupScheme/Torus/Split.md`: Milne, *Algebraic Groups* (2017),
Definition 12.14.

## Derived construction

- `complexGroupScheme` is the actual pullback of `DeligneTorus.groupScheme` along
  `Spec ℂ ⟶ Spec ℝ`. It and `complexSplitting : complexGroupScheme ≅
  splitGroupScheme` come from the published `DeligneSchemeSplitting` module
  (Worker 57). There `splitGroupScheme` is the cartesian monoidal product
  `Gm ⊗ Gm` over `Spec ℂ`, and the splitting sends a point to the evaluations at
  the two complex roots of `ω² = -1`. This is the identification `S_C ≅ Gm × Gm`
  of the source.
- `complexSplitTorusIso : complexGroupScheme ≅ GroupScheme.splitTorus
  (Spec ℂ) (PUnit ⊕ PUnit)` composes three isomorphisms. The first is
  `complexSplitting`. The second is the monoidal product
  `splitTorus.gmIso ⊗ᵢ splitTorus.gmIso`, which identifies each factor `Gm` with
  the split torus on `PUnit`. The third is `splitTorus.prodIso PUnit PUnit`, the
  product of split tori on `PUnit` and `PUnit` as the split torus on
  `PUnit ⊕ PUnit`. The index type `PUnit ⊕ PUnit` has two elements, so the
  complex Deligne torus has rank two.
- `isSplitTorus_complexGroupScheme : GroupScheme.IsSplitTorus complexGroupScheme`
  records this isomorphism.

## Scope

This module does not treat the Galois action on the split form. It does not
state that the real group scheme is not split, or compute its character
lattice. Non-splitting over `ℝ` is the separate statement
`DeligneTorus.NonSplitTorusStatement`.
