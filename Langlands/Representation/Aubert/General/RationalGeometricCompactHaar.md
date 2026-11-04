# Ambient Haar characters of the actual rational compact comparison

This internal construction by Worker 184 specializes
`Langlands.Induction.SplitStagesAmbientHaar` to the actual subgroups used in
`RationalGeometricCompactComparison`. It identifies the positive characters
behind that compact comparison and proves their kernels are open in the
nonarchimedean case. Its provenance is the published compact comparison,
split-stage identifications, and closed-normalizer Haar-character theory,
together with the generic helper paired with this module.

Fix any field `k : Type u`, an affine group scheme `G` over `k`, a commutative
group scheme `T`, a morphism `i : T.toGrp ⟶ G`, a cocharacter `ν`, finite sets
`I`, `J` of the associated simple roots, and a point `n` of the actual torus
normalizer. Supply the actual semidirect decomposition
`dI : IsSemidirectDecomposition P_I M_I U_I`. The construction is general
enough that connected reductivity, maximal splitness and genericity are not
additional hypotheses here. Those remain part of the host expansion target.

Write `A = G(k)`, `Q = P_I`, `L = M_I`, `U = U_I`, and
`F = n P_J n⁻¹`, using `Subgroup.map (MulAut.conj n)` literally. Set

```
Kt = L intersect F,       K = Kt.subgroupOf L,
C  = U intersect F,       H = (Q intersect F).subgroupOf Q.
```

`P` is the existing `geometricSplitIntermediate`, with its proved containment
of `dI.projection.ker`; `rP` and `sP` are its restricted retraction and section.
`N = geometricCompactKernel` and `D = geometricCompactKernelIntersection` are
the original nested subgroups from the compact comparison. No replacement
intersection or coordinate convention is introduced.

With any topology on `A`, `geometricCompactKernelEquiv : N ≃ₜ* U` and
`geometricCompactKernelIntersectionEquiv : D ≃ₜ* C` specialize the generic
ambient equivalences. Their application theorems preserve the identical
ambient group element while removing the subtype wrappers. The algebraic
`geometricCompactTarget_normalizes_correction` proves that the whole `Kt`
normalizes `C`, using `dI` and the two literal intersection containments.

Assume next that `A` is a locally compact topological group and that `U_I` and
`P_J` are closed. Conjugation preserves closedness, so `C` is closed.
`geometricCompactRadicalModulus : K →* ℝ≥0ˣ` restricts the original radical's
`HaarModulus.closedRestrictCharacter` from `L` to `K`.
`geometricCompactCorrectionModulus : K →* ℝ≥0ˣ` restricts the closed-normalizer
character of `C` to `Kt` and then transports it along the canonical
`K ≃* Kt`. Both act on the whole target intersection parabolic, not just on its
Levi subgroup. Write these characters as `delta_U` and `delta_C`.

For the equality with the compact integral character, additionally assume
`P_I` is closed, `N` is locally compact, and `N` and `D` have specified
measurable spaces satisfying `BorelSpace`. Then for every `l : K`,
`geometricCompactHaarCharacter_eq_ambient` proves the equality of complex units

```
geometricCompactHaarCharacter ... l
  = Jacquet.complexCharacter delta_U l
      / Jacquet.complexCharacter delta_C l.
```

The existing `geometricCompactHaarCharacter` is the complexification of the
split-kernel Haar ratio transported through `geometricSplitQuotientEquiv.symm`.
The proof specializes `splitStagesAmbientHaarRatio_apply` with the supplied
measurable and Borel instances on `N` and `D`. The quotient equivalence retains
the original Levi point, and the existing section-containment theorem supplies
the generic hypothesis. Closedness of `P_I` and `P_J` supplies closedness of
`HP`. Coercion of positive units to complex units then preserves division.
Thus the two inverse-conjugation Haar factors in the compact integral give
precisely the displayed radical-over-correction ratio.

If `A` is also nonarchimedean, the two ambient positive characters have open
kernel: these are `isOpen_ker_geometricCompactRadicalModulus` and
`isOpen_ker_geometricCompactCorrectionModulus`. Each pulls back
`HaarModulus.isOpen_ker_closedRestrictCharacter` along its continuous subgroup
inclusion. Under the same additional assumptions as the displayed character
equality, `isOpen_ker_geometricCompactHaarCharacter` follows because the
intersection of those two open kernels is contained in the integral
character's kernel. The equality makes its value there `1 / 1 = 1`.
`NonarchimedeanGroup` supplies the topological-group structure in these
smoothness lemmas. These lemmas establish the open-kernel property used for
scalar twisting; they do not introduce a representation carrier universe.

All constructions are derived helpers. No choice or compatibility of quotient
measures is needed for this character identity itself. The original compact
comparison has further smoothness, continuity, Hausdorffness, compact-open-basis,
and regular left/right Haar-measure hypotheses for its representation
equivalence, and this module does not discharge them. It also does not assert
the balance between the two distinct radicals, cancellation of both epsilon
corrections, compact/full induction, naturality, an orbit filtration, or the
normalized rational K0 expansion.
