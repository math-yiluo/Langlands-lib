# Actual root-weight line bundles and coherent affine root frames

Lean module: `Langlands.GroupScheme.Reductive.RootWeightLineBundles`.

## Setting

- `S` is an arbitrary scheme and `G : GroupScheme S` is reductive (`hG : IsReductive G`).
- `t : splitTorus S I ⟶ G` is a finite coordinate torus that is fibrewise maximal (`hmax`).
- `P : RootDatum J (I → ℤ) (I → ℤ)` is a global coordinate root datum of `(G, t)`
  (`hP : IsGlobalCoordinateRootDatumOf I G t P`): finite and reduced, and realized as the actual
  root datum on every field-valued fibre.

No noetherian, quasi-compact, separated, affine, local-ring or characteristic hypothesis is
imposed, and universes are arbitrary. The construction does not use closedness of `t`, so no
closed-immersion hypothesis appears; the results apply in particular to a closed torus.

## The line bundles

- `rootWeightSystem hG t P α := splitTorus.weightTestSystem I G t (P.root α)` is the affine test
  system of actual exponent-weight modules of the root `α`, from `RootWeightTestSystem`.
- `isLocallyFreeRankOne_rootWeight`: on the chart of every affine open `U`, the associated sheaf
  of the root-weight module is locally free of rank one. The module is finite projective
  (`finite_exponentWeightSpace`, `projective_exponentWeightSpace`) and has rank one at every prime
  (`rootWeightRank_eq_one`). The datum on the chart comes from
  `IsGlobalCoordinateRootDatumOf.affinePullback`, and `isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one`
  concludes.
- **`rootLineBundle hG t hmax P hP α : Picard.LineBundle S`** is the realization of the system as an
  actual line bundle (`AffineTestSystem.toLineBundle`). Its underlying sheaf is
  `(rootWeightSystem hG t P α).toModules` (`rootLineBundle_obj`).

## The affine comparisons and their coherence

- **`rootFrame α a`**, for every commutative ring `R` and every morphism `a : Spec R ⟶ S`, is the
  isomorphism
  `a^* (rootLineBundle α) ≅ (splitTorus.exponentWeightSpace I ((baseChange a).obj G)
     ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t) (P.root α))^~`.
  It is the canonical frame `AffineTestSystem.frame`.
- **`rootFrame_hom_eq`**: for an `R`-algebra `A`, `p = Spec(R → A)` and `h : p ≫ a = b`, the
  frame on `b` equals the inverse of the canonical scheme-module identification
  `(pullbackComp p a) ≪≫ (pullbackCongr h)`, followed by `p^*` of the frame on `a`, the actual
  `tildePullbackAlgebraIso R A`, and `tilde.map` of the coefficient-extension identification.
  By `rootWeightSystem_ext`, that identification is `splitTorus.weightExt`: the actual
  exponent-weight base-change equivalence followed by the transport along the ambient
  `baseChangeCompIso` normalization.

## Frames under the Picard hypothesis

Assume `hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S)`.

- **`picardRootFrames hG t hmax P hP hPic : CoordinateRootDatum.AffineRootFrames t P`** consists of
  chosen global trivializations of the `rootLineBundle α` (`AffineTestSystem.picardFrame`). They give
  linear equivalences `R ≃ₗ[R] exponentWeightSpace …` on every affine test `a : Spec R ⟶ S` and every
  root `α`.
- **`picardRootFrames_isCoherent`**: these frames satisfy
  `CoordinateRootDatum.AffineRootFrames.IsCoherent`. After extending coefficients to the same
  affine test ring (`Algebra.ofId R A`, test `algebraBaseMap R A ≫ a`), the actual root-vector
  dual-number points agree in the original group `G`. This follows from the frame coherence
  `picardFrame_ext` and the point formula `splitTorus.weightExt_point`.

## Provenance

This module is the construction required by the task (a prerequisite of the parent task, not a
proof of the parent isomorphism statement). The root-weight sheaves, their affine comparisons and
coherence are built from the actual group and torus. No weight-sheaf decomposition, root line
bundle, cocycle or compatible frame is taken as a hypothesis. The only Picard input is the
parent's exact hypothesis that line bundles on `S` are trivial.
