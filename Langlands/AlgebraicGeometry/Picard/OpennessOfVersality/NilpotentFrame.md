# Lifting frames along nilpotent thickenings of relative spaces

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NilpotentFrame`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

Setting: `f : X ⟶ Spec R` and a surjective `R`-algebra map `q : A →ₐ[R] B` with nilpotent
kernel (`hq`, `hn`). `relMap f q : relSpace f B ⟶ relSpace f A` is its relative-space map
(Library `Picard/RelativeAffineSections`).

## Declarations

- `surjective_morphismRestrict_relMap`: for every open `U`, the restriction
  `relMap f q ∣_ U` is surjective. `relMap f q` is surjective by `surjective_relMap`
  (`OpennessOfVersality.Obstruction`; nilpotent elements lie in the nilradical).
- `exists_frame_lift N U hU t ht`: let `N` be a line bundle on `relSpace f A` and `U` an
  affine open. Let `t` be a frame of the pullback `(relMap f q)^* N` on `relMap f q⁻¹ U`.
  Then there is a frame `s` of `N` on `U` with `pullbackLocalSection (relMap f q) s = t`.
  Proof:
  1. `t` trivializes the pullback on `relMap f q⁻¹ U` (FLT
     `IsFrameOn.nonempty_pullback_iso_unit`).
  2. The restriction of `relMap f q` to the open subschemes over `U` is surjective. It is
     surjective on global sections (Library
     `InfinitesimalAffineOpenNilpotence.relativeRestriction_appTop_nilpotentSurjective`).
     So `N` is trivial on `U` (Library `lineBundle_trivial_of_affinePullback`). This gives
     a frame `s₀` on `U` (FLT `exists_isFrameOn_of_pullback_iso_unit`).
  3. The coefficient `c` of `t` with respect to the pulled-back frame `pbs s₀` is a unit
     (`CocycleGluing.frameCoeff`, `frameCoeff_mul_frameCoeff`).
  4. The section map `(relMap f q).appLE U (relMap f q⁻¹ U)` is surjective with nilpotent
     kernel. This uses the Library's `isPushout_sections` and
     `nilpotentSurjective_of_isPushout`. So `c` lifts to a unit `a` on `U`
     (`NilpotentUnitReduction.unitsMap_surjective`).
  5. `s := a • s₀` is a frame (`DualNumberThickening.isFrameOn_smul_unit`) and pulls back
     to `c • pbs s₀ = t`.

## Provenance

Internal infrastructure for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It adapts the
argument of the Library module `Picard/DualNumberAffineFrames` to a general nilpotent
thickening of relative spaces. No literature statement is formalized.
