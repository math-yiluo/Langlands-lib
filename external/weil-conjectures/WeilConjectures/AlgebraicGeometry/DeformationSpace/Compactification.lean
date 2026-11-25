/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Dense

/-!
# A compactification of the deformation to the normal cone over the affine line

Let `g : V ⟶ B` be a proper morphism with a section `s`, over a quasi-compact quasi-separated
locally noetherian base. The deformation to the normal cone `g̃ : D_s V ⟶ 𝔸¹_B`
(`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj`) is not proper: its fibre over `0` is the
affine normal cone. We compactify it over `𝔸¹_B` without changing it over the punctured line
`𝔾_{m,B}`: the dense compactification `D_s V ⟶ P ⟶ 𝔸¹_B`
(`AlgebraicGeometry.denseCompactification`) restricts over `𝔾_{m,B}` to an isomorphism
`V ×_B 𝔾_{m,B} ≅ P ×_{𝔸¹_B} 𝔾_{m,B}`.

The general input is `AlgebraicGeometry.Compactification.isIso_i_ofIsPullback`: over a flat base
change along which the morphism becomes proper, the open immersion of a dense compactification
becomes an isomorphism, being then a closed immersion that is scheme-theoretically dominant.

## Main results

- `AlgebraicGeometry.Compactification.isIso_i_ofIsPullback`: a dense compactification of `p`
  is an isomorphism after a flat base change making `p` proper.
- `AlgebraicGeometry.Scheme.Hom.deformationCompactification`: the compactification of `g̃`.
- `AlgebraicGeometry.Scheme.Hom.isPullback_deformationCompactification_puncturedLine`: over
  `𝔾_{m,B}` the compactification is `V ×_B 𝔾_{m,B}`, embedded by the punctured trivialisation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

variable {X Y S T : Scheme.{u}} {u : X ⟶ S} {p : Y ⟶ T} {h : X ⟶ Y} {t : S ⟶ T}

/-- Let `c` be a dense compactification of a quasi-compact morphism `p`, and let `u` be the base
change of `p` along a flat morphism `t`. If `u` is proper, then the open immersion of the base
changed compactification `c.ofIsPullback hsq` is an isomorphism: it is a closed immersion, since
`u` is proper, and it is scheme-theoretically dominant, since density is preserved by flat base
change. -/
theorem isIso_i_ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) (hc : c.IsDense)
    [QuasiCompact p] [Flat t] [IsProper u] : IsIso (c.ofIsPullback hsq).i := by
  have := c.quasiCompact_openImmersion ‹_›
  have := (c.ofIsPullback hsq).isClosedImmersion_openImmersion ‹_›
  have := c.isSchemeTheoreticallyDominant_i_ofIsPullback hsq hc
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  exact Scheme.Hom.ker_eq_bot _

/-- In the situation of `AlgebraicGeometry.Compactification.isIso_i_ofIsPullback`, the square
formed by `h ≫ c.i`, `u`, `c.g` and `t` is a pullback square: over `S`, the compactification `c.Z`
is `X`. -/
theorem isPullback_comp_i_of_isProper (hsq : IsPullback h u p t) (c : Compactification p)
    (hc : c.IsDense) [QuasiCompact p] [Flat t] [IsProper u] :
    IsPullback (h ≫ c.i) u c.g t := by
  have := c.isIso_i_ofIsPullback hsq hc
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (c.ofIsPullback hsq).i) (by simp) (by simp)
  rw [Category.assoc, ← c.comm, hsq.w]

end Compactification

namespace Scheme.Hom

open AffineZariskiSite

variable {V B : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V)

/-- `g̃ : D_s V ⟶ 𝔸¹_B` is locally of finite type if `g` is and `V` is locally noetherian. -/
instance [LocallyOfFiniteType g] [IsLocallyNoetherian V] :
    LocallyOfFiniteType (deformationSpaceProj g s) := by
  have : LocallyOfFiniteType
      (s.ker.deformationSpaceToPolynomialSpec ≫ V.polynomialSpecProj) := by
    rw [IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase _ _ _ s.ker.toPolynomialPresheaf_comp_polynomialToRees]
    infer_instance
  have : LocallyOfFiniteType s.ker.deformationSpaceToPolynomialSpec :=
    locallyOfFiniteType_of_comp _ V.polynomialSpecProj
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin 1)) g) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (AffineSpace.isPullback_map g).flip inferInstance
  rw [deformationSpaceProj]
  infer_instance

variable [IsProper g] [IsLocallyNoetherian V] [CompactSpace B] [QuasiSeparatedSpace B]

/-- The relative compactification `D_s V ⟶ P ⟶ 𝔸¹_B` of the deformation to the normal cone
`g̃ : D_s V ⟶ 𝔸¹_B` of a section `s` of a proper morphism `g`: the chosen dense compactification
of `g̃`. Its open immersion is scheme-theoretically dense
(`AlgebraicGeometry.Scheme.Hom.deformationCompactification_isDense`), and over the punctured
line it is an isomorphism
(`AlgebraicGeometry.Scheme.Hom.isPullback_deformationCompactification_puncturedLine`). -/
noncomputable def deformationCompactification : Compactification (deformationSpaceProj g s) :=
  have := QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have := quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  denseCompactification (deformationSpaceProj g s)

theorem deformationCompactification_isDense : (deformationCompactification g s).IsDense :=
  have := QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have := quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  denseCompactification_isDense (deformationSpaceProj g s)

/-- **The compactification does not change the deformation over the punctured line.** The
punctured trivialisation `κ° : V ×_B 𝔾_{m,B} ⟶ D_s V` followed by the open immersion into the
compactification `P` identifies `V ×_B 𝔾_{m,B}` with `P ×_{𝔸¹_B} 𝔾_{m,B}`. -/
theorem isPullback_deformationCompactification_puncturedLine :
    IsPullback (deformationSpaceGeneric g s ≫ (deformationCompactification g s).i)
      (pullback.snd _ _) (deformationCompactification g s).g (puncturedLine B).ι :=
  (deformationCompactification g s).isPullback_comp_i_of_isProper
    (isPullback_deformationSpaceGeneric g s) (deformationCompactification_isDense g s)

end Scheme.Hom

end AlgebraicGeometry
