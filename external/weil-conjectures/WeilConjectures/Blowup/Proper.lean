/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Blowup.Affine.Proper
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.FiniteTypeExtension

/-!

# Properness of the global blow-up

We show that the blow-up map `I.blowupMap : I.blowup ⟶ X` of a scheme `X` along a
quasi-coherent ideal `I : X.IdealSheafData` is proper, provided `I` is of finite type.

Mathlib has no predicate for a finite-type quasi-coherent ideal sheaf, so the finite-type
condition of the blueprint is spelled out here as `∀ U : X.affineOpens, (I.ideal U).FG`.
On a locally Noetherian scheme this is automatic, which is recorded as an instance.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap_restrict` — the restriction of
  the blow-up map over an affine open on which the ideal is finitely generated is proper
  (blueprint: `lemma:nagata-global-blowup-proper-local`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap` — the blow-up map along an
  ideal that is finitely generated on every affine open is proper
  (blueprint: `thm:nagata-global-blowup-proper`).

## Blueprint

This file implements `lemma:nagata-global-blowup-proper-local` and
`thm:nagata-global-blowup-proper` of the Nagata compactification blueprint.

The blueprint deduces properness from projectivity of `b_{X,𝓘}`
(`thm:nagata-global-blowup-projective`), which in turn goes through the comparison of the
blow-up with a relative `Proj`. We instead prove properness directly, by locality on the
target: `IsProper` is Zariski-local on the target, and over an affine open the blow-up map
is, by `prop:nagata-global-blowup-affine-restrict`, the affine blow-up, which is proper by
`lemma:nagata-affine-blowup-proper`. Projectivity of the blow-up remains unformalized.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Local properness of the global blow-up**: the blow-up map is proper over an affine
open on which the ideal is finitely generated.
(blueprint: `lemma:nagata-global-blowup-proper-local`) -/
lemma isProper_blowupMap_restrict {U : X.affineOpens} (h : (I.ideal U).FG) :
    IsProper (I.blowupMap ∣_ U.1) := by
  have happ : IsProper (I.blowupNatTrans.app U) := by
    rw [I.blowupNatTrans_app U, MorphismProperty.cancel_right_of_respectsIso @IsProper]
    exact AffineBlowup.isProper_toSpec _ h
  have e : Arrow.mk (I.blowupMap ∣_ U.1.ι.opensRange) ≅ Arrow.mk (I.blowupNatTrans.app U) :=
    morphismRestrictArrowIso I.blowupMap (I.blowupNatTrans.app U) (I.blowupι_blowupMap U)
      (by rw [Scheme.Opens.opensRange_ι]; exact I.blowupMap_preimage U)
  have H : IsProper (I.blowupMap ∣_ U.1.ι.opensRange) :=
    ((MorphismProperty.arrow_mk_iso_iff @IsProper e).mpr happ)
  rwa [Scheme.Opens.opensRange_ι] at H

/-- **Properness of the global blow-up**: if the ideal is finitely generated on every affine
open, the blow-up map `Bl_I(X) ⟶ X` is proper.
(blueprint: `thm:nagata-global-blowup-proper`) -/
theorem isProper_blowupMap (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsProper I.blowupMap :=
  IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) fun U ↦ I.isProper_blowupMap_restrict (hI U)

/-- The blow-up of a locally Noetherian scheme along any quasi-coherent ideal is proper. -/
instance isProper_blowupMap_of_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsProper I.blowupMap :=
  I.isProper_blowupMap fun U ↦ I.ofFiniteType_of_isLocallyNoetherian U le_top

end AlgebraicGeometry.Scheme.IdealSheafData
