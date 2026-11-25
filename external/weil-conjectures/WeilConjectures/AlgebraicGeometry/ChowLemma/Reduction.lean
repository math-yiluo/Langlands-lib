/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!
# The reduction step of Chow's lemma

Let `S` be a Noetherian scheme and let `f : X ⟶ S` be separated, locally of finite type and
quasi-compact. The first two steps of the proof of Chow's lemma replace `X` by a closed
subscheme `X*` carrying a finite affine open cover whose intersection is not merely dense but
*scheme-theoretically* dense. This file packages the outcome of those two steps as a structure
`AlgebraicGeometry.ChowReduction f` and proves that it is nonempty
(`AlgebraicGeometry.nonempty_chowReduction`), so that the proof of Chow's lemma itself can
`obtain` such a package and start from step 3.

Both ingredients are already available: the cover is
`AlgebraicGeometry.exists_isAffineOpen_cover_genericPoints_subset` (step 1) and the passage to
the scheme-theoretic closure `X*` of the intersection is the material around
`AlgebraicGeometry.Scheme.Opens.surjective_imageι_ι` (step 2). What this file adds is the
assembly, together with the deduction that `X` is Noetherian, which is what makes both
ingredients applicable.

## Main definitions

- `AlgebraicGeometry.ChowReduction` — the data produced by steps 1 and 2 of the proof of
  Chow's lemma.

## Main statements

- `AlgebraicGeometry.nonempty_chowReduction` — steps 1 and 2 of the proof of Chow's lemma.
- `AlgebraicGeometry.nonempty_chowReduction_of_finite_irreducibleComponents` — the same for a
  quasi-compact quasi-separated scheme with finitely many irreducible components.
- `AlgebraicGeometry.exists_chowReduction_n_ne_zero` — the same, with a nonempty cover.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200), steps 1 and 2 of the proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **The reduction step of Chow's lemma** for a morphism `f : X ⟶ S`: a surjective closed
immersion `c : X* ⟶ X` together with a finite affine open cover `X* = ⋃ i, Uᵢ` whose
intersection `⋂ i, Uᵢ` is scheme-theoretically dense in `X*`, and which is the preimage under
`c` of a dense open `V ⊆ X` over which `c` is an isomorphism.

Since `c` is a closed immersion, `X*` is again separated, locally of finite type and
quasi-compact over `S`, so the remaining steps of the proof of Chow's lemma may be run on `X*`
in place of `X`. -/
structure ChowReduction {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- the number of members of the cover -/
  n : ℕ
  /-- the closed model `X*` of `X` -/
  Y : Scheme.{u}
  /-- the surjective closed immersion `X* ⟶ X` -/
  c : Y ⟶ X
  [isClosedImmersion_c : IsClosedImmersion c]
  [surjective_c : Surjective c]
  /-- the finite affine open cover of `X*` -/
  U : Fin n → Y.Opens
  isAffineOpen_U : ∀ i, IsAffineOpen (U i)
  iSup_U : ⨆ i, U i = ⊤
  /-- the dense open of `X` the closed model is an isomorphism over -/
  V : X.Opens
  dense_V : Dense (V : Set X)
  preimage_V : c ⁻¹ᵁ V = ⨅ i, U i
  [isIso_morphismRestrict_c : IsIso (c ∣_ V)]
  [isSchemeTheoreticallyDominant_iInf : IsSchemeTheoreticallyDominant (⨅ i, U i).ι]

attribute [instance] ChowReduction.isClosedImmersion_c ChowReduction.surjective_c
  ChowReduction.isIso_morphismRestrict_c ChowReduction.isSchemeTheoreticallyDominant_iInf

/-- **Steps 1 and 2 of the proof of Chow's lemma for a scheme with finitely many irreducible
components.** A quasi-compact quasi-separated scheme `X` with finitely many irreducible
components admits a surjective closed model `X*` with a finite affine open cover whose
intersection is scheme-theoretically dense in `X*` and lies over a dense open of `X` over which
`X* ⟶ X` is an isomorphism.

Step 1 covers `X` by finitely many affine opens `Wᵢ` all containing the generic points of the
irreducible components of `X`; their intersection `V` is then dense, and quasi-compact since
`X` is quasi-separated. Step 2 replaces `X` by the scheme-theoretic image `X*` of the
quasi-compact immersion `V ⟶ X`, in which the copy of `V` is scheme-theoretically dense.
This is the form of steps 1 and 2 used in the non-Noetherian variant of Chow's lemma
(blueprint `rem-chow-lemma-non-noetherian`). -/
@[stacks 0203]
theorem nonempty_chowReduction_of_finite_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : (irreducibleComponents X).Finite) :
    Nonempty (ChowReduction f) := by
  -- Step 1: a finite affine cover through the generic points, with dense intersection.
  obtain ⟨n, W, hWaff, hWgen, hWcov⟩ := exists_isAffineOpen_cover_genericPoints_subset hX
  set V : X.Opens := ⨅ i, W i with hV
  have hVdense : Dense (V : Set X) := dense_iInf_of_genericPoints_subset hWgen
  -- `V` is quasi-compact, being a finite intersection of affine opens of a quasi-separated
  -- scheme, so the inclusion `V ⟶ X` is quasi-compact.
  have hVc : IsCompact (V : Set X) := by
    have h := QuasiSeparatedSpace.isCompact_sInter (α := X)
      (s := Set.range fun i ↦ (W i : Set X)) (Set.finite_range _)
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (W i).isOpen)
      (by rintro _ ⟨i, rfl⟩; exact (hWaff i).isCompact)
    rwa [Set.sInter_range, ← TopologicalSpace.Opens.coe_iInf] at h
  have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  have : QuasiCompact V.ι := (quasiCompact_iff_compactSpace V.ι).mpr inferInstance
  -- Step 2: replace `X` by the scheme-theoretic image of `V ⟶ X`.
  have hVU : ⨅ i, V.ι.imageι ⁻¹ᵁ W i = V.ι.imageι ⁻¹ᵁ V := V.iInf_preimage_imageι hV.symm
  exact ⟨{ n := n
           Y := V.ι.image
           c := V.ι.imageι
           surjective_c := V.surjective_imageι_ι hVdense
           U i := V.ι.imageι ⁻¹ᵁ W i
           isAffineOpen_U i := V.isAffineOpen_preimage_imageι (hWaff i)
           iSup_U := V.iSup_preimage_imageι_eq_top hWcov
           V := V
           dense_V := hVdense
           preimage_V := hVU.symm
           isSchemeTheoreticallyDominant_iInf := hVU ▸ inferInstance }⟩

/-- **Steps 1 and 2 of the proof of Chow's lemma.** A scheme `X` that is separated and of finite
type over a Noetherian scheme `S` admits a surjective closed model `X*` with a finite affine
open cover whose intersection is scheme-theoretically dense in `X*` and lies over a dense open
of `X` over which `X* ⟶ X` is an isomorphism.

Indeed, `X` is Noetherian, hence quasi-compact, quasi-separated and with finitely many
irreducible components, so this is a special case of
`AlgebraicGeometry.nonempty_chowReduction_of_finite_irreducibleComponents`. -/
@[stacks 0200 "Steps 1 and 2 of the proof"]
theorem nonempty_chowReduction {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (ChowReduction f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  exact nonempty_chowReduction_of_finite_irreducibleComponents f
    (finite_irreducibleComponents_of_isNoetherian (X := X))

/-- The cover of a `AlgebraicGeometry.ChowReduction` may always be assumed to be nonempty: if it
is indexed by `Fin 0`, then `X*` is empty and the one-element cover by `⊤` satisfies all the
requirements. -/
theorem ChowReduction.exists_n_ne_zero {X S : Scheme.{u}} {f : X ⟶ S} (R : ChowReduction f) :
    ∃ R' : ChowReduction f, R'.n ≠ 0 := by
  rcases eq_or_ne R.n 0 with hn | hn
  · -- If the cover is indexed by the empty type, `X*` is covered by nothing, hence empty.
    have : IsEmpty (Fin R.n) := by rw [hn]; infer_instance
    have hbot : (⊥ : R.Y.Opens) = ⊤ := (iSup_of_empty R.U).symm.trans R.iSup_U
    have : IsEmpty R.Y := Set.univ_eq_empty_iff.mp
      (congrArg (fun W : R.Y.Opens ↦ (W : Set R.Y)) hbot.symm)
    -- In an empty scheme all opens agree, so every field is inherited from `R`.
    have hopens : ∀ U U' : R.Y.Opens, U = U' := fun U U' ↦ by
      ext x
      exact isEmptyElim x
    refine ⟨{ R with
      n := 1
      U := fun _ ↦ ⊤
      isAffineOpen_U := fun _ ↦ isAffineOpen_top R.Y
      iSup_U := hopens _ _
      preimage_V := hopens _ _
      isSchemeTheoreticallyDominant_iInf := ?_ }, one_ne_zero⟩
    rw [hopens (⨅ _ : Fin 1, (⊤ : R.Y.Opens)) ⊤]
    infer_instance
  · exact ⟨R, hn⟩

/-- **Steps 1 and 2 of the proof of Chow's lemma**, with a nonempty cover. This is
`AlgebraicGeometry.nonempty_chowReduction` normalised via
`AlgebraicGeometry.ChowReduction.exists_n_ne_zero`, so that the constructions consuming the cover
may assume it has at least one member. -/
@[stacks 0200 "Steps 1 and 2 of the proof"]
theorem exists_chowReduction_n_ne_zero {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ R : ChowReduction f, R.n ≠ 0 :=
  (nonempty_chowReduction f).elim fun R ↦ R.exists_n_ne_zero

end AlgebraicGeometry
