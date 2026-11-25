/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Proper closed models of affine pieces

Let `S` be a Noetherian scheme and let `g : V ⟶ S` be locally of finite type with `V` affine.
Step 3 of the proof of Chow's lemma replaces `V` by the scheme-theoretic image `Z` of an
immersion of `V` into a projective space over `S`: then `Z` is proper over `S` and `V` sits
inside `Z` as a scheme-theoretically dense open subscheme. This file packages that outcome as a
structure `AlgebraicGeometry.ProperClosedModel g` and proves that it is nonempty
(`AlgebraicGeometry.nonempty_properClosedModel`).

Both ingredients are already available: the immersion into projective space is
`AlgebraicGeometry.exists_isImmersion_projectiveSpace`, and the properties of the
scheme-theoretic image of a quasi-compact immersion are Mathlib's
`AlgebraicGeometry.Scheme.Hom.toImage`. What this file adds is the assembly, together with the
deduction that `V` is Noetherian, which is what makes the immersion quasi-compact.

## Main definitions

- `AlgebraicGeometry.ProperClosedModel` — a proper closed model of a morphism `g : V ⟶ S`.

## Main statements

- `AlgebraicGeometry.nonempty_properClosedModel` — an affine scheme locally of finite type over
  a Noetherian scheme admits a proper closed model.
- `AlgebraicGeometry.nonempty_properClosedModel_of_quasiSeparatedSpace` — the same over a
  quasi-compact quasi-separated scheme.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200), step 3 of the proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A **proper closed model** of `g : V ⟶ S`: a closed subscheme `Z` of a projective space
`ℙ(n; S)` with `n` finite, in which `V` sits as a scheme-theoretically dense open subscheme,
compatibly with `g`.

Since a closed immersion is proper and `ℙ(n; S)` is proper over `S` for finite `n`, the
structure morphism `Z ⟶ S` is proper; see the `IsProper` instance below. -/
structure ProperClosedModel {V S : Scheme.{u}} (g : V ⟶ S) where
  /-- the index type of the homogeneous coordinates of the ambient projective space -/
  n : Type u
  [finite_n : Finite n]
  /-- the proper closed model `Z` of `V` -/
  Z : Scheme.{u}
  /-- the closed immersion of `Z` into the projective space `ℙ(n; S)` -/
  emb : Z ⟶ ℙ(n; S)
  [isClosedImmersion_emb : IsClosedImmersion emb]
  /-- the identification of `V` with a scheme-theoretically dense open subscheme of `Z` -/
  ι : V ⟶ Z
  [isOpenImmersion_ι : IsOpenImmersion ι]
  [isSchemeTheoreticallyDominant_ι : IsSchemeTheoreticallyDominant ι]
  w : ι ≫ emb ≫ ℙ(n; S) ↘ S = g

attribute [instance] ProperClosedModel.finite_n ProperClosedModel.isClosedImmersion_emb
  ProperClosedModel.isOpenImmersion_ι ProperClosedModel.isSchemeTheoreticallyDominant_ι

namespace ProperClosedModel

variable {V S : Scheme.{u}} {g : V ⟶ S} (M : ProperClosedModel g)

/-- **The closed model is proper over the base**: `Z ⟶ S` is the composition of a closed
immersion with the structure morphism of a projective space, both of which are proper. -/
instance isProper_emb_comp_over : IsProper (M.emb ≫ ℙ(M.n; S) ↘ S) := inferInstance

end ProperClosedModel

/-- **Step 3 of the proof of Chow's lemma over a quasi-compact quasi-separated base.** An affine
scheme `V` locally of finite type over a quasi-compact quasi-separated scheme `S` admits a
proper closed model.

Indeed, `V` immerses into some `ℙ(n; S)` over `S` by
`AlgebraicGeometry.exists_isImmersion_projectiveSpace`, and this immersion is quasi-compact
since `V` is quasi-compact and `ℙ(n; S)` is quasi-compact and quasi-separated, being proper
over `S`; so its scheme-theoretic image does the job. This is the form of step 3 used in the
non-Noetherian variant of Chow's lemma (blueprint `rem-chow-lemma-non-noetherian`). -/
@[stacks 01RG "combined with 0203"]
theorem nonempty_properClosedModel_of_quasiSeparatedSpace {V S : Scheme.{u}} [IsAffine V]
    [CompactSpace S] [QuasiSeparatedSpace S] (g : V ⟶ S) [LocallyOfFiniteType g] :
    Nonempty (ProperClosedModel g) := by
  obtain ⟨n, hn, j, hj, hjg⟩ := exists_isImmersion_projectiveSpace g
  -- `ℙ(n; S)` is quasi-compact and quasi-separated, hence `j` is quasi-compact.
  have : CompactSpace ℙ(n; S) := QuasiCompact.compactSpace_of_compactSpace (ℙ(n; S) ↘ S)
  have : QuasiSeparatedSpace ℙ(n; S) := quasiSeparatedSpace_of_quasiSeparated (ℙ(n; S) ↘ S)
  have : QuasiCompact j := (quasiCompact_iff_compactSpace j).mpr inferInstance
  exact ⟨{ n := n
           Z := j.image
           emb := j.imageι
           ι := j.toImage
           w := by rw [j.toImage_imageι_assoc, hjg] }⟩

/-- **Step 3 of the proof of Chow's lemma.** An affine scheme `V` locally of finite type over a
Noetherian scheme `S` admits a proper closed model: a closed subscheme `Z` of some projective
space `ℙ(n; S)` with `n` finite, containing `V` as a scheme-theoretically dense open subscheme
and proper over `S`. This is the special case of
`AlgebraicGeometry.nonempty_properClosedModel_of_quasiSeparatedSpace` for a Noetherian `S`. -/
@[stacks 01RG "combined with 0200, step 3 of the proof"]
theorem nonempty_properClosedModel {V S : Scheme.{u}} [IsAffine V] [IsNoetherian S] (g : V ⟶ S)
    [LocallyOfFiniteType g] :
    Nonempty (ProperClosedModel g) :=
  nonempty_properClosedModel_of_quasiSeparatedSpace g

end AlgebraicGeometry
