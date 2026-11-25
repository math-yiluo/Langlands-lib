/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcDescendingTypesMorphisms
import WeilConjectures.AlgebraicGeometry.AffineFlatDescent

/-! Effective fpqc descent of affine morphisms.
Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245).
(blueprint: lem-galois-fpqc-affine-descent-effective)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

set_option backward.isDefEq.respectTransparency false in
private theorem isAffineHom_sigmaMap (m : ℕ) (Y V : Fin m → Scheme.{u})
    (g : ∀ i, Y i ⟶ V i) (hg : ∀ i, IsAffineHom (g i)) :
    IsAffineHom (Limits.Sigma.map g) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) (sigmaOpenCover V)
  intro i
  have hsq : IsPullback (g i) (Sigma.ι Y i) (Sigma.ι V i) (Limits.Sigma.map g) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
    apply le_antisymm
    · rintro x ⟨y, hxy⟩
      obtain ⟨j, x, rfl⟩ := (sigmaOpenCover Y).exists_eq x
      simp only [sigmaOpenCover_f, ← Scheme.Hom.comp_apply, Sigma.ι_map] at hxy
      have hij : i = j := by
        simpa only [Sigma.mk.injEq] using congrArg Sigma.fst
          ((sigmaι_eq_iff V _ _ y _).mp hxy)
      subst j
      exact ⟨x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨g i x, by simp only [← Scheme.Hom.comp_apply, Sigma.ι_map]⟩
  have : IsAffineHom (g i) := hg i
  change IsAffineHom (pullback.snd (Limits.Sigma.map g) (Sigma.ι V i))
  rw [← hsq.flip.isoPullback_inv_snd]
  infer_instance

/-- For a singleton fpqc covering `p : X ⟶ Y`, a descent datum on an affine
`X`-scheme is effective (Stacks Project, Descent, Lemma 35.37.1, Tag 0245).

The fpqc reduction applies to the affine morphism property. Base change stability is
`MorphismProperty.pullback_snd`; finite coproduct stability is the proved helper
`isAffineHom_sigmaMap`; the affine flat case is `isEffective_of_isAffineHom_flat_affine`.

(blueprint: lem-galois-fpqc-affine-descent-effective) -/
theorem isEffective_of_isAffineHom_fpqc {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y) {V : Over X}
    [IsAffineHom V.hom] (D : Over.DescentDatum p V) : D.IsEffective := by
  refine fpqcDescentEffective_of_affine (@IsAffineHom) ?_
    (fun m Y V g hg => isAffineHom_sigmaMap m Y V g hg) ?_ p hp D inferInstance
  · intro Y V V' g h hg
    exact MorphismProperty.pullback_snd g h hg
  · intro X S _ _ f hf hs V D hV
    let : IsAffineHom V.hom := hV
    exact isEffective_of_isAffineHom_flat_affine f hf hs D

end CategoryTheory.Over.DescentDatum
