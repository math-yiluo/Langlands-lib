/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventually affine stages in an inverse system

Source: Stacks Project, Limits, Lemma 09ZM (limits.tex, lines 891--911)
(blueprint: lem-weil-pbc-eventually-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- If an inverse system of quasi-compact, quasi-separated schemes over a
quasi-compact, quasi-separated base has affine transition maps and affine
limit morphism, then all sufficiently late structure morphisms are affine.

Source: Stacks Project, Limits, Lemma 09ZM, proof lines 902--911.
(blueprint: lem-weil-pbc-eventually-affine)
The structure maps hᵢ of the node are `h.app (op i)`; its induced limit map h is `f`.
Proof:
1. Fix an index b. Its upper tail is directed and cofinal. Choose a finite affine open
   cover V₁, …, Vₙ of T; n may be zero (def-pc-scheme,
   definition-ind-etale-pro-etale-weakly--3).
2. Put Wⱼᵢ = hᵢ⁻¹(Vⱼ) and Wⱼ = f⁻¹(Vⱼ). Compatibility identifies these on the
   tail with inverse images of Wⱼᵦ under the transition maps and the limit projection.
   Wⱼ is affine because f is affine (pqf-def-affine-morphism). Each Wⱼᵢ is qcqs:
   the qcqs source and quasi-separated target make hᵢ qcqs
   (lem-weil-pbc-qcqs-morphism-permanence); restriction to Vⱼ is its base change
   (lem-weil-pbc-open-preimage-fibre-product), so it is qcqs over an affine scheme
   (lem-weil-pbc-qcqs-over-affine).
3. Restrict the limit cone to Wⱼᵦ on the upper tail. This gives Wⱼ as the limit of
   Wⱼᵢ, with affine transition maps (lem-weil-pbc-limit-cone-affine-projections-opens).
4. Apply the absolute affine-limit lemma to each such qcqs system with affine limit
   (lem-weil-pbc-limit-affine-stage, `Scheme.exists_isAffine_of_isLimit`). It gives
   an affine stage; every later stage is affine by its affine transition to that stage.
5. Directedness gives a common upper bound i₀ for b and the finitely many selected
   indices (take b if n = 0). At every i ≥ i₀ the preimages of all Vⱼ are affine;
   hence hᵢ is affine since affineness is local on the target
   (pqf-lem-affine-local-target). -/
theorem eventually_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsAffineHom f] :
    ∃ i : I, ∀ j : I, i ≤ j → IsAffineHom (h.app (op j)) := by
  classical
  let b : Iᵒᵖ := op (Classical.choice inferInstance)
  let 𝒰 := T.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  let V (a : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f a).opensRange,
    isAffineOpen_opensRange (𝒰.f a)⟩
  have H (a : 𝒰.I₀) : ∃ k : Over b, IsAffineOpen (h.app k.left ⁻¹ᵁ (V a).1) := by
    let U := h.app b ⁻¹ᵁ (V a).1
    have : QuasiCompact (h.app b) := by
      change QuasiCompact (show D.obj b ⟶ T from h.app b)
      infer_instance
    have hU : IsCompact (U : Set (D.obj b)) :=
      QuasiCompact.isCompact_preimage (f := h.app b) _ (V a).1.isOpen (V a).2.isCompact
    have (k : Over b) : CompactSpace ((opensDiagram D b U).obj k) :=
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage (f := D.map k.hom) _ U.isOpen hU)
    have (k : Over b) : QuasiSeparatedSpace ((opensDiagram D b U).obj k) :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map k.hom ⁻¹ᵁ U).isOpen).mp
        (.of_quasiSeparatedSpace _)
    have : IsAffine (opensCone D c b U).pt := by
      change IsAffineOpen (c.π.app b ⁻¹ᵁ U)
      simpa [U, ← Scheme.Hom.comp_preimage, _hf b] using (V a).2.preimage f
    obtain ⟨k, hk⟩ := Scheme.exists_isAffine_of_isLimit
      (opensDiagram D b U) (opensCone D c b U) (isLimitOpensCone D c _hc b U)
    refine ⟨k, ?_⟩
    change IsAffineOpen (D.map k.hom ⁻¹ᵁ U) at hk
    simpa [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom] using hk
  choose k hk using H
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image (fun a ↦ (k a).left))
  have gi (a : 𝒰.I₀) : i ⟶ (k a).left := (hi (by simp)).some
  refine ⟨i.unop, fun j hij ↦ ?_⟩
  let g : op j ⟶ i := (homOfLE hij).op
  apply HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom) V 𝒰.iSup_opensRange
  intro a
  change IsAffineOpen (h.app (op j) ⁻¹ᵁ (V a).1)
  have ha := (hk a).preimage (D.map (g ≫ gi a))
  simpa [← Scheme.Hom.comp_preimage, h.naturality (g ≫ gi a)] using ha

end AlgebraicGeometry
