/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of a proper-fibre idempotent to a Noetherian model

Source: Stacks Project, Tag 0G7X, general case before applying the Noetherian case.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem descend_idempotent
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Limits.Cone D) (hc : Limits.IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (e : Γ(c.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ (i : I) (e₀ : Γ(D.obj i, ⊤)),
      IsIdempotentElem e₀ ∧ (c.π.app i).appTop e₀ = e := by
  obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_of_isLimit D c hc e
  obtain ⟨j, h, hh⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (t * t - t) (by
    simp only [map_sub, map_mul, ← ht]
    exact sub_eq_zero.mpr he)
  refine ⟨j, (D.map h).appTop t, ?_, ?_⟩
  · exact sub_eq_zero.mp (by simpa only [map_sub, map_mul] using hh)
  · change ((c.π.app j ≫ D.map h).appTop) t = e
    rw [c.w h]
    exact ht.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem affine_fibre_idempotent_descent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (Y T : Scheme.{u}) (g : Y ⟶ T)
      (_ : IsProper g) (_ : IsLocallyNoetherian T)
      (p : X ⟶ Y) (r : S ⟶ T)
      (q : f.fiber s ⟶ g.fiber (r s)) (e₀ : Γ(g.fiber (r s), ⊤)),
      p ≫ g = f ≫ r ∧ q ≫ g.fiberι (r s) = f.fiberι s ≫ p ∧
      IsIdempotentElem e₀ ∧ q.appTop e₀ = e := by
  obtain ⟨I, hpre, hne, hdir, Xs, Ss, fs, πX, πS,
    ⟨hcX⟩, ⟨hcS⟩, htrans, hproper, hfinite, hcomm, _⟩ :=
    exists_proper_limit_noetherian f
  let : Preorder I := hpre
  let : Nonempty I := hne
  let : IsDirected I (· ≤ ·) := hdir
  let cX := Limits.Cone.mk X πX
  let cS := Limits.Cone.mk S πS
  have instX {i j : Iᵒᵖ} (h : i ⟶ j) : IsAffineHom (Xs.map h) := (htrans i j h).1
  have instS {i j : Iᵒᵖ} (h : i ⟶ j) : IsAffineHom (Ss.map h) := (htrans i j h).2
  obtain ⟨Q, a, cQ, hQ, ha, hQa, hpt, hπ, ⟨hlim⟩⟩ :=
    (limit_fibre_products_of_affine_transition Xs Ss Ss fs (𝟙 Ss)
      cX hcX cS hcS cS hcS f (𝟙 S) (fun i ↦ (hcomm i).symm)
      (fun i ↦ by
        change 𝟙 S ≫ πS.app i = πS.app i ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm)).2 s
  dsimp [cX, cS] at hQ ha hπ
  have instQ {i j : Iᵒᵖ} (h : i ⟶ j) : IsAffineHom (Q.map h) := hQa h
  have instCompact (i : Iᵒᵖ) : CompactSpace (Q.obj i) := by
    rw [hQ i]
    let := hproper i
    infer_instance
  have instQS (i : Iᵒᵖ) : QuasiSeparatedSpace (Q.obj i) := by
    rw [hQ i]
    let := hproper i
    let : QuasiSeparated ((fs.app i).fiberToSpecResidueField (πS.app i s)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated ((fs.app i).fiberToSpecResidueField _)
  let c : Limits.Cone Q := cQ.extend (eqToHom hpt.symm)
  have hc : Limits.IsLimit c :=
    hlim.ofIsoLimit (Limits.Cone.extendIso cQ (eqToIso hpt))
  obtain ⟨i, t, ht, hte⟩ := descend_idempotent Q c hc e he
  let b : Q.obj i ≅ (fs.app i).fiber (πS.app i s) := eqToIso (hQ i)
  have hn : IsLocallyNoetherian (Ss.obj i) := by
    let := (hfinite i).1
    let : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from (Ss.obj i))
  refine ⟨Xs.obj i, Ss.obj i, fs.app i, hproper i, hn,
    πX.app i, πS.app i, c.π.app i ≫ b.hom, b.inv.appTop t, hcomm i, ?_, ?_, ?_⟩
  · have hι : b.hom ≫ (fs.app i).fiberι (πS.app i s) = a.app i := by
      apply eq_of_heq
      dsimp [b, eqToIso]
      simpa only [eqToHom_comp_heq_iff] using (ha i).symm
    refine (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ c.π.app i ≫ k) hι).trans ?_)
    have hh := hπ i
    dsimp [c, Limits.Cone.extend]
    apply eq_of_heq
    simpa only [Category.assoc, eqToHom_comp_heq_iff] using hh
  · exact ht.map b.inv.appTop.hom
  · change ((c.π.app i ≫ b.hom) ≫ b.inv).appTop t = e
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using hte

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An idempotent on a proper fibre descends to a proper morphism over a locally
Noetherian base, together with the commuting maps on schemes and fibres.
Source: Stacks, Tag 0G7X, Steps 5--8. First restrict the base to an affine
neighbourhood of s and apply proper Noetherian approximation. The residue field of s
is the filtered colimit of the stage residue fields, so the fibre is the inverse limit
of the stage fibres with affine transitions. Global sections commute with that limit:
descend e to a stage, then descend its equation e * e = e to a later stage. The
Noetherian model is that stage and the projections provide p, r and q. Commutation
with the fibre embeddings is the defining property of the induced fibre projections.
This statement asks for no section on a neighbourhood of s.
(blueprint: lem-weil-pbc-stein-fibre-idempotent-descent) -/
theorem proper_fibre_idempotent_descent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (W : S.Opens) (hs : s ∈ W) (Y T : Scheme.{u}) (g : Y ⟶ T)
      (_ : IsProper g) (_ : IsLocallyNoetherian T)
      (p : (f ⁻¹ᵁ W).toScheme ⟶ Y) (r : W.toScheme ⟶ T)
      (a : f.fiber s ⟶ (f ⁻¹ᵁ W).toScheme)
      (q : f.fiber s ⟶ g.fiber (r ⟨s, hs⟩)) (e₀ : Γ(g.fiber (r ⟨s, hs⟩), ⊤)),
      p ≫ g = (f ∣_ W) ≫ r ∧ a ≫ (f ⁻¹ᵁ W).ι = f.fiberι s ∧
      q ≫ g.fiberι (r ⟨s, hs⟩) = a ≫ p ∧
      IsIdempotentElem e₀ ∧ q.appTop e₀ = e := by
  obtain ⟨W, hW, hs, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) (by simp)
  let : IsAffine W.toScheme := hW
  let fW := f ∣_ W
  let sW : W.toScheme := ⟨s, hs⟩
  let k : fW.fiber sW ⟶ f.fiber s :=
    Limits.pullback.map fW (W.toScheme.fromSpecResidueField sW)
      f (S.fromSpecResidueField s) (f ⁻¹ᵁ W).ι
      (Spec.map (W.ι.residueFieldMap sW)) W.ι
      (morphismRestrict_ι f W)
      (W.ι.SpecMap_residueFieldMap_fromSpecResidueField sW).symm
  have hk : IsPullback k (fW.fiberToSpecResidueField sW)
      (f.fiberToSpecResidueField s) (Spec.map (W.ι.residueFieldMap sW)) :=
    isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_morphismRestrict f W).flip sW
  let : IsIso k := hk.isIso_fst_of_isIso
  have hkι : k ≫ f.fiberι s = fW.fiberι sW ≫ (f ⁻¹ᵁ W).ι :=
    by
      simp only [k, Scheme.Hom.fiberι, Limits.pullback.map, Limits.pullback.lift_fst]
  obtain ⟨Y, T, g, hg, hT, p, r, q, e₀, hpg, hq, he₀, hqe⟩ :=
    affine_fibre_idempotent_descent fW sW (k.appTop e) (he.map k.appTop.hom)
  refine ⟨W, hs, Y, T, g, hg, hT, p, r, inv k ≫ fW.fiberι sW,
    inv k ≫ q, e₀, hpg, ?_, ?_, he₀, ?_⟩
  · rw [Category.assoc, ← hkι, IsIso.inv_hom_id_assoc]
  · rw [Category.assoc, hq, Category.assoc]
  · change (inv k).appTop (q.appTop e₀) = e
    rw [hqe]
    change (inv k ≫ k).appTop e = e
    simp only [IsIso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

end AlgebraicGeometry
