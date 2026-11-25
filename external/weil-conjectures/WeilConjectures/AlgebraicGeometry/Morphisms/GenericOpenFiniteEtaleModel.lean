/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Spreading a generic finite étale cover to an open

## References

* Stacks Project, Tag 0EYJ (choice of an initial open), Tag 01ZM (descending finite presentation),
  Tag 01ZO (finiteness), and Tag 07RP (étaleness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem property_pullback_snd_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X S T : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) :
    P (Limits.pullback.snd p q) ↔
      P (((Over.pullback q).map (Over.homMk p (by simp) :
        Over.mk p ⟶ Over.mk (𝟙 S))).left) := by
  have he : (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫ Limits.pullback.snd (𝟙 S) q =
      Limits.pullback.snd p q := by simp
  rw [← he, P.cancel_right_of_respectsIso]

private theorem property_pullback_snd_mono
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X S T T' : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) (q' : T' ⟶ S)
    (r : T' ⟶ T) (hr : r ≫ q = q') (hp : P (Limits.pullback.snd p q)) :
    P (Limits.pullback.snd p q') := by
  exact P.of_isPullback (Limits.isPullback_pullback_map p q' q r hr) hp

-- Assemble Tags 01ZM, 01ZO, and 07RP for a finite étale morphism.
-- The pullback bookkeeping follows the proved helper in FiniteEtaleAlgebraStage.
private theorem exists_finiteEtale_limit_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Limits.Cone D) (hc : Limits.IsLimit c)
    {X : Scheme.{u}} (g : X ⟶ c.pt) [IsFinite g] [Etale g] :
    ∃ (i : I) (W : Scheme.{u}) (p : W ⟶ D.obj (Opposite.op i))
      (_ : IsFinite p) (_ : Etale p) (h : X ⟶ W),
      IsPullback h g p (c.π.app (Opposite.op i)) := by
  classical
  obtain ⟨i, W, p, hp, hqc, hqs, h, H⟩ :=
    exists_isPullback_of_finitePresentation (D := D) (c := c) hc g
  have := hp
  have := hqc
  have := hqs
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace (Over.mk p).left := inferInstanceAs (CompactSpace W)
  have : QuasiSeparatedSpace (Over.mk p).left :=
    inferInstanceAs (QuasiSeparatedSpace W)
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let φ : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p (by simp)
  have : LocallyOfFinitePresentation φ.left := hp
  have hf : IsFinite (Limits.pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have he : Etale (Limits.pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j, hj, hfin⟩ := exists_isFinite_baseChange_stage D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((property_pullback_snd_iff @IsFinite p (c.π.app i)).mp hf)
  obtain ⟨k, hk, het⟩ := Etale.exists_stage_of_inverseLimit D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((property_pullback_snd_iff @Etale p (c.π.app i)).mp he)
  obtain ⟨r, hjr, hkr⟩ := exists_ge_ge j k
  let a : Opposite.op r ⟶ i := (homOfLE (hj.trans hjr)).op
  let q := D.map a
  have hfin' : IsFinite (Limits.pullback.snd p q) := by
    apply property_pullback_snd_mono @IsFinite p (D.map (homOfLE hj).op) q
      (D.map (homOfLE hjr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (property_pullback_snd_iff @IsFinite p _).mpr hfin
  have het' : Etale (Limits.pullback.snd p q) := by
    apply property_pullback_snd_mono @Etale p (D.map (homOfLE hk).op) q
      (D.map (homOfLE hkr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (property_pullback_snd_iff @Etale p _).mpr het
  let t : X ⟶ Limits.pullback p q := Limits.pullback.lift h (g ≫
    c.π.app (Opposite.op r))
    (by change h ≫ p = (g ≫ c.π.app (Opposite.op r)) ≫ D.map a
        rw [Category.assoc, c.w a]; exact H.w)
  have H' : IsPullback t g (Limits.pullback.snd p q) (c.π.app (Opposite.op r)) := by
    apply IsPullback.of_right (h₁₂ := Limits.pullback.fst p q) (h₂₂ := q)
    · convert H using 1
      · simp [t]
      · exact c.w a
    · simp [t]
    · exact IsPullback.of_hasPullback p q
  exact ⟨r, Limits.pullback p q, Limits.pullback.snd p q, hfin',
    het', t, H'⟩

/-- A finite étale torsor on the generic fibre spreads over an open containing the generic
point. No normality, section, or invertibility assumption is needed for this step. -/
theorem GaloisCover.exists_generic_open_finiteEtale_model {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη) :
    ∃ U : S.Opens, genericPoint S ∈ U ∧
      ∃ (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (P : Scheme.{u})
        (π : P ⟶ (c ⁻¹ᵁ U).toScheme) (ψ : Z.P ⟶ P),
        jU ≫ (c ⁻¹ᵁ U).ι = j ∧ IsFinite π ∧ Etale π ∧ IsPullback ψ Z.π π jU := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    -- Reindex by the opposite of an increasing directed set for the descent interfaces.
    let I := OrderDual S.NonemptyAffineOpens
    have : IsDirected I (· ≤ ·) := inferInstanceAs
      (IsDirected S.NonemptyAffineOpens (· ≥ ·))
    have : Nonempty I := inferInstanceAs (Nonempty S.NonemptyAffineOpens)
    have : IsFiltered I := inferInstance
    have : IsCofiltered Iᵒᵖ := inferInstance
    have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
    let R := (orderDualEquivalence S.NonemptyAffineOpens).leftOp.functor
    let D := R ⋙ S.affineOpensDiagram
    let b := S.functionFieldCone.whisker R
    have hb : Limits.IsLimit b :=
      (Functor.Initial.isLimitWhiskerEquiv R S.functionFieldCone).symm
        S.isLimitFunctionFieldCone
    let p : D ⟶ (Functor.const Iᵒᵖ).obj S :=
      { app := fun i ↦ S.affineOpensDiagramι.app (R.obj i)
        naturality := fun i j a ↦ S.affineOpensDiagramι.naturality (R.map a) }
    have hbp (i : Iᵒᵖ) : b.π.app i ≫ p.app i = S.fromSpecFunctionField :=
      (S.fromSpecFunctionField_eq_functionFieldCone_comp (R.obj i)).symm
    -- Pull back the affine-neighbourhood system to the qcqs family.
    let E : Iᵒᵖ ⥤ Scheme.{u} :=
      { obj := fun i ↦ Limits.pullback c (p.app i)
        map := fun a ↦ Limits.pullback.map _ _ _ _ (𝟙 C) (D.map a) (𝟙 S)
          (by simp) (by simp [p.naturality a])
        map_id := by intro i; apply Limits.pullback.hom_ext <;> simp
        map_comp := by intro i j k a b; apply Limits.pullback.hom_ext <;> simp }
    let ρ : E ⟶ D := { app := fun i ↦ Limits.pullback.snd c (p.app i) }
    let d : Limits.Cone E :=
      { pt := Limits.pullback c S.fromSpecFunctionField
        π :=
          { app := fun i ↦ Limits.pullback.map _ _ _ _ (𝟙 C) (b.π.app i) (𝟙 S)
              (by simp) (by simpa using (hbp i).symm)
            naturality := by
              intro i j a
              apply Limits.pullback.hom_ext
              · simp [E]
              · simp only [E, Limits.pullback.map, Functor.const_obj_obj,
                Functor.const_obj_map,
                  Category.id_comp, Limits.pullback.lift_snd,
                    Limits.pullback.lift_snd_assoc, Category.assoc]
                exact congrArg (Limits.pullback.snd c S.fromSpecFunctionField ≫ ·)
                  (b.w a).symm } }
    let v : (Limits.Cone.postcompose ρ).obj d ⟶ b :=
      { hom := Limits.pullback.snd _ _
        w := by intro i; simp [d, ρ] }
    have hd : Limits.IsLimit d := Limits.isLimitOfIsPullbackOfIsConnected ρ d b v
      (fun i ↦ Limits.isPullback_pullback_map c _ _ (b.π.app i) (hbp i)) hb
    have (i : Iᵒᵖ) : IsAffine (D.obj i) :=
      inferInstanceAs (IsAffine (Spec Γ(S, (R.obj i).1)))
    have (i : Iᵒᵖ) : CompactSpace (E.obj i) :=
      QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd c (p.app i))
    have (i : Iᵒᵖ) : QuasiSeparatedSpace (E.obj i) :=
      quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd c (p.app i))
    have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) := by
      dsimp [D, R, Scheme.affineOpensDiagram]
      infer_instance
    have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (E.map a) :=
      MorphismProperty.of_isPullback
        (Limits.isPullback_pullback_map c (p.app i) (p.app j) (D.map a)
          (by simp [p.naturality a])).flip inferInstance
    let e := hCη.flip.isoPullback
    have : IsIso e.hom := inferInstanceAs (IsIso hCη.flip.isoPullback.hom)
    have : IsFinite Z.π := Z.isFinite
    have : Etale Z.π := Z.etale
    let g : Z.P ⟶ d.pt := Z.π ≫ e.hom
    have : IsFinite g := by dsimp [g]; infer_instance
    have : Etale g := by dsimp [g]; infer_instance
    obtain ⟨i, P, π, hfin, het, ψ, H⟩ := exists_finiteEtale_limit_stage E d hd g
    -- Identify this affine-base-change stage with the corresponding open of C.
    let U := (R.obj (Opposite.op i)).1
    have hU : genericPoint S ∈ U := (R.obj (Opposite.op i)).genericPoint_mem
    have ht : IsPullback (c ⁻¹ᵁ U).ι
        ((c ∣_ U) ≫ (R.obj (Opposite.op i)).2.1.isoSpec.hom) c (p.app (Opposite.op i)) :=
      (isPullback_morphismRestrict c U).flip.of_iso
        (Iso.refl _) (Iso.refl _) (R.obj (Opposite.op i)).2.1.isoSpec (Iso.refl _)
        (by simp) (by simp) (by simp)
        (by exact (R.obj (Opposite.op i)).2.1.isoSpec_hom_fromSpec.symm)
    let t : (c ⁻¹ᵁ U).toScheme ≅ E.obj (Opposite.op i) := ht.isoPullback
    let jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme := e.hom ≫ d.π.app (Opposite.op i) ≫ t.inv
    have hjU : jU ≫ (c ⁻¹ᵁ U).ι = j := by
      dsimp [jU]
      simp only [Category.assoc]
      rw [show t.inv ≫ (c ⁻¹ᵁ U).ι = Limits.pullback.fst c (p.app (Opposite.op i))
        from
        ht.isoPullback_inv_fst]
      simp only [d, Limits.pullback.map, Limits.pullback.lift_fst,
        Category.comp_id]
      exact hCη.flip.isoPullback_hom_fst
    have := hfin
    have := het
    refine ⟨U, hU, jU, P, π ≫ t.inv, ψ, hjU, inferInstance, inferInstance, ?_⟩
    exact H.of_iso (Iso.refl _) (Iso.refl _) e.symm t.symm
      (by simp) (by simp [g]) (by simp) (by simp [jU])


end AlgebraicGeometry.Scheme
