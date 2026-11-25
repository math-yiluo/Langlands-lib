/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Descent of a finite etale cover from a stalk family

## References

* Stacks Project, Tags 0BQ5 and 0EY3, object descent in their proofs
* Stacks Project, Tag 0BQ5, the paragraph expressing the stalk
  spectrum as a limit, and Tag 0EY3, property descent,
  relative to `C`
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Refine an existing finitely presented cartesian model using Tags 01ZO and 07RP.
private theorem exists_finiteEtale_refinement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Limits.Cone D) (hc : Limits.IsLimit c)
    {X : Scheme.{u}} (g : X ⟶ c.pt) [IsFinite g] [Etale g]
    (i : Iᵒᵖ) (W : Scheme.{u}) (p : W ⟶ D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (h : X ⟶ W) (H : IsPullback h g p (c.π.app i)) :
    ∃ (r : I) (_ : i.unop ≤ r) (W : Scheme.{u})
      (p : W ⟶ D.obj (Opposite.op r))
      (_ : IsFinite p) (_ : Etale p) (h : X ⟶ W),
      IsPullback h g p (c.π.app (Opposite.op r)) := by
  classical
  have : Nonempty I := ⟨i.unop⟩
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
  have : LocallyOfFinitePresentation φ.left :=
    inferInstanceAs (LocallyOfFinitePresentation p)
  have hf : IsFinite (Limits.pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have he : Etale (Limits.pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have property_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      {T : Scheme.{u}} (q : T ⟶ D.obj i) :
      P (Limits.pullback.snd p q) ↔
        P (((Over.pullback q).map φ).left) := by
    have heq : ((Over.pullback q).map φ).left ≫ Limits.pullback.snd (𝟙 _) q =
        Limits.pullback.snd p q := by simp [φ]
    rw [← heq, P.cancel_right_of_respectsIso]
  obtain ⟨j, hj, hfin⟩ := exists_isFinite_baseChange_stage D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((property_iff @IsFinite (c.π.app i)).mp hf)
  obtain ⟨k, hk, het⟩ := Etale.exists_stage_of_inverseLimit D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((property_iff @Etale (c.π.app i)).mp he)
  obtain ⟨r, hjr, hkr⟩ := exists_ge_ge j k
  let a : Opposite.op r ⟶ i := (homOfLE (hj.trans hjr)).op
  let q := D.map a
  have hfin' : IsFinite (Limits.pullback.snd p q) := by
    apply MorphismProperty.of_isPullback
      (P := @IsFinite) (Limits.isPullback_pullback_map p q
        (D.map (homOfLE hj).op) (D.map (homOfLE hjr).op) ?_)
      ((property_iff @IsFinite _).mpr hfin)
    dsimp [q]
    rw [← D.map_comp]
    congr 1
  have het' : Etale (Limits.pullback.snd p q) := by
    apply MorphismProperty.of_isPullback
      (P := @Etale) (Limits.isPullback_pullback_map p q
        (D.map (homOfLE hk).op) (D.map (homOfLE hkr).op) ?_)
      ((property_iff @Etale _).mpr het)
    dsimp [q]
    rw [← D.map_comp]
    congr 1
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
  exact ⟨r, hj.trans hjr, Limits.pullback p q, Limits.pullback.snd p q, hfin',
    het', t, H'⟩

/-- A finite etale cover of the stalk family has a model on an open neighbourhood. -/
theorem FiniteEtale.exists_stalk_neighbourhood_model {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (s : S) (Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale) :
    ∃ (W : S.Opens), s ∈ W ∧
      ∃ (R : (c ⁻¹ᵁ W).toScheme.FiniteEtale)
        (l : Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ W).toScheme),
        l ≫ (c ⁻¹ᵁ W).ι = pullback.fst c (S.fromSpecStalk s) ∧
          Nonempty ((FiniteEtale.pullback l).obj R ≅ Q) := by
  classical
  let N := {W : S.Opens // IsAffineOpen W ∧ s ∈ W}
  let I := OrderDual N
  obtain ⟨_, hne, hdir, _, _, _, _, _, hcompat, huniv⟩ :=
    S.fromSpecStalk_limit_affine_neighbourhoods s
  let : Nonempty I := hne
  let : IsDirected I (· ≤ ·) := ⟨fun W V ↦ by
    obtain ⟨Z, hZ⟩ := hdir W V
    exact ⟨Z, hZ.trans inf_le_left, hZ.trans inf_le_right⟩⟩
  let : IsFiltered I := inferInstance
  let : IsCofiltered Iᵒᵖ := inferInstance
  let : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  let R := (orderDualEquivalence N).leftOp.functor
  let D₀ : N ⥤ Scheme.{u} :=
    { obj := fun W ↦ W.1.toScheme
      map := fun a ↦ S.homOfLE (leOfHom a)
      map_id := fun W ↦ S.homOfLE_rfl W.1
      map_comp := fun a b ↦ (S.homOfLE_homOfLE _ _).symm }
  let b₀ : Cone D₀ :=
    { pt := Spec (S.presheaf.stalk s)
      π :=
        { app := fun W ↦ W.1.fromSpecStalkOfMem s W.2.2
          naturality := fun W V a ↦ (hcompat V W (leOfHom a)).symm } }
  have hb₀ : IsLimit b₀ := by
    apply IsLimit.ofExistsUnique
    intro t
    obtain ⟨f, hf, huniq⟩ := huniv t.pt t.π.app (fun W V h ↦ t.w (homOfLE h))
    exact ⟨f, hf, fun g hg ↦ huniq g hg⟩
  let D := R ⋙ D₀
  let b := b₀.whisker R
  have hb : IsLimit b :=
    (Functor.Initial.isLimitWhiskerEquiv R b₀).symm hb₀
  let p : D ⟶ (Functor.const Iᵒᵖ).obj S :=
    { app := fun i ↦ (R.obj i).1.ι
      naturality := by intro i j a; simp [D, D₀, homOfLE_ι] }
  have hbp (i : Iᵒᵖ) : b.π.app i ≫ p.app i = S.fromSpecStalk s :=
    (R.obj i).1.fromSpecStalkOfMem_ι s (R.obj i).2.2
  let E : Iᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun i ↦ Limits.pullback c (p.app i)
      map := fun a ↦ Limits.pullback.map _ _ _ _ (𝟙 C) (D.map a) (𝟙 S)
        (by simp) (by simp [p.naturality a])
      map_id := by intro i; apply Limits.pullback.hom_ext <;> simp
      map_comp := by intro i j k a b; apply Limits.pullback.hom_ext <;> simp }
  let ρ : E ⟶ D := { app := fun i ↦ Limits.pullback.snd c (p.app i) }
  let d : Cone E :=
    { pt := Limits.pullback c (S.fromSpecStalk s)
      π :=
        { app := fun i ↦ Limits.pullback.map _ _ _ _ (𝟙 C) (b.π.app i) (𝟙 S)
            (by simp) (by simpa using (hbp i).symm)
          naturality := by
            intro i j a
            apply Limits.pullback.hom_ext
            · simp [E]
            · simp only [E, Limits.pullback.map, Functor.const_obj_obj, Functor.const_obj_map,
                Category.id_comp, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
                Category.assoc]
              exact congrArg (Limits.pullback.snd c (S.fromSpecStalk s) ≫ ·) (b.w a).symm } }
  let v : (Cone.postcompose ρ).obj d ⟶ b :=
    { hom := Limits.pullback.snd _ _
      w := by intro i; simp [d, ρ] }
  have hd : IsLimit d := isLimitOfIsPullbackOfIsConnected ρ d b v
    (fun i ↦ isPullback_pullback_map c _ _ (b.π.app i) (hbp i)) hb
  have (i : Iᵒᵖ) : IsAffine (D.obj i) := (R.obj i).2.1
  have (i : Iᵒᵖ) : CompactSpace (E.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd c (p.app i))
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (E.obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd c (p.app i))
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) := by
    let : IsAffine (R.obj i).1.toScheme := (R.obj i).2.1
    let : IsAffine (R.obj j).1.toScheme := (R.obj j).2.1
    dsimp [D, D₀]
    infer_instance
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (E.map a) :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_map c (p.app i) (p.app j) (D.map a)
        (by simp [p.naturality a])).flip inferInstance
  have : IsFinite Q.obj.hom := Q.property
  obtain ⟨i₀, P₀, π₀, hfp, hqc, hqs, ψ₀, H₀⟩ :=
    exists_isPullback_of_finitePresentation (D := E) (c := d) hd Q.obj.hom
  have := hfp
  have := hqc
  have := hqs
  obtain ⟨i, _, P, π, hfin, het, ψ, H⟩ :=
    exists_finiteEtale_refinement E d hd Q.obj.hom i₀ P₀ π₀ ψ₀ H₀
  let W := (R.obj (Opposite.op i)).1
  let t : (c ⁻¹ᵁ W).toScheme ≅ E.obj (Opposite.op i) :=
    (isPullback_morphismRestrict c W).flip.isoPullback
  let l := d.π.app (Opposite.op i) ≫ t.inv
  have hl : l ≫ (c ⁻¹ᵁ W).ι = Limits.pullback.fst c (S.fromSpecStalk s) := by
    dsimp [l]
    rw [Category.assoc, IsPullback.isoPullback_inv_fst]
    change Limits.pullback.map c (S.fromSpecStalk s) c W.ι (𝟙 C)
      (b.π.app (Opposite.op i)) (𝟙 S) (by simp)
      (by simpa using (hbp (Opposite.op i)).symm) ≫ Limits.pullback.fst c W.ι = _
    simp
  have := hfin
  have := het
  let f := π ≫ t.inv
  have : Etale f := by dsimp [f]; infer_instance
  have : IsFinite f := by dsimp [f]; infer_instance
  let V : (c ⁻¹ᵁ W).toScheme.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
  have H' : IsPullback ψ Q.obj.hom f l :=
    H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) t.symm
      (by simp) (by simp) (by simp [f]) (by simp [l])
  refine ⟨W, (R.obj (Opposite.op i)).2.2, V, l, hl, ?_⟩
  exact ⟨ObjectProperty.isoMk _
    (MorphismProperty.Over.isoMk H'.isoPullback.symm H'.isoPullback_inv_snd)⟩

end AlgebraicGeometry.Scheme
