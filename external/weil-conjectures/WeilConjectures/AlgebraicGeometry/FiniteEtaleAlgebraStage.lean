/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Descent to a finitely presented algebra

Source: Stacks Project, Tag 0GS2, proof.
(blueprint: lem-weil-pbc-finite-etale-algebra-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private def algebraDiagram (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    {S : Subalgebra A B // S.FG} ⥤ CommRingCat.{u} where
  obj S := .of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

private def algebraCocone (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Cocone (algebraDiagram A B) where
  pt := .of B
  ι := { app S := CommRingCat.ofHom S.1.val.toRingHom }

private theorem algebraCocone_isColimit
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsColimit (algebraCocone A B)) := by
  classical
  have hsup : ⨆ S : {S : Subalgebra A B // S.FG}, S.1.restrictScalars ℤ = ⊤ := by
    apply top_unique
    intro x _
    exact Algebra.mem_iSup_of_mem
      (S := fun S : {S : Subalgebra A B // S.FG} ↦ S.1.restrictScalars ℤ)
      (Subalgebra.fgAdjoinSingleton A B x) (Subalgebra.self_mem_fgAdjoinSingleton A B x)
  have hdir : Directed (· ≤ ·)
      (fun S : {S : Subalgebra A B // S.FG} ↦ S.1.restrictScalars ℤ) :=
    Monotone.directed_le (fun _ _ h _ hx ↦ (show _ ≤ _ from (Subtype.coe_le_coe.mpr h)) hx)
  let desc (s : Cocone (algebraDiagram A B)) : B →+* s.pt :=
    ((Subalgebra.iSupLift
      (fun S : {S : Subalgebra A B // S.FG} ↦ S.1.restrictScalars ℤ) hdir
      (fun S ↦ by exact (s.ι.app S).hom.toIntAlgHom)
      (fun S T h ↦ AlgHom.ext fun x ↦
        (ConcreteCategory.congr_hom (s.w (homOfLE
          (Subtype.coe_le_coe.mp (fun _ hx ↦ h hx)))) x).symm)
      ⊤ hsup.ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom
  have hdesc (s : Cocone (algebraDiagram A B))
      (S : {S : Subalgebra A B // S.FG}) (x : S.1) :
      desc s (S.1.val x) = (s.ι.app S).hom x := by
    have h : Subalgebra.topEquiv.symm.toAlgHom (S.1.val x) =
        Subalgebra.inclusion (le_top : S.1.restrictScalars ℤ ≤ ⊤) x := Subtype.ext rfl
    simp only [desc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, h,
      Subalgebra.iSupLift_inclusion]
    rfl
  refine ⟨{ desc := fun s ↦ CommRingCat.ofHom (desc s)
            fac := ?_
            uniq := ?_ }⟩
  · intro s S
    ext x
    exact hdesc s S x
  · intro s m hm
    ext x
    let S := Subalgebra.fgAdjoinSingleton A B x
    let y : S.1 := ⟨x, Subalgebra.self_mem_fgAdjoinSingleton A B x⟩
    exact (ConcreteCategory.congr_hom (hm S) y).trans (hdesc s S y).symm

private theorem property_pullback_snd_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X S T : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) :
    P (pullback.snd p q) ↔
      P (((Over.pullback q).map (Over.homMk p (by simp) :
        Over.mk p ⟶ Over.mk (𝟙 S))).left) := by
  have he : (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫ pullback.snd (𝟙 S) q =
      pullback.snd p q := by simp
  rw [← he, P.cancel_right_of_respectsIso]

private theorem property_pullback_snd_mono
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X S T T' : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) (q' : T' ⟶ S)
    (r : T' ⟶ T) (hr : r ≫ q = q') (hp : P (pullback.snd p q)) :
    P (pullback.snd p q') := by
  exact P.of_isPullback (isPullback_pullback_map p q' q r hr) hp

private theorem exists_finiteEtale_limit_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
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
  have hf : IsFinite (pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have he : Etale (pullback.snd p (c.π.app i)) := by
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
  have hfin' : IsFinite (pullback.snd p q) := by
    apply property_pullback_snd_mono @IsFinite p (D.map (homOfLE hj).op) q
      (D.map (homOfLE hjr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (property_pullback_snd_iff @IsFinite p _).mpr hfin
  have het' : Etale (pullback.snd p q) := by
    apply property_pullback_snd_mono @Etale p (D.map (homOfLE hk).op) q
      (D.map (homOfLE hkr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (property_pullback_snd_iff @Etale p _).mpr het
  let t : X ⟶ pullback p q := pullback.lift h (g ≫ c.π.app (Opposite.op r))
    (by change h ≫ p = (g ≫ c.π.app (Opposite.op r)) ≫ D.map a
        rw [Category.assoc, c.w a]; exact H.w)
  have H' : IsPullback t g (pullback.snd p q) (c.π.app (Opposite.op r)) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst p q) (h₂₂ := q)
    · convert H using 1
      · simp [t]
      · exact c.w a
    · simp [t]
    · exact IsPullback.of_hasPullback p q
  exact ⟨r, pullback p q, pullback.snd p q, hfin', het', t, H'⟩

/-- A finite étale cover after an arbitrary algebra base change descends to a finitely
presented algebra stage.
Source: Stacks Project, Tag 0GS2, proof, lines 1823–1829; Limits, Tags 01ZM, 01ZO, 07RP
(blueprint: lem-weil-pbc-finite-etale-algebra-stage).

Proof: Express B as the filtered union of its A-subalgebras generated by finite subsets.
Each such algebra is finitely presented because A is Noetherian. Their spectra form
an inverse system with affine transitions and limit Spec B. Base change of Y commutes
with that limit; all its stages are quasi-compact and quasi-separated, since they are
proper over affine schemes. A finite étale morphism is of finite presentation, so
spreading out gives a finitely presented cover at some stage with base change U.
Finiteness and étaleness each descend after increasing the stage. Choose a common
larger finite subset; both properties persist under base change. Call this algebra R
and its inclusion c. The induced morphism l from Y_B to Y_R has the displayed
projections. Transport the spread-out isomorphism through these base-change squares
to get an isomorphism over Y_B. The zero algebra and the empty cover cause no exception:
the directed system is nonempty (it includes the empty subset) and the same descent
statements apply. -/
theorem exists_finiteEtale_algebra_stage
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R),
      Algebra.FinitePresentation A R ∧
      ∃ (c : R →ₐ[A] B)
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A R)))))
        (l : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap A R)))),
        l ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        l ≫ pullback.snd _ _ = pullback.snd _ _ ≫
          Spec.map (CommRingCat.ofHom c.toRingHom) ∧
        Nonempty (Over.mk (pullback.snd W.hom l) ≅ Over.mk U.hom) := by
  classical
  let I := {S : Subalgebra A B // S.FG}
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  let D := (algebraDiagram A B).op ⋙ Scheme.Spec
  let c := Scheme.Spec.mapCone (algebraCocone A B).op
  obtain ⟨hcR⟩ := algebraCocone_isColimit A B
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec hcR.op
  let p : D ⟶ (Functor.const Iᵒᵖ).obj (Spec (.of A)) :=
    { app := fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap A i.unop.1))
      naturality := by
        intro i j a
        dsimp [D, algebraDiagram]
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1 }
  let E : Iᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun i ↦ pullback f (p.app i)
      map := fun {i j} a ↦ pullback.map _ _ _ _ (𝟙 Y) (D.map a) (𝟙 _)
        (by simp) (by simp [p.naturality a])
      map_id := by intro i; apply pullback.hom_ext <;> simp
      map_comp := by intro i j k a b; apply pullback.hom_ext <;> simp }
  let π : E ⟶ D := { app := fun i ↦ pullback.snd f (p.app i) }
  have hcp (i : Iᵒᵖ) : c.π.app i ≫ p.app i =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    dsimp [c, p, algebraCocone]
    rw [← Spec.map_comp]
    congr 1
  let d : Cone E :=
    { pt := pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      π :=
        { app := fun i ↦ pullback.map _ _ _ _ (𝟙 Y) (c.π.app i) (𝟙 _)
            (by simp) (by simpa using (hcp i).symm)
          naturality := by
            intro i j a
            apply pullback.hom_ext
            · simp [E]
            · simp only [E, pullback.map, Functor.const_obj_obj, Functor.const_obj_map,
                Category.id_comp, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc]
              exact congrArg
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ ·)
                (c.w a).symm } }
  let v : (Cone.postcompose π).obj d ⟶ c :=
    { hom := pullback.snd _ _
      w := by intro i; simp [d, π] }
  have hd : IsLimit d := isLimitOfIsPullbackOfIsConnected π d c v
    (fun i ↦ isPullback_pullback_map f _ _ (c.π.app i) (hcp i)) hc
  have (i : Iᵒᵖ) : IsAffine (D.obj i) := inferInstanceAs (IsAffine (Spec (.of i.unop.1)))
  have (i : Iᵒᵖ) : IsProper (pullback.snd f (p.app i)) := inferInstance
  have (i : Iᵒᵖ) : CompactSpace (E.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (p.app i))
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (E.obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (p.app i))
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (E.map a) :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_map f (p.app i) (p.app j) (D.map a)
        (by simp [p.naturality a])).flip inferInstance
  have : IsFinite U.hom := U.prop.1
  have : Etale U.hom := U.prop.2
  obtain ⟨i, Z, q, hfin, het, h, H⟩ := exists_finiteEtale_limit_stage E d hd U.hom
  have : Algebra.FiniteType A i.1 := i.1.fg_iff_finiteType.mp i.2
  have hfp : Algebra.FinitePresentation A i.1 :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A i.1)))) :=
    MorphismProperty.Over.mk _ q ⟨hfin, het⟩
  refine ⟨i.1, inferInstance, inferInstance, hfp, i.1.val, W, d.π.app (Opposite.op i), ?_, ?_, ?_⟩
  · simp [d, p, pullback.map]
  · simp [d, p, c, algebraCocone, pullback.map]
  · refine ⟨Over.isoMk H.isoPullback.symm ?_⟩
    change H.isoPullback.inv ≫ U.hom = pullback.snd q (d.π.app (Opposite.op i))
    exact H.isoPullback_inv_snd

end AlgebraicGeometry.Scheme
