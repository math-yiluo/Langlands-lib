import Langlands.GroupScheme.Rational.TrialitarianOppositeBorelFactors
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelPinning
import Langlands.GroupScheme.Rational.TrialitarianDerivedFaces
import Langlands.GroupScheme.Derived.Action

/-! # The actual central and leaf factors of the opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

section Action

variable {F : Type u} [Field F]
  {M H G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom M.X.hom]
  {T T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of F))}
  (t : T.toGrp ⟶ M) (j : M ⟶ G)
  (d : H ⟶ M) (hd : IsDerivedSubgroup d)
  (i : T₁.toGrp ⟶ H) (m₁ : T₁ ⟶ T) (m₂ : T₂ ⟶ T)
  (h : i ≫ d = CommGroupScheme.groupHom m₁ ≫ t)

include hd h in
/-- The other torus factor acts by conjugating the actual derived group
inside the Levi. The shared torus commutativity makes this action trivial
on the first torus factor. -/
theorem exists_derivedFaceAction (hT₂ : IsTorus T₂.toGrp) :
    ∃ act : AutomorphicAction T₂.toGrp H,
      (∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ T₂.toGrp.X) (y : Z ⟶ H.X),
        act.act x y ≫ (d ≫ j).hom.hom =
          (x ≫ (CommGroupScheme.groupHom m₂ ≫ t ≫ j).hom.hom) *
            (y ≫ (d ≫ j).hom.hom) *
            (x ≫ (CommGroupScheme.groupHom m₂ ≫ t ≫ j).hom.hom)⁻¹) ∧
      ∀ (Z : Over (Spec (CommRingCat.of F))) (x : Z ⟶ T₂.toGrp.X) (z : Z ⟶ T₁.toGrp.X),
        act.act x (z ≫ i.hom.hom) = z ≫ i.hom.hom := by
  let h₂ : T₂.toGrp ⟶ M := CommGroupScheme.groupHom m₂ ≫ t
  let : IsAffine T₂.toGrp.X.left := SplittingAssembly.isAffine_of_isTorus _ hT₂
  let : IsAffineHom T₂.toGrp.X.hom := inferInstance
  let a := AutomorphicAction.conjugation h₂
  refine ⟨hd.action a, ?_, ?_⟩
  · intro Z x y
    rw [Grp.comp_hom_hom, ← Category.assoc, hd.action_act_comp,
      show a.act x (y ≫ d.hom.hom) = _ from AutomorphicAction.conjugation_act h₂ x _,
      MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    simp only [h₂, Grp.comp_hom_hom, Category.assoc]
  · intro Z x z
    let : IsClosedImmersion d.hom.hom.left := hd.1
    let : Mono d.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono d.hom.hom).mp
    rw [hd.action_act_comp, Category.assoc, ← Grp.comp_hom_hom, h]
    rw [show a.act x (z ≫ (CommGroupScheme.groupHom m₁ ≫ t).hom.hom) = _
      from AutomorphicAction.conjugation_act h₂ x _]
    have hc : Commute
        (x ≫ (CommGroupScheme.groupHom m₂).hom.hom)
        (z ≫ (CommGroupScheme.groupHom m₁).hom.hom) := Commute.all _ _
    have hc' : Commute (x ≫ h₂.hom.hom) (z ≫ (CommGroupScheme.groupHom m₁ ≫ t).hom.hom) := by
      apply (commute_iff_eq _ _).mpr
      simp only [h₂, Grp.comp_hom_hom, ← Category.assoc]
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, hc.eq]
    rw [hc'.eq, mul_inv_cancel_right]

end Action

section Product

variable {S : Scheme.{u}} {T T' T₁ T₂ : CommGroupScheme S}
  {G : GroupScheme S} (t : T.toGrp ⟶ G) (t' : T'.toGrp ⟶ G)
  (e : T' ≅ T) (he : CommGroupScheme.groupHom e.hom ≫ t = t')
  (m₁ : T₁ ⟶ T') (m₂ : T₂ ⟶ T')

include he in
/-- Inverting an isomorphism given by torus multiplication gives the
corresponding projections and their product identity on all tests. -/
theorem exists_torusFactorProjections
    (h : IsIso (CommGroupScheme.prodFst T₁ T₂ ≫ m₁ + CommGroupScheme.prodSnd T₁ T₂ ≫ m₂)) :
    ∃ (p₁ : T.toGrp ⟶ T₁.toGrp) (p₂ : T.toGrp ⟶ T₂.toGrp),
      ∀ (Z : Over S) (z : Z ⟶ T.toGrp.X),
        z ≫ t.hom.hom =
          (z ≫ p₁.hom.hom ≫ (CommGroupScheme.groupHom m₁ ≫ t').hom.hom) *
            (z ≫ p₂.hom.hom ≫ (CommGroupScheme.groupHom m₂ ≫ t').hom.hom) := by
  let m := CommGroupScheme.prodFst T₁ T₂ ≫ m₁ + CommGroupScheme.prodSnd T₁ T₂ ≫ m₂
  let : IsIso m := h
  let p := e.inv ≫ inv m
  let p₁ := p ≫ CommGroupScheme.prodFst T₁ T₂
  let p₂ := p ≫ CommGroupScheme.prodSnd T₁ T₂
  have hp : p₁ ≫ m₁ + p₂ ≫ m₂ = e.inv := by
    change (p ≫ _) ≫ m₁ + (p ≫ _) ≫ m₂ = e.inv
    simp only [Category.assoc]
    rw [← Preadditive.comp_add]
    change (e.inv ≫ inv m) ≫ m = e.inv
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ht : CommGroupScheme.groupHom e.inv ≫ t' = t := by
    rw [← he, ← Category.assoc]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ t = t
    rw [e.inv_hom_id]
    exact Category.id_comp _
  refine ⟨CommGroupScheme.groupHom p₁, CommGroupScheme.groupHom p₂, fun Z z => ?_⟩
  rw [← ht, Grp.comp_hom_hom, ← Category.assoc, ← hp, comp_groupHom_add, MonObj.mul_comp]
  rfl

end Product

private def oneVertexEquiv {V : Type u} (e : V ≃ Fin 4) :
    {a : V // e a = 1} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨e.symm 1, e.apply_symm_apply 1⟩
  left_inv a := Subtype.ext (e.injective ((e.apply_symm_apply 1).trans a.property.symm))
  right_inv _ := Subsingleton.elim _ _

/-- The central and leaf faces of the actual opposite-Borel torus give,
respectively, a rank-one group and a rank-one Weil restriction. -/
theorem trialitarianOppositeBorelFactors : TrialitarianOppositeBorelFactorsStatement.{u} := by
  classical
  intro F _ _ G _ _ d e hsc _ hD hmove Q _ _ T t ht
  let E := SeparableClosure F
  obtain ⟨p, eT, heT, v, hpair, hstar, hs⟩ :=
    exists_quadraticOppositeBorelPinning t Q ht.1 hsc ht d e hD
  let eG : p.torus.toGrp ≅ T.toGrp :=
    ⟨CommGroupScheme.groupHom eT.hom, CommGroupScheme.groupHom eT.inv,
      congrArg CommGroupScheme.groupHom eT.hom_inv_id,
      congrArg CommGroupScheme.groupHom eT.inv_hom_id⟩
  have hmax : IsMaximalTorus p.inclusion := by
    rw [← heT]
    exact ht.2.1.iso_comp (T' := p.torus) eG
  let J : Set p.base.support := {x | e (v.symm x) = 1}
  have hJ (σ : E ≃ₐ[F] E) (x : p.base.support) : p.starSupport σ x ∈ J ↔ x ∈ J := by
    obtain ⟨a, rfl⟩ := v.surjective x
    have h : p.starSupport σ (v a) = v (d.star σ a) := Subtype.ext (hstar σ a).symm
    rw [h]
    change e (v.symm (v (d.star σ a))) = 1 ↔ e (v.symm (v a)) = 1
    rw [v.symm_apply_apply, v.symm_apply_apply]
    exact d.star_central_label_iff_of_D4 e hD σ a
  have hJ' (σ : E ≃ₐ[F] E) (x : p.base.support) : p.starSupport σ x ∈ Jᶜ ↔ x ∈ Jᶜ :=
    not_congr (hJ σ x)
  obtain ⟨ν₁, C, RC, hc⟩ := p.exists_derivedSimpleFace hsc hmax hs J hJ
  obtain ⟨ν₂, L, RL, hl⟩ := p.exists_derivedSimpleFace hsc hmax hs Jᶜ hJ'
  have hpart (x : p.base.support) : p.rootDatum.root' x.val ν₂ = 0 ↔
      p.rootDatum.root' x.val ν₁ ≠ 0 :=
    (hl x).trans (not_congr (hc x)).symm
  have hμ := GaloisBorelFaceDerived.isIso_torusProduct RC RL hsc hpart
  have hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a := by
    rintro ⟨a, ha, hfix⟩
    obtain ⟨σ, hσ⟩ := hmove a ha
    exact hσ (hfix σ)
  let a := e.symm 0
  have ha : e a ≠ 1 := by change e (e.symm 0) ≠ 1; rw [e.apply_symm_apply]; decide
  obtain ⟨hfd, A, hAffA, hAffHomA, hFinA, dA, hscA, hAbsA, hrankA, ⟨eW⟩⟩ :=
    d.exists_rankOneWeil_of_D4_leafFace RL e hD hno v hpair hstar hs hl a ha
  let : FiniteDimensional F (d.starVertexField a) := hfd
  let : NumberField (d.starVertexField a) := NumberField.of_module_finite F _
  let : IsAffine A.X.left := hAffA
  let : IsAffineHom A.X.hom := hAffHomA
  let : LocallyOfFiniteType A.X.hom := hFinA
  let : IsAffineHom C.derived.X.hom := C.derivedAffine
  let : LocallyOfFiniteType C.derived.X.hom := C.derivedFiniteType
  let : IsAffineHom C.levi.X.hom := C.isReductive.isAffineHom
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj C.derived).X.hom :=
    RC.pinning.isConnectedReductive.isAffineHom
  let w : RC.face.base.support ≃ {x : d.Vertex // e x = 1} :=
    RC.simpleEquiv.trans (v.symm.subtypeEquiv hc)
  let e₁ := w.trans (oneVertexEquiv e)
  have hAbsH := RC.isAbsolutelyAlmostSimple_of_singleton e₁
  obtain ⟨dH⟩ := titsIndexExistence F C.derived C.isSimplyConnected.isSemisimple
  obtain ⟨eH⟩ := dH.nonempty_vertexEquiv_of_geometricPinning RC.pinning.toSplitPinning (Iso.refl _)
  let r := L.torusInclusion ≫ eW.inv
  let s := eW.hom ≫ L.derivedInclusion ≫ L.inclusion
  have hrs : r ≫ s = CommGroupScheme.groupHom L.torusMap ≫ p.inclusion := by
    dsimp only [r, s]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, L.torus_square,
      Category.assoc, L.leviTorus_comp]
  let j := C.derivedInclusion ≫ C.inclusion
  have hij : C.torusInclusion ≫ j = CommGroupScheme.groupHom C.torusMap ≫ p.inclusion := by
    dsimp only [j]
    rw [← Category.assoc, C.torus_square, Category.assoc, C.leviTorus_comp]
  obtain ⟨p₁, p₂, hprod⟩ :=
    exists_torusFactorProjections t p.inclusion eT heT C.torusMap L.torusMap hμ
  obtain ⟨act, hact, hfix⟩ := exists_derivedFaceAction C.leviTorusInclusion C.inclusion
    C.derivedInclusion C.isDerived C.torusInclusion C.torusMap L.torusMap C.torus_square
    L.torus_maximal.1
  refine ⟨a, inferInstance, hfd, A, hAffA, hAffHomA, hFinA, dA,
    C.derived, inferInstance, inferInstance, dH, C.torus, L.torus, p₁, p₂, C.torusInclusion,
    j, r, s, act, ha, hscA, hAbsA, hrankA, C.isSimplyConnected, hAbsH, ⟨eH.trans e₁⟩,
    L.isSimplyConnected.of_iso eW, ?_, hfix, ?_⟩
  · intro Z x y
    rw [hrs, ← C.leviTorus_comp]
    exact hact Z x y
  · intro Z z
    have he₁ : (CommGroupScheme.groupHom C.torusMap ≫ p.inclusion).hom.hom =
        C.torusInclusion.hom.hom ≫ j.hom.hom :=
      congrArg (fun f : C.torus.toGrp ⟶ G => f.hom.hom) hij.symm
    simpa only [hrs, he₁, Category.assoc] using hprod Z z

end Langlands.GroupScheme
