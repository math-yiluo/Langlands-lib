/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax

/-! # Ordinary tensor comparison for completed coefficient transport

Source: Stacks Project, Modules on Sites, Tags 03DA and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v c' v' w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Comparing the localized tensor expressions requires extra elaboration heartbeats.
private theorem pushforward_tensor_isIso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
    {D : Type c'} [Category.{v'} D] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
    (S : Sheaf J CommRingCat.{w}) (R : Sheaf K CommRingCat.{w})
    (φ : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S ⟶
      (G.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (hφ : ∀ U, IsIso (φ.hom.app U))
    (L : letI := SheafOfModules.monoidalCategory.{v', c', w} R
      letI := SheafOfModules.monoidalCategory.{v, c, w} S
      (SheafOfModules.pushforward.{w} φ).LaxMonoidal)
    (hL : SheafOfModules.RingedPushforwardPureTensor.{c, v, c', v', w} G S R φ L)
    (M N : SheafOfModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := SheafOfModules.monoidalCategory.{v', c', w} R
    letI := SheafOfModules.monoidalCategory.{v, c, w} S
    letI := L
    IsIso (Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{w} φ) M N) := by
  let := SheafOfModules.monoidalCategory.{v', c', w} R
  let := SheafOfModules.monoidalCategory.{v, c, w} S
  let := L
  let V := SheafOfModules.pushforward.{w} φ
  let P := M.val ⊗ N.val
  let Q := (V.obj M).val ⊗ (V.obj N).val
  let T := SheafOfModules.tensorObjIsoSheafification.{v, c, w} (V.obj M) (V.obj N)
  let U := SheafOfModules.tensorObjIsoSheafification.{v', c', w} M N
  let t := WeilConjectures.SemilinearSections.restrictionTensorPresheafIso.{c, v, w, c', v'}
    (F := G) (R := R.obj) (S := S.obj) φ.hom hφ M.val N.val
  let a := PresheafOfModules.sheafification.{w}
    (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _)
  let b := restrictionSheafificationMap.{c, v, w, c', v'} φ P
  let hb : IsIso b := restrictionSheafificationMap_isIso.{c, v, w, c', v'} φ P
  let f := T.hom ≫ a.map t.hom ≫ b ≫ V.map U.inv
  have hf : f = Functor.LaxMonoidal.μ V M N := by
    apply SheafOfModules.pureMap_ext S (V.obj M) (V.obj N) (V.obj (M ⊗ N))
    intro W x y
    have h := tensorComparison_unit_apply.{c, v, w, c', v'}
      φ P Q t.hom T U W (x ⊗ₜ[S.obj.obj W] y)
    have hp := WeilConjectures.SemilinearSections.restrictionTensorPresheafIso_pure
      (F := G) (R := R.obj) (S := S.obj) φ.hom hφ M.val N.val W x y
    let adj := PresheafOfModules.sheafificationAdjunction.{w}
      (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
    have he := congrArg (fun z ↦ U.inv.val.app (G.op.obj W)
      ((adj.unit.app P).app (G.op.obj W) z)) hp
    exact h.trans (he.trans (hL M N W x y).symm)
  have hi : IsIso f := by
    change IsIso ((T ≪≫ a.mapIso t ≪≫
      (@asIso _ _ _ _ b hb) ≪≫ V.mapIso U.symm).hom)
    infer_instance
  exact hf ▸ hi

universe u
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary module comparison, normalized at the regular module.
Source: Stacks Project, Modules on Sites, Tags 03DA and 03EK, the balanced
bilinear universal property and its invariance under an equivalence of ringed sites.
(blueprint: lem-weil-pbc-completed-module-tensor-transport).

Proof: restrict along the inverse of the completed coefficient-ring isomorphism.
On each object the balanced tensor isomorphism takes x tensor y to x tensor y;
its inverse uses the inverse ring map. These maps commute with restrictions
and with linear maps in both variables. Reindex along the inverse site
equivalence and sheafify. The sheafification universal property identifies the
result with the tensor of the two transported sheaves and preserves the inverse
equations. This gives the natural isomorphism of bifunctors. At the regular
module, the coefficient-ring comparison sends the transported section 1 to 1.
The inverse right unitor sends x to x tensor 1, so both sides of the displayed
normalization send x to x tensor 1. Equality follows from the module-sheaf
universal property, or directly from the section formula for the unitor.
The construction uses no complexes, totalization, Koszul complex, or choice of
representative; the zero ring and empty site satisfy the same equations. -/
theorem completedCechModuleTensorTransport
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients
      (adicDatumRing X (intrinsicPresentationDatum d))
    letI := SheafOfModules.monoidalCategory (adicDatumRing X (intrinsicPresentationDatum d))
    letI := SheafOfModules.monoidalCategory (completedCechRing X d)
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    ∃ τ : (Functor.postcompose₂.obj F).obj (curriedTensor _) ≅
        (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor _),
      ∀ M : adicDatumModules X (intrinsicPresentationDatum d),
        F.map (ρ_ M).inv ≫ (τ.hom.app M).app (𝟙_ _) =
          (ρ_ (F.obj M)).inv ≫ F.obj M ◁ completedCechCoefficientUnit X d := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
    let : EssentiallySmall.{u + 1} (completedCechSite X) :=
      essentiallySmallSelf.{u + 1} _
    let R := adicDatumRing X (intrinsicPresentationDatum d)
    let S := pbcAdicCompletion X d
    let O := completedCechRing X d
    let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
    let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
    let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
    let := SheafOfModules.monoidalCategory.{u + 1, u + 1, u + 1} O
    let c := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (pbcCompletedComparison X d).inv
    let B := intrinsicPresentationModulesBack X d
    let G := (completedCechModulesEquiv X d).functor
    let F := B ⋙ G
    obtain ⟨LB, hLB, hεB, _⟩ :=
      SheafOfModules.exists_unique_ringedPushforward_laxMonoidal.{u + 1, u, u + 1, u, u + 1}
      (𝟭 X.ProEt) S R c
    let : B.LaxMonoidal := LB
    have hB (M N) : IsIso (Functor.LaxMonoidal.μ B M N) :=
      pushforward_tensor_isIso.{u + 1, u, u + 1, u, u + 1} (𝟭 X.ProEt) S R c (fun U ↦ by
        change IsIso (c.hom.app U)
        infer_instance) LB hLB M N
    let e := completedCechSiteEquiv X
    let J := ProEt.topology X
    let K := completedCechTopology X
    let cG : (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O ⟶
        (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) := 𝟙 _
    let : e.inverse.IsCocontinuous K J := by
      dsimp only [K, completedCechTopology]
      rw [← e.inverse.restrictedTopology_eq_inducedTopology]
      infer_instance
    obtain ⟨LG, hLG, hεG, _⟩ :=
      SheafOfModules.exists_unique_ringedPushforward_laxMonoidal.{u + 1, u + 1, u + 1, u, u + 1}
      e.inverse O S cG
    let : G.LaxMonoidal := LG
    have hG (M N) : IsIso (Functor.LaxMonoidal.μ G M N) :=
      pushforward_tensor_isIso.{u + 1, u + 1, u + 1, u, u + 1} e.inverse O S cG (fun U ↦ by
        change IsIso (𝟙 (RingCat.of (S.obj.obj (e.inverse.op.obj U))))
        infer_instance) LG hLG M N
    let : F.LaxMonoidal := inferInstanceAs (B ⋙ G).LaxMonoidal
    have hF (M N) : IsIso (Functor.LaxMonoidal.μ F M N) := by
      change IsIso (Functor.LaxMonoidal.μ G (B.obj M) (B.obj N) ≫
        G.map (Functor.LaxMonoidal.μ B M N))
      let := hB M N
      let := hG (B.obj M) (B.obj N)
      infer_instance
    let t (M N) := @asIso _ _ _ _ (Functor.LaxMonoidal.μ F M N) (hF M N)
    let τ : (Functor.postcompose₂.obj F).obj (curriedTensor _) ≅
        (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor _) :=
      NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ (t M N).symm) (by
        intro N N' f
        change F.map (M ◁ f) ≫ (t M N').inv =
          (t M N).inv ≫ F.obj M ◁ F.map f
        apply (cancel_epi (t M N).hom).mp
        simp only [Iso.hom_inv_id_assoc]
        change Functor.LaxMonoidal.μ F M N ≫ F.map (M ◁ f) ≫
          (t M N').inv = F.obj M ◁ F.map f
        rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
        change (F.obj M ◁ F.map f) ≫ (t M N').hom ≫ (t M N').inv = _
        simp)) (by
          intro M M' f
          apply NatTrans.ext
          funext N
          change F.map (f ▷ N) ≫ (t M' N).inv =
            (t M N).inv ≫ F.map f ▷ F.obj N
          apply (cancel_epi (t M N).hom).mp
          simp only [Iso.hom_inv_id_assoc]
          change Functor.LaxMonoidal.μ F M N ≫ F.map (f ▷ N) ≫
            (t M' N).inv = F.map f ▷ F.obj N
          rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
          change (F.map f ▷ F.obj N) ≫ (t M' N).hom ≫ (t M' N).inv = _
          simp)
    have hε : Functor.LaxMonoidal.ε F = completedCechCoefficientUnit X d := by
      let M₀ := (intrinsicPresentationModulesBack X d ⋙
        (completedCechModulesEquiv X d).functor).obj
          (SheafOfModules.unit ((adicLisseForget X).obj
            (adicDatumRing X (intrinsicPresentationDatum d))))
      apply (SheafOfModules.unitHomEquiv M₀).injective
      simp only [M₀, completedCechCoefficientUnit]
      erw [Equiv.apply_symm_apply]
      ext U
      rw [SheafOfModules.unitHomEquiv_apply_coe]
      change (Functor.LaxMonoidal.ε B).val.app (e.inverse.op.obj U)
        ((Functor.LaxMonoidal.ε G).val.app U (1 : O.obj.obj U)) =
          (1 : R.obj.obj (e.inverse.op.obj U))
      have hG1 : (Functor.LaxMonoidal.ε G).val.app U (1 : O.obj.obj U) =
          (1 : S.obj.obj (e.inverse.op.obj U)) := hεG U 1
      have hB1 : (Functor.LaxMonoidal.ε B).val.app (e.inverse.op.obj U)
          (1 : S.obj.obj (e.inverse.op.obj U)) =
            (1 : R.obj.obj (e.inverse.op.obj U)) :=
        (hεB (e.inverse.op.obj U) 1).trans
          ((c.hom.app (e.inverse.op.obj U)).hom.map_one)
      exact (congrArg (fun z ↦ (Functor.LaxMonoidal.ε B).val.app
        (e.inverse.op.obj U) z) hG1).trans hB1
    refine ⟨τ, ?_⟩
    intro M
    change F.map (ρ_ M).inv ≫ (t M (𝟙_ _)).inv =
      (ρ_ (F.obj M)).inv ≫ F.obj M ◁ completedCechCoefficientUnit X d
    rw [← hε]
    apply (cancel_mono (t M (𝟙_ _)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Functor.LaxMonoidal.right_unitality_inv F M).symm

end AlgebraicGeometry.Scheme
