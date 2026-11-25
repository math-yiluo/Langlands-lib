/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # The geometric fibre restriction formula for exchange

Source: Stacks Project, Tag 0EYP, the canonical base change map on germs.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme
set_option backward.isDefEq.respectTransparency false

/-- At the identity geometric point, the marked map itself is a section of each
pointed neighbourhood. Restricting representatives along these sections proves
bijectivity of the terminal germ. This is the field case of Stacks Tag 03QO. -/
private theorem terminalGerm_isIso
    (Λ : Type (u + 1)) [CommRing Λ]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)) F.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let t : Φ.fiber.obj T := Over.homMk (𝟙 _) (Category.comp_id _)
  have hsec (V : (Spec (.of Ω)).Etale) (v : Φ.fiber.obj V) :
      ∃ g : T ⟶ V, Φ.fiber.map g t = v := by
    refine ⟨MorphismProperty.Over.homMk v.left v.w, ?_⟩
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    obtain ⟨V, f, v, _, heq⟩ :=
      (Φ.toPresheafFiber_eq_iff' (P := F.obj) T t a b).mp hab
    obtain ⟨g, _⟩ := hsec V v
    have hgf : g ≫ f = 𝟙 T := (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
      (Spec (.of Ω))).hom_ext _ _
    have h := congrArg (F.obj.map g.op) heq
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
  · intro z
    obtain ⟨V, v, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) z
    obtain ⟨g, hg⟩ := hsec V v
    refine ⟨F.obj.map g.op a, ?_⟩
    rw [Φ.toPresheafFiber_w_apply, hg]

/-- The pointed neighbourhood section on the geometric fibre, followed by its lift
through the iterated pullback. Both components are specified, so this construction
involves no choice of a geometric lift. -/
noncomputable def geometricFibreSectionLift
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    Scheme.Etale.mk (𝟙 X') ⟶ g'.Etale.obj (f.Etale.obj V) := by
  let a : X' ⟶ pullback V.hom f := pullback.lift (f' ≫ v.left) g' (by
    have hv : v.left ≫ V.hom = s := v.w
    rw [Category.assoc, hv]
    exact sq.w.symm)
  exact MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 X') (by
      change a ≫ pullback.snd V.hom f = 𝟙 X' ≫ g'
      simp [a])) (pullback.lift_snd _ _ _)

/-- Restrict a neighbourhood section by the inverse-image unit and the specified
pointed lift to the fibre. This definition does not use the exchange map. -/
noncomputable def geometricFibreSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    F.obj.obj (op (f.Etale.obj V)) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.map
      (geometricFibreSectionLift sq V v).op

/-- The inverse-image comparison at the identity geometric point, with identity
composition normalized. -/
noncomputable def geometricPointSourceStalkIso
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    (P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        ((s)^*[ModuleCat.{u + 1} Λ].obj P) ≅
      (pointSmallEtale s).sheafFiber.obj P := by
  simpa only [Functor.comp_obj, Category.id_comp] using
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)).app P

/-- The germ formula for the specified canonical source comparison, obtained by
expanding its three factors and using the comap-unit identity. This is the
ModuleCat version of the proof of `inverseImage_stalk_germ` (Stacks Tag 03Q1). -/
private theorem sourceStalkIso_germ
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (ū : (pointSmallEtale s).fiber.obj U) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app G).hom.app
          (op U) ≫
        (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber (s.Etale.obj U)
          ((pointSmallEtaleFiberEtaleIso s (𝟙 _)).inv.app U
            (by simpa only [Category.id_comp] using ū))
          ((s)^*[ModuleCat.{u + 1} Λ].obj G).obj ≫
        (geometricPointSourceStalkIso Λ s G).hom =
      (pointSmallEtale s).toPresheafFiber U ū G.obj := by
  change _ ≫ _ ≫ (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)).hom.app G = _
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)).app G)).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map _ =
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ s) (ModuleCat.{u + 1} Λ)
      (Y.smallGrothendieckTopology (P := @Etale))
      ((Spec (.of Ω)).smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

/-- Any map on direct-image germs having the fibre restriction formula is the
actual exchange after the canonical source comparison and a target section comparison.
This is a compatibility assertion only: it asserts no invertibility of that map or
of exchange, and has no integral or proper hypothesis.

Source: Stacks Project, Tag 0EYP, definition of the base change map, and Tags 03Q1
and 03QO for inverse-image stalks and sections on the spectrum of a closed field.
(blueprint: lem-sbc-geometric-fibre-exchange-germs).

Proof: identify the source by the inverse-image stalk isomorphism. On Spec Omega,
every pointed etale neighbourhood of the identity has a section through its marked
point, so the terminal section germ is bijective. Apply this to the direct image
along f', and identify its terminal sections with those on X' using the unique
isomorphism from the pullback of the terminal object to the terminal object. Its
inverse is the target comparison b. For a neighbourhood (V,v), the pushforward
unit identity for base change expresses the mate as the unit for g' followed by
the pushforward square isomorphism. Restrict along the marked point v: the two
pullback projections are f' followed by v and g', respectively. The iterated
pullback lift is therefore geometricFibreSectionLift. This gives exactly the
displayed formula on every germ. All germs have such representatives, so the
assumed formula for Theta proves the equality on every element. No bijectivity
of Theta is used. -/
theorem geometricFibreExchange_germs
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))))
    (hΘ : ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (z : F.obj.obj (op (f.Etale.obj V))),
      Θ.hom ((pointSmallEtale s).toPresheafFiber V v
        ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z) =
      (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z) :
    ∃ b : (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        ((f')_*[ModuleCat.{u + 1} Λ].obj ((g')^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
          ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) ≫ b.hom =
        (geometricPointSourceStalkIso Λ s ((f)_*[ModuleCat.{u + 1} Λ].obj F)).hom ≫ Θ := by
  let H : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ) := (g')^*[ModuleCat.{u + 1} Λ].obj F
  let P := (f')_*[ModuleCat.{u + 1} Λ].obj H
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let TX := Scheme.Etale.mk (𝟙 X')
  let t : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj T :=
    Over.homMk (𝟙 _) (Category.comp_id _)
  let e : f'.Etale.obj T ≅ TX :=
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale
      (Spec (.of Ω))).isTerminalObj f'.Etale).uniqueUpToIso
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X')
  let j : P.obj.obj (op T) ⟶
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj P :=
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber T t P.obj
  have : IsIso j := terminalGerm_isIso Λ P
  let b := (asIso j).symm ≪≫ H.obj.mapIso e.op.symm
  refine ⟨b, ?_⟩
  let Q := (f)_*[ModuleCat.{u + 1} Λ].obj F
  let a := geometricPointSourceStalkIso Λ s Q
  apply (Iso.inv_comp_eq a).1
  apply (pointSmallEtale s).presheafFiber_hom_ext
  intro V v
  change (pointSmallEtale s).toPresheafFiber V v Q.obj ≫
    (a.inv ≫ _ ≫ b.hom) = (pointSmallEtale s).toPresheafFiber V v Q.obj ≫ Θ
  have hsrc := sourceStalkIso_germ Λ s Q V v
  rw [← Category.assoc] at hsrc
  have hsrc' := (Iso.eq_comp_inv a).2 hsrc
  rw [← Category.assoc, ← hsrc', Category.assoc]
  change _ ≫ _ ≫ _ ≫ b.hom = _
  rw [show (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map _ =
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  rw [← Category.assoc]
  have hu := unit_map_baseChangeMap_app (ModuleCat.{u + 1} Λ) sq.toCommSq F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  change _ ≫ _ = _ at huV
  erw [huV]
  let w : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj (s.Etale.obj V) :=
    (pointSmallEtaleFiberEtaleIso s (𝟙 _)).inv.app V
      (by simpa only [Category.id_comp] using v)
  let σ : T ⟶ s.Etale.obj V := MorphismProperty.Over.homMk w.left w.w
  have hσ : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.map σ t = w := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app H).hom.app (op V) ≫
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber (s.Etale.obj V) w P.obj ≫
    b.hom = _
  rw [← hσ, ← GrothendieckTopology.Point.toPresheafFiber_w_assoc]
  have hterm : j ≫ b.hom = H.obj.map e.inv.op := by
    simp [b]
  change _ ≫ _ ≫ P.obj.map σ.op ≫ j ≫ b.hom = _
  rw [hterm]
  let c₁ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) g' f
  let c₂ := MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
    (Q := ⊤) f' s (g' ≫ f) sq.w
  change _ ≫ (H.obj.map (c₁.hom.app V).op ≫ H.obj.map (c₂.inv.app V).op) ≫
    H.obj.map (f'.Etale.map σ).op ≫ H.obj.map e.inv.op = _
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  have hlift : e.inv ≫ f'.Etale.map σ ≫ c₂.inv.app V ≫ c₁.hom.app V =
      geometricFibreSectionLift sq.toCommSq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change e.inv.left ≫ (f'.Etale.map σ).left ≫ (c₂.inv.app V).left ≫
        (c₁.hom.app V).left ≫ pullback.fst (pullback.snd V.hom f) g' =
          (geometricFibreSectionLift sq.toCommSq V v).left ≫
            pullback.fst (pullback.snd V.hom f) g'
      simp only [geometricFibreSectionLift]
      apply pullback.hom_ext
      · simp only [Functor.id_obj, Functor.const_obj_obj, Hom.Etale,
          MorphismProperty.Over.pullback_map_left, Functor.comp_obj,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
          Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_fst, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, c₂, c₁]
        erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, pullback.lift_fst]
        have hw := pointSmallEtaleFiberEtaleIso_inv_app_left_fst
          s (𝟙 (Spec (.of Ω))) V (by simpa only [Category.id_comp] using v)
        change σ.left ≫ pullback.fst V.hom s = v.left at hw
        have he : e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' = 𝟙 X' := e.inv.w
        have hefst : e.inv.left ≫ pullback.fst (𝟙 (Spec (.of Ω))) f' = f' := by
          have h := congrArg (fun q : X' ⟶ X' ↦ q ≫ f') he
          erw [Category.assoc, ← pullback.condition, Category.comp_id] at h
          exact h
        simp only [Category.assoc]
        erw [hw]
        change e.inv.left ≫ pullback.fst (𝟙 (Spec (.of Ω))) f' ≫ v.left = f' ≫ v.left
        rw [← Category.assoc, hefst]
      · simp only [Functor.id_obj, Functor.const_obj_obj, Hom.Etale,
          MorphismProperty.Over.pullback_map_left, Functor.comp_obj,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
          Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_snd_assoc, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, c₂, c₁]
        erw [pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_snd]
        have he : e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' = 𝟙 X' := e.inv.w
        change e.inv.left ≫ pullback.snd (𝟙 (Spec (.of Ω))) f' ≫ g' = g'
        rw [← Category.assoc, he]
        exact Category.id_comp g'
    · exact (e.inv ≫ f'.Etale.map σ ≫ c₂.inv.app V ≫ c₁.hom.app V).w.trans
        (geometricFibreSectionLift sq.toCommSq V v).w.symm
  rw [hlift]
  apply ModuleCat.hom_ext
  ext z
  exact (hΘ V v z).symm

end AlgebraicGeometry.Etale
