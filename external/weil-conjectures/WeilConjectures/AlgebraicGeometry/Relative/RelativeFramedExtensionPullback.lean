/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierPairPullbackSection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback

/-! # Arbitrary inverse image of a relative framed torsor extension

## References

* Stacks 03AJ and 0A45
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

open Opposite

private theorem presheafHomPullback_map {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) (U : T.Etale) (s : unit T ⟶ L) :
    presheafHomPullback v L U ((pullback U.hom).map s) =
      (pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U).hom).map
        ((pullbackObjUnitIso v).inv ≫ (pullback v).map s) := by
  erw [presheafHomPullback, pullbackMap_presheaf_map, presheafHomRestrict_eq]
  let c := Cat.Hom.toNatIso (modulesPseudofunctor.mapComp' v.op.toLoc
    ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U).hom.op.toLoc
    (((MorphismProperty.Over.pullback @Etale ⊤ v).obj U).hom ≫ v).op.toLoc
    (by simp))
  exact (AlgebraicGeometry.Etale.iso_conj_map c s
    ((pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U).hom).map
      (pullbackObjUnitIso v).inv)).trans
        ((pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U).hom).map_comp _ _).symm

private def framePullbackMap {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) (L' : T'.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} L']
    [SheafOfModules.IsInvertible.{u, u, u} ((pullback v).obj L)]
    (e : (pullback v).obj L ≅ L') :
    (etaleIsoTorsor L).sheaf.obj ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ v).op ⋙ (etaleIsoTorsor L').sheaf.obj where
  app U := TypeCat.ofHom fun x ↦
    have : IsIso (etaleIsoTorsorVal L (U := U) x) := x.down.2
    have hx : IsIso (presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x)) :=
      isIso_presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x)
    have he : IsIso
        ((pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map e.hom) :=
      inferInstance
    etaleIsoTorsorMk L'
      (U := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop))
      (presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x) ≫
        (pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map e.hom)
      (@IsIso.comp_isIso' _ _ _ _ _ _ _ hx he)
  naturality U V f := by
    ext x
    apply etaleIsoTorsorVal_injective L'
      (U := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj V.unop))
    change presheafHomPullback v L V.unop
        ((modulesPseudofunctor.presheafHom (unitObj T) L).map
          ((toProEt T ⋙ ProEt.forget T).map f.unop).op (etaleIsoTorsorVal L (U := U) x)) ≫ _ =
      (modulesPseudofunctor.presheafHom (unitObj T') L').map
        ((toProEt T' ⋙ ProEt.forget T').map
          ((MorphismProperty.Over.pullback @Etale ⊤ v).map f.unop)).op
        (presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x) ≫ _)
    exact ((Pseudofunctor.presheafHom_map_comp
      ((toProEt T' ⋙ ProEt.forget T').map
        ((MorphismProperty.Over.pullback @Etale ⊤ v).map f.unop))
      (presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x))
      ((pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map e.hom)).trans
        (congrArg₂ (fun s t ↦ s ≫ t)
          (presheafHomPullback_naturality v L f.unop (etaleIsoTorsorVal L (U := U) x))
          (pullbackMap_presheaf_map ((pullback v).obj L) L'
            ((toProEt T' ⋙ ProEt.forget T').map
              ((MorphismProperty.Over.pullback @Etale ⊤ v).map f.unop)) e.hom))).symm

private theorem framePullbackMap_val {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) (L' : T'.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} L']
    [SheafOfModules.IsInvertible.{u, u, u} ((pullback v).obj L)]
    (e : (pullback v).obj L ≅ L') (U : T.Etaleᵒᵖ)
    (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    etaleIsoTorsorVal L'
        (U := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop))
        ((framePullbackMap v L L' e).app U x) =
      presheafHomPullback v L U.unop (etaleIsoTorsorVal L (U := U) x) ≫
        (pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map e.hom :=
  rfl

attribute [local irreducible] framePullbackMap

private theorem etaleIsoTorsorVal_map {T : Scheme.{u}} (L : T.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    {U V : T.Etaleᵒᵖ} (f : U ⟶ V) (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    etaleIsoTorsorVal L (U := V) ((etaleIsoTorsor L).sheaf.obj.map f x) =
      (modulesPseudofunctor.presheafHom (unitObj T) L).map
        ((toProEt T ⋙ ProEt.forget T).map f.unop).op
        (etaleIsoTorsorVal L (U := U) x) := rfl

private theorem framePullbackMap_vadd {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) (L' : T'.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} L']
    [SheafOfModules.IsInvertible.{u, u, u} ((pullback v).obj L)]
    (e : (pullback v).obj L ≅ L')
    (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U) (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    (framePullbackMap v L L' e).app U ((etaleIsoTorsor L).vadd U g x) =
      (etaleIsoTorsor L').vadd _ ((gmSheafToLowerStarGmSheaf v).hom.app U g)
        ((framePullbackMap v L L' e).app U x) := by
  apply etaleIsoTorsorVal_injective L'
    (U := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop))
  let V := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop)
  let : SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map v.op.toLoc).toFunctor.obj L : T'.Modules) :=
    inferInstanceAs (SheafOfModules.IsInvertible.{u, u, u} ((pullback v).obj L))
  have hv := congrArg (etaleIsoTorsorVal ((pullback v).obj L) (U := V))
    (Scheme.etaleIsoTorsorPullback_vadd v L U g x)
  have ha := etaleIsoTorsorVal_vadd L' (U := V)
    ((gmSheafToLowerStarGmSheaf v).hom.app U g) ((framePullbackMap v L L' e).app U x)
  erw [ha, framePullbackMap_val v L L' e U ((etaleIsoTorsor L).vadd U g x),
    framePullbackMap_val v L L' e U x]
  exact (congrArg (· ≫
    (pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map e.hom)
      hv).trans (Category.assoc _ _ _)

private theorem framePullbackMap_section {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) (L' : T'.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} L']
    [SheafOfModules.IsInvertible.{u, u, u} ((pullback v).obj L)]
    (e : (pullback v).obj L ≅ L') (s : unit T ⟶ L) (s' : unit T' ⟶ L')
    (hs : (pullback v).map s ≫ e.hom = (pullbackObjUnitIso v).hom ≫ s')
    (U : T.Etaleᵒᵖ) (x : (etaleIsoTorsor L).sheaf.obj.obj U)
    (hx : etaleIsoTorsorVal L (U := U) x = (pullback U.unop.hom).map s) :
    etaleIsoTorsorVal L'
      (U := op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop))
      ((framePullbackMap v L L' e).app U x) =
      (pullback ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop).hom).map s' := by
  rw [framePullbackMap_val, hx, presheafHomPullback_map]
  erw [← Functor.map_comp, Category.assoc, hs,
    Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Scheme.Modules.framePullbackMap

set_option maxRecDepth 2000 in
/-- An equivariant map of framed torsors gives the naturality square for their
relative integral extension classes under any scheme map. Only the exchange map
is required, not its inverse. -/
theorem relative_extension_pullback_square {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) (w : Z' ⟶ Z) (sq : IsPullback w i' i h)
    (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
    (hb : ∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      b.app V (P.1.vadd V g t) =
        Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V.unop))
          (f.hom.app V g) (b.app V t)) :
    (Ext.mk₀ (relativeExtensionExchange i i' h w sq.toCommSq)).comp
        (relativeExtension i' (relativeExtensionPulledFrame i i' h hW P Q b))
        (zero_add 1) =
      ((relativeExtension i P).mapExactFunctor (upperStar AddCommGrpCat.{u + 1} h)).comp
        (Ext.mk₀ (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv _ _).symm f))
        (add_zero 1) := by
  let F := lowerStar AddCommGrpCat.{u + 1} h
  let L := upperStar AddCommGrpCat.{u + 1} h
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h
  let B := MorphismProperty.Over.pullback @Etale ⊤ h
  let c := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let e := relativeExtensionExchange i i' h w sq.toCommSq
  let R := relativeExtensionPulledFrame i i' h hW P Q b
  obtain ⟨E', a', b', hab', hE', f', hfa', hfb', hfτ', hβ'⟩ :=
    (Classical.choose_spec (relativeExtension_existsUnique i' R)).1
  change relativeExtension i' R = hE'.extClass at hβ'
  let r := (adj.homEquiv _ _).toFun e
  have hp : supportedIntegralUnit i ≫ r =
      supportedIntegralUnit h ≫ F.map (supportedIntegralUnit i') := by
    change supportedIntegralUnit i ≫ adj.homEquiv _ _ e =
      adj.homEquiv _ _ c.hom ≫ F.map (supportedIntegralUnit i')
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    apply congrArg (adj.homEquiv _ _)
    have hu := integralBaseChangeUnit h i i' w sq.toCommSq
    change c.inv ≫ L.map (supportedIntegralUnit i) ≫ e = _ at hu
    have hh := congrArg (fun t ↦ c.hom ≫ t) hu
    simpa only [← Category.assoc, c.hom_inv_id, Category.id_comp] using hh
  let φ := b ≫ Functor.whiskerLeft B.op f'
  have hφa (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V) :
      φ.app V (P.1.vadd V g t) =
        (show (F.obj E').obj.obj V from φ.app V t) + (f ≫ F.map a').hom.app V g := by
    change f'.app (op (B.obj V.unop)) (b.app V (P.1.vadd V g t)) = _
    exact (congrArg (f'.app (op (B.obj V.unop))) (hb V g t)).trans
      (hfa' (op (B.obj V.unop)) (f.hom.app V g) (b.app V t))
  have hφb (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V) :
      (F.map b').hom.app V (φ.app V t) =
        (supportedIntegralUnit i ≫ r).hom.app V
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
              V ⟨1⟩) := by
    rw [hp]
    exact (hfb' (op (B.obj V.unop)) (b.app V t)).trans
      (congrArg ((supportedIntegralUnit i').hom.app (op (B.obj V.unop)))
        (integralUnit_section h V.unop ⟨1⟩).symm)
  let U := Scheme.Etale.mk i.openComplement.ι
  let U' := Scheme.Etale.mk i'.openComplement.ι
  let k : U' ⟶ B.obj U :=
    eqToHom (congrArg (fun W : T'.Opens ↦ Scheme.Etale.mk W.ι) hW) ≫
      openSectionPullback h i.openComplement
  have hk : IsIso k := by
    have : IsIso (openSectionPullback h i.openComplement) :=
      openSectionPullback_isIso h i.openComplement
    dsimp only [k]
    infer_instance
  have hφτ : (show (F.obj E').obj.obj (op U) from φ.app (op U) P.2) = 0 := by
    apply (asIso (E'.obj.map k.op)).addCommGroupIsoToAddEquiv.injective
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom (f'.naturality k.op) (b.app (op U) P.2)
    change _ = E'.obj.map k.op (φ.app (op U) P.2) at hn
    change E'.obj.map k.op (φ.app (op U) P.2) = 0
    exact hn.symm.trans hfτ'
  obtain ⟨E, a₀, b₀, hab₀, hE, hβ, α, hαa, hαb⟩ :=
    relativeExtension_morphism i P f (F.obj E') (F.map a') (F.map b')
      (by rw [← F.map_comp, hab', F.map_zero]) r φ hφa hφb hφτ
  let α' := (adj.homEquiv _ _).symm α
  let f₀ := (adj.homEquiv _ _).symm f
  have hα'a : L.map a₀ ≫ α' = f₀ ≫ a' := by
    exact (adj.homEquiv_naturality_left_symm a₀ α).symm.trans
      ((congrArg (adj.homEquiv _ _).symm hαa).trans
        (adj.homEquiv_naturality_right_symm f a'))
  have hα'b : α' ≫ b' = L.map b₀ ≫ e := by
    exact (adj.homEquiv_naturality_right_symm α b').symm.trans
      ((congrArg (adj.homEquiv _ _).symm hαb).trans
        ((adj.homEquiv_naturality_left_symm b₀ r).trans
          (congrArg (L.map b₀ ≫ ·) ((adj.homEquiv _ _).symm_apply_apply e))))
  have hn := (hE.map_of_exact L).extClass_naturality hE'
    (ShortComplex.homMk f₀ α' e hα'a.symm hα'b)
  change (hE.map_of_exact L).extClass.comp (Ext.mk₀ f₀) (add_zero 1) =
    (Ext.mk₀ e).comp hE'.extClass (zero_add 1) at hn
  rw [← Ext.mapExactFunctor_extClass L hE] at hn
  rw [← hβ, ← hβ'] at hn
  exact hn.symm

end AlgebraicGeometry.Etale
