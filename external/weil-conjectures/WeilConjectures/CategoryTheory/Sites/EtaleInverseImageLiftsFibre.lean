/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # The underlying fibre comparison for étale inverse image

Source: Stacks Project, Tags 03AJ and 00X6
(blueprint: lem-sc-etale-inverse-image-lifts-fibre).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency false

section Fibre

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {E : C} (hE : IsTerminal E)
  (S : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}))
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (hS : S.ShortExact) (s : S.X₃.obj.obj (op E))

private def fibreConst : (sheafForget J).obj S.X₂ ⟶ (sheafForget J).obj S.X₃ :=
  ⟨{ app := fun W ↦ ↾fun _ ↦ S.X₃.obj.map (hE.from W.unop).op s
     naturality := by
       intro W V k
       ext x
       change S.X₃.obj.map (hE.from V.unop).op s =
         S.X₃.obj.map k (S.X₃.obj.map (hE.from W.unop).op s)
       rw [← ConcreteCategory.comp_apply, ← S.X₃.obj.map_comp]
       have hh : (hE.from V.unop).op = (hE.from W.unop).op ≫ k := by
         simpa only [op_comp, Quiver.Hom.op_unop] using
           congrArg Quiver.Hom.op (hE.hom_ext (hE.from V.unop)
             (k.unop ≫ hE.from W.unop))
       rw [hh] }⟩

private def fibreInclusion : (lifts hE hS s).sheaf ⟶ (sheafForget J).obj S.X₂ :=
  ⟨(liftsSubfunctor S.g hE s).ι⟩

private theorem fibreCondition :
    fibreInclusion hE S hS s ≫ (sheafForget J).map S.g =
      fibreInclusion hE S hS s ≫ fibreConst hE S s := by
  ext W x
  exact x.property

private noncomputable def fibreIsLimit :
    IsLimit (Fork.ofι (fibreInclusion hE S hS s) (fibreCondition hE S hS s)) := by
  refine Fork.IsLimit.mk _ (fun k ↦ ?_) ?_ ?_
  · refine ⟨{ app := fun W ↦ ↾fun x ↦ ⟨k.ι.hom.app W x, ?_⟩
              naturality := ?_ }⟩
    · exact congrArg (fun h ↦ h.hom.app W x) k.condition
    · intro W V j
      ext x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (k.ι.hom.naturality j) x
  · intro k
    rfl
  · intro k m hm
    ext W x
    apply Subtype.ext
    exact congrArg (fun h ↦ h.hom.app W x) hm

end Fibre

/-- Set inverse image identifies the underlying fibre sheaves, compatibly with their
inclusions into the abelian middle objects on sections from the adjunction unit.
Source: Stacks Project, Tag 03AJ (the sheaf of lifts) and Tag 00X6 (finite limits).
(blueprint: lem-sc-etale-inverse-image-lifts-fibre)

Proof: The subtype sheaf of lifts is the equalizer of the underlying quotient map
and the map sending every section to the restriction of s. Express this as a limiting
fork, with the subtype inclusion as its arrow. Apply the finite-limit-preserving set
inverse image. The underlying abelian inverse-image comparison identifies its middle
and quotient objects with the corresponding abelian inverse images, naturally in the
quotient map. Its unit equation and the terminal comparison in the global-section
pullback identify the image of the constant-section map with the restriction of s'.
The resulting fork is the defining equalizer fork of the target subtype sheaf. The
unique isomorphism of the two limiting forks gives e. Its equation with the fork
arrows, evaluated on the set adjunction unit, together with the abelian comparison's
unit equation, is the displayed equality. No action or torsor-isomorphism transport
is asserted here. -/
theorem etale_inverse_image_lifts_fibre
    (X Y : Scheme.{u}) (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact)
    (s : S.X₃.obj.obj (op (⊤_ X.Etale))) :
    let U := Etale.upperStar AddCommGrpCat.{u + 1} f
    let hY := hS.map_of_exact U
    let s' := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.app (U.obj S.X₃)
      (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f S.X₃
        ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).inv.app S.X₃ s))
    let T' := lifts terminalIsTerminal hY s'
    ∃ e : (Scheme.etaleSetPullback f).obj (lifts terminalIsTerminal hS s).sheaf ≅
        T'.sheaf,
      ∀ (W : X.Etale) (t : (lifts terminalIsTerminal hS s).sheaf.obj.obj (op W)),
        (e.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (Y.smallGrothendieckTopology @Etale)).unit.app
              (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t)).val =
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app S.X₂).hom.app
          (op W) t.val := by
  dsimp only
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let U := Etale.upperStar AddCommGrpCat.{u + 1} f
  let FX := sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology
  let FY := sheafForget (D := AddCommGrpCat.{u + 1}) Y.smallEtaleTopology
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  let aa := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let s' := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.app (U.obj S.X₃)
      (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f S.X₃
        ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).inv.app S.X₃ s))
  obtain ⟨hL, ea, da, Lr, ar, er, dr, hd, hdr, hhom, hunit, hrest⟩ :=
    etaleInverseImageAlgebraicStructures Y X f
  clear hdr hunit hrest Lr ar er dr
  let := hL
  have hη (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (W : X.Etaleᵒᵖ) (x : G.obj.obj W) :
      (ea.inv.app G).hom.app (b.op.obj W) ((a.unit.app (FX.obj G)).hom.app W x) =
        (aa.unit.app G).hom.app W x := by
    have hh := hhom G (U.obj G) (𝟙 _)
    simp only [Functor.map_id] at hh
    have hv := congrArg (fun k ↦ k.hom.app W x) hh
    rw [Adjunction.homEquiv_unit] at hv
    change (da.hom.app (U.obj G)).hom.app W ((aa.unit.app G).hom.app W x) = _ at hv
    rw [hd] at hv
    exact hv.symm
  clear hhom hd da
  have hs' (W : X.Etaleᵒᵖ) :
      (U.obj S.X₃).obj.map (terminalIsTerminal.from (b.op.obj W).unop).op s' =
        (aa.unit.app S.X₃).hom.app W
          (S.X₃.obj.map (terminalIsTerminal.from W.unop).op s) := by
    have hs0 : s' = (U.obj S.X₃).obj.map (PreservesTerminal.iso f.Etale).inv.op
        ((aa.unit.app S.X₃).hom.app (op (⊤_ X.Etale)) s) := by
      dsimp [s', Etale.globalSectionsUpperStarMap]
      simp only [U, aa, ← ConcreteCategory.comp_apply, Category.assoc,
        Iso.inv_hom_id_app]
      rfl
    rw [hs0]
    have hh : terminalIsTerminal.from (b.op.obj W).unop ≫
        (PreservesTerminal.iso f.Etale).inv =
      b.map (terminalIsTerminal.from W.unop) := by
      apply (cancel_mono (PreservesTerminal.iso f.Etale).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact terminalIsTerminal.hom_ext _ _
    have hn := ConcreteCategory.congr_hom
      ((aa.unit.app S.X₃).hom.naturality (terminalIsTerminal.from W.unop).op) s
    change (aa.unit.app S.X₃).hom.app W
        (S.X₃.obj.map (terminalIsTerminal.from W.unop).op s) =
      (U.obj S.X₃).obj.map (b.map (terminalIsTerminal.from W.unop)).op
        ((aa.unit.app S.X₃).hom.app (op (⊤_ X.Etale)) s) at hn
    rw [← hh] at hn
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hn
    exact hn.symm
  let i := fibreInclusion terminalIsTerminal S hS s
  let k := fibreConst terminalIsTerminal S s
  let SY := S.map U
  let hY := hS.map_of_exact U
  let ky := fibreConst terminalIsTerminal SY s'
  have hd' : (ea.app S.X₂).inv ≫ FY.map SY.g =
      L.map (FX.map S.g) ≫ (ea.app S.X₃).inv := by
    exact (ea.inv.naturality S.g).symm
  have hk' : (ea.app S.X₂).inv ≫ ky = L.map k ≫ (ea.app S.X₃).inv := by
    apply (a.homEquiv _ _).injective
    ext W x
    simp only [Adjunction.homEquiv_unit]
    change (U.obj S.X₃).obj.map
        (terminalIsTerminal.from (b.op.obj W).unop).op s' =
      (ea.inv.app S.X₃).hom.app (b.op.obj W)
        ((L.map k).hom.app (b.op.obj W) ((a.unit.app (FX.obj S.X₂)).hom.app W x))
    have hn := congrArg (fun z ↦ z.hom.app W x) (a.unit.naturality k)
    change (a.unit.app (FX.obj S.X₃)).hom.app W
        (S.X₃.obj.map (terminalIsTerminal.from W.unop).op s) =
      (L.map k).hom.app (b.op.obj W) ((a.unit.app (FX.obj S.X₂)).hom.app W x) at hn
    rw [← hn, hη, hs']
  let c := Fork.ofι (L.map i)
    (show L.map i ≫ L.map (FX.map S.g) = L.map i ≫ L.map k by
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map (fibreCondition terminalIsTerminal S hS s))
  have hc : IsLimit c :=
    isLimitForkMapOfIsLimit L _ (fibreIsLimit terminalIsTerminal S hS s)
  let cy := (Fork.equivOfIsos (ea.app S.X₂).symm (ea.app S.X₃).symm
    hd' hk').functor.obj c
  have hcy : IsLimit cy := Fork.isLimitOfIsos c hc cy
    (ea.app S.X₂).symm (ea.app S.X₃).symm (CategoryTheory.Iso.refl _)
    hd' hk' (by simp [cy])
  let ly := fibreIsLimit terminalIsTerminal SY hY s'
  let e := hcy.conePointUniqueUpToIso ly
  refine ⟨e, ?_⟩
  intro W t
  have he := hcy.conePointUniqueUpToIso_hom_comp ly WalkingParallelPair.zero
  have hv := congrArg (fun z ↦ z.hom.app (op (b.obj W))
    ((a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t)) he
  change (e.hom.hom.app (op (b.obj W))
      ((a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t)).val =
    (ea.inv.app S.X₂).hom.app (op (b.obj W))
      ((L.map i).hom.app (op (b.obj W))
        ((a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t)) at hv
  change (e.hom.hom.app (op (b.obj W))
      ((a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t)).val =
    (aa.unit.app S.X₂).hom.app (op W) t.val
  rw [hv]
  have hn := congrArg (fun z ↦ z.hom.app (op W) t) (a.unit.naturality i)
  change (a.unit.app (FX.obj S.X₂)).hom.app (op W) t.val =
    (L.map i).hom.app (op (b.obj W))
      ((a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W) t) at hn
  rw [← hn]
  exact hη S.X₂ (op W) t.val

end CategoryTheory.Sheaf.Torsor
