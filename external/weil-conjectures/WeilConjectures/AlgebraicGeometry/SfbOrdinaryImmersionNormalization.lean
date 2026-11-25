/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import all WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites

/-! # Ordinary module comparisons for normalized restriction

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def resIdIso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) :
    ConstantCompletion.res (𝟙 R) ≅ 𝟭 (ConstantCompletion.Mod R) := Iso.refl _

private noncomputable def scalarEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    ConstantCompletion.Mod S ≌ ConstantCompletion.Mod R :=
  CategoryTheory.Equivalence.mk (ConstantCompletion.res c.hom) (ConstantCompletion.res c.inv)
    (ConstantCompletion.resCompIso c.inv c.hom (𝟙 S) c.inv_hom_id ≪≫ resIdIso S).symm
    (ConstantCompletion.resCompIso c.hom c.inv (𝟙 R) c.hom_inv_id ≪≫ resIdIso R)

private noncomputable def pullScalarIso
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    (F : ConstantCompletion.InverseImageData L)
    {R : Sheaf J CommRingCat.{u + 1}}
    {S T : Sheaf K CommRingCat.{u + 1}}
    (e : F.rings.obj R ≅ S) (c : F.rings.obj R ⟶ T) [IsIso c] :
    ConstantCompletion.pull F c ≅
      ConstantCompletion.pull F e.hom ⋙
        ConstantCompletion.res (e.symm ≪≫ asIso c).inv := by
  let d := e.symm ≪≫ asIso c
  let E := scalarEquivalence d
  let a := (SheafOfModules.tensorAdjunction e.hom).comp E.symm.toAdjunction
  let right : E.functor ⋙ ConstantCompletion.res e.hom ≅ ConstantCompletion.res c := by
    change ConstantCompletion.res d.hom ⋙ ConstantCompletion.res e.hom ≅
      ConstantCompletion.res c
    exact ConstantCompletion.resCompIso e.hom d.hom c (by
      simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.hom_inv_id_assoc])
  exact Functor.isoWhiskerLeft (F.algebra R).modules
    ((SheafOfModules.tensorAdjunction c).leftAdjointUniq (a.ofNatIsoRight right))

private noncomputable def sourceNormalization
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {V : C ⥤ D} [V.IsContinuous J K]
    {R B : Sheaf J CommRingCat.{u + 1}} {T : Sheaf K CommRingCat.{u + 1}}
    (e : R ≅ B) (φ : R ⟶ (V.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj T)
    [(SheafOfModules.pushforward.{u + 1} (F := V) (J := J) (K := K) (R := siteModuleRings T)
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u + 1} (F := V) (J := J) (K := K) (R := siteModuleRings T)
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (e.inv ≫ φ))).IsRightAdjoint] :
    ConstantCompletion.res e.inv ⋙
      SheafOfModules.pullback (F := V) (J := J) (K := K) (R := siteModuleRings T)
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (e.inv ≫ φ)) ≅
      SheafOfModules.pullback (F := V) (J := J) (K := K) (R := siteModuleRings T)
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) := by
  let r := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let ψ : siteModuleRings B ⟶
      (V.sheafPushforwardContinuous RingCat.{u + 1} J K).obj (siteModuleRings T) :=
    r.map (e.inv ≫ φ)
  let E := scalarEquivalence e.symm
  let right : SheafOfModules.pushforward.{u + 1} (F := V) (J := J) (K := K)
      (R := siteModuleRings T) ψ ⋙ E.inverse ≅
      SheafOfModules.pushforward (F := V) (J := J) (K := K) (R := siteModuleRings T) (r.map φ) := by
    change SheafOfModules.pushforward.{u + 1} (F := V) (J := J) (K := K)
      (R := siteModuleRings T) ψ ⋙
      SheafOfModules.pushforward (F := 𝟭 C) (J := J) (K := J)
        (R := siteModuleRings B) (r.map e.hom) ≅ _
    exact SheafOfModules.pushforwardComp (F := 𝟭 C) (G := V)
      (J := J) (K := J) (K' := K) (R := siteModuleRings B)
      (R' := siteModuleRings T)
      (r.map e.hom) ψ ≪≫ SheafOfModules.pushforwardCongr (F := V) (J := J) (K := K)
        (R := siteModuleRings T) (by
        change r.map e.hom ≫ r.map (e.inv ≫ φ) = r.map φ
        rw [← Functor.map_comp, ← Category.assoc, e.hom_inv_id, Category.id_comp])
  let a := E.toAdjunction.comp
    (SheafOfModules.pullbackPushforwardAdjunction (F := V) (J := J) (K := K)
      (R := siteModuleRings T) ψ)
  exact (a.ofNatIsoRight right).leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction (F := V) (J := J) (K := K)
      (R := siteModuleRings T) (r.map φ))

-- The comparison elaborates module actions in two equivalent site presentations.
/-- The ordinary module inverse image commutes with normalization of the source
coefficient ring. The target coefficient identification is produced by the algebraic
inverse-image data and the specified invertible scalar map.

Source: Stacks Project, sites-modules.tex, lemmas `lemma-pullback-module` and
`lemma-adjoint-push-pull-modules` (Tags 03D2 and 03D3)
(auxiliary; not a blueprint node).

Proof: let phi0 be the transported original ring adjunction unit and precompose it
with eX inverse. Its transpose under the set-sheaf adjunction is invertible: the
unit-normalized ring presentation and uniqueness of left adjoints exhibit it as
a composite of isomorphisms. The graph equations of F.algebra lift this transpose
to an invertible ring map d. Restrict the underlying Hom adjunction to linear
maps and compose with the tensor/restriction adjunction. This identifies pull F d
with the specified continuous module pullback. Put eS=d inverse followed by c.
Scalar extension along c is extension along d followed by restriction along eS
inverse, since their right adjoints agree. Cancel eX in the source coefficient
map by the same adjunction argument. Finally remove extension along the identity
and cancel the module site equivalence in the original specified pullback.
Everything is ordinary and works for zero rings and empty schemes. -/
theorem sfbOrdinaryImmersionNormalization
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    (F : ConstantCompletion.InverseImageData (SfbAdicRestriction.inverse i))
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (BX : Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1})
    (BS : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1})
    (eX : (sfbModelRings X).obj R ≅ BX)
    (c : F.rings.obj BX ⟶ BS) [IsIso c] :
    ∃ eS : (sfbModelRings S).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) ≅ BS,
      Nonempty
        ((proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
            ConstantCompletion.res eX.inv) ⋙ ConstantCompletion.pull F c ≅
          proEtaleRingModulePullback i R
              ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ⋙
            (proEtaleModuleToModel ((adicLisseForget S).obj
                ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) ⋙
              ConstantCompletion.res eS.inv)) := by
  let J := proEtaleModelTopology X
  let K := proEtaleModelTopology S
  let V := proEtaleModelBaseChange i
  let RX := (sfbModelRings X).obj R
  let RS := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let RT := (sfbModelRings S).obj RS
  let φ₀ : RX ⟶ (V.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj RT :=
    ⟨Functor.whiskerLeft AsSmall.down.op
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom⟩
  let φ := eX.inv ≫ φ₀
  let a : SfbAdicRestriction.inverse i ⊣
      V.sheafPushforwardContinuous (Type (u + 1)) J K :=
    SfbAdicRestriction.adjunction i
  let f := SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos
    V (SfbAdicRestriction.inverse i) a RT BX φ
  obtain ⟨p, hp⟩ := proEtaleModelRingPresentation i R
  let forgetX := sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})
  let forgetS := sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous V (Type (u + 1)) J K
  let t := a.leftAdjointUniq b
  let q : (SfbAdicRestriction.inverse i).obj (forgetX.obj BX) ≅ forgetS.obj RT :=
    (SfbAdicRestriction.inverse i).mapIso (forgetX.mapIso eX.symm) ≪≫
      t.app (forgetX.obj RX) ≪≫ p.iso.symm
  have hf : f.ringMap =
      (a.homEquiv (forgetX.obj BX) (forgetS.obj RT)).symm (forgetX.map φ) := by
    rfl
  have hq : f.ringMap = q.hom := by
    rw [hf]
    apply (a.homEquiv (forgetX.obj BX) (forgetS.obj RT)).injective
    rw [Equiv.apply_symm_apply]
    dsimp only [q, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
    have ht : a.homEquiv (forgetX.obj RX)
        ((Functor.sheafPullbackConstruction.sheafPullback V (Type (u + 1)) J K).obj
          (forgetX.obj RX)) (t.app (forgetX.obj RX)).hom = b.unit.app (forgetX.obj RX) :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app a b (forgetX.obj RX)
    rw [ht]
    ext U x
    have he := p.equation U (eX.inv.hom.app U x)
    have hi := congrArg (fun k ↦ k.hom.app (V.op.obj U)) p.iso.hom_inv_id
    have hh := ConcreteCategory.congr_hom hi (p.unit.hom.app U (eX.inv.hom.app U x))
    change (φ₀.hom.app U) (eX.inv.hom.app U x) =
      p.iso.inv.hom.app (V.op.obj U) ((b.unit.app (forgetX.obj RX)).hom.app U
        (eX.inv.hom.app U x))
    rw [← he]
    exact (hp U _).symm.trans hh.symm
  have : IsIso f.ringMap := by rw [hq]; infer_instance
  obtain ⟨d, hd⟩ := SheafOfModules.RingedPresentationOnSites.structural_map
    K J RT BX f (F.rings.obj BX) (F.algebra BX)
  have : IsIso (forgetS.map d) := by rw [hd]; infer_instance
  have : IsIso d := isIso_of_reflects_iso d forgetS
  let e := asIso d
  let eS : RT ≅ BS := e.symm ≪≫ asIso c
  obtain ⟨ad⟩ := SheafOfModules.RingedPresentationOnSites.supplied_adjunction
    f (F.rings.obj BX) (F.algebra BX) d hd
  change ConstantCompletion.pull F d ⊣
    SheafOfModules.pushforward (F := V) (J := J) (K := K) (R := siteModuleRings RT)
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) at ad
  let φR : siteModuleRings BX ⟶
      (V.sheafPushforwardContinuous RingCat.{u + 1} J K).obj (siteModuleRings RT) :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
  have : (SheafOfModules.pushforward.{u + 1} (F := V) (J := J) (K := K)
      (R := siteModuleRings RT) φR).IsRightAdjoint := ad.isRightAdjoint
  let ed : ConstantCompletion.pull F d ≅
      SheafOfModules.pullback (F := V) (J := J) (K := K)
        (R := siteModuleRings RT) φR :=
    ad.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction
      (F := V) (J := J) (K := K) (R := siteModuleRings RT) φR)
  let ex : ConstantCompletion.res eX.inv ⋙
      SheafOfModules.pullback (F := V) (J := J) (K := K) (R := siteModuleRings RT) φR ≅
      SheafOfModules.pullback (proEtaleModelRingUnit i R) :=
    sourceNormalization (V := V) (J := J) (K := K) (T := RT) eX φ₀
  let extId : proEtaleRingExtension i R RS (Iso.refl _) ≅ 𝟭 _ :=
    (proEtaleRingExtensionAdjunction i R RS (Iso.refl _)).leftAdjointUniq Adjunction.id
  let eqv := proEtaleModuleModelEquivalence S ((adicLisseForget S).obj RS)
  let em : proEtaleRingModulePullback i R RS (Iso.refl _) ⋙
      proEtaleModuleToModel ((adicLisseForget S).obj RS) ≅
      proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
        SheafOfModules.pullback (proEtaleModelRingUnit i R) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (proEtaleModuleInverseImage i R) extId) _ ≪≫
      Functor.isoWhiskerLeft
        (proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
          SheafOfModules.pullback (proEtaleModelRingUnit i R)) eqv.unitIso.symm
  refine ⟨eS, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft
      (proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙ ConstantCompletion.res eX.inv)
      (pullScalarIso F e c) ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleToModel ((adicLisseForget X).obj R))
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (ConstantCompletion.res eX.inv) ed)
        (ConstantCompletion.res eS.inv)) ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleToModel ((adicLisseForget X).obj R))
      (Functor.isoWhiskerRight ex (ConstantCompletion.res eS.inv)) ≪≫
    Functor.isoWhiskerRight em.symm (ConstantCompletion.res eS.inv)

end AlgebraicGeometry.Scheme
