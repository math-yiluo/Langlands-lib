/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Simultaneous local representatives for étale inverse images

Source: Stacks Project, Tag 09XN (description of inverse image) and Tag 00YV
(inverse image commutes with algebraic structures).
(blueprint: lem-sc-etale-inverse-image-joint-representatives)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pair_section {C : Type*} [Category C] (E : C ⥤ Type (u + 1))
    (A B : C) [HasBinaryProduct A B] [PreservesLimit (pair A B) E]
    (a : E.obj A) (b : E.obj B) :
    ∃ x : E.obj (A ⨯ B), E.map prod.fst x = a ∧ E.map prod.snd x = b := by
  let e := asIso (prodComparison E A B) ≪≫ Types.binaryProductIso (E.obj A) (E.obj B)
  let x := e.inv (a, b)
  have he : e.hom x = (a, b) := e.toEquiv.apply_symm_apply (a, b)
  refine ⟨x, ?_, ?_⟩
  · have hf : e.hom ≫ TypeCat.ofHom Prod.fst = E.map prod.fst := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      rw [Category.assoc, Types.binaryProductIso_hom_comp_fst]
      exact prodComparison_fst E A B
    calc
      E.map prod.fst x = (e.hom x).1 := ConcreteCategory.congr_hom hf.symm x
      _ = a := congrArg Prod.fst he
  · have hf : e.hom ≫ TypeCat.ofHom Prod.snd = E.map prod.snd := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      rw [Category.assoc, Types.binaryProductIso_hom_comp_snd]
      exact prodComparison_snd E A B
    calc
      E.map prod.snd x = (e.hom x).2 := ConcreteCategory.congr_hom hf.symm x
      _ = b := congrArg Prod.snd he

/-- Any pair of sections of an abelian and a set inverse image is locally pulled back
from a pair of sections on the same étale object.

Source: Stacks Project, Tags 09XN and 00YV.
(blueprint: lem-sc-etale-inverse-image-joint-representatives)

Proof: Forget the abelian sheaf to sets. The abelian and set inverse images are
identified by the comparison compatible with the adjunction units (00YV). Set inverse
image preserves binary products. Regard the given pair as a section of the inverse
image of the product of the two set sheaves. The sheafification unit is locally
surjective, so on a covering sieve it has representatives in the left Kan extension.
Each such representative comes from one object of the Kan indexing category (09XN).
Project the representing product section to its two factors. Naturality of both
projections and compatibility of the abelian comparison with units give the two
identities. This argument works at every test object, not just the terminal one.
Empty sections cause no exception: their pair exists only when both factors do;
on an empty test scheme the empty sieve covers. -/
theorem etaleInverseImage_joint_representatives
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : Y.Etaleᵒᵖ)
    (a : ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj.obj U)
    (t : ((Scheme.etaleSetPullback f).obj F).obj.obj U) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
      (Y.smallGrothendieckTopology @Etale)).unit.app F
    let ηG := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G
    ∃ R : Sieve U.unop, R ∈ Y.smallEtaleTopology U.unop ∧
      ∀ (V : Y.Etale) (i : V ⟶ U.unop), R i →
        ∃ (W : X.Etale) (k : V ⟶ b.obj W)
          (g : G.obj.obj (op W)) (s : F.obj.obj (op W)),
          ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map i.op a =
            ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map k.op
              (ηG.hom.app (op W) g) ∧
          ((Scheme.etaleSetPullback f).obj F).obj.map i.op t =
            ((Scheme.etaleSetPullback f).obj F).obj.map k.op
              (η.hom.app (op W) s) := by
  dsimp only
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let FG := (sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj G
  let P := FG ⨯ F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  have hL : PreservesFiniteLimits L := by
    unfold L Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, hea⟩ := etaleInverseImageAbelianLift_hom Y X f hL
  have : PreservesFiniteLimits L := hL
  let E := L ⋙ sheafToPresheaf Y.smallEtaleTopology (Type (u + 1)) ⋙
    (evaluation Y.Etaleᵒᵖ (Type (u + 1))).obj U
  obtain ⟨x, hxg, hxt⟩ := pair_section E FG F ((ea.hom.app G).hom.app U a) t
  change (L.map (prod.fst : P ⟶ FG)).hom.app U x =
    (ea.hom.app G).hom.app U a at hxg
  change (L.map (prod.snd : P ⟶ F)).hom.app U x = t at hxt
  let Q := b.op.lan.obj P.obj
  let R := Presheaf.imageSieve (toSheafify Y.smallEtaleTopology Q) x
  refine ⟨R, ?_, ?_⟩
  · exact Presheaf.imageSieve_mem Y.smallEtaleTopology
      (toSheafify Y.smallEtaleTopology Q) x
  intro V i hi
  obtain ⟨p, hp⟩ := hi
  obtain ⟨W, k, z, hz⟩ := etaleInverseImageSectionDescription_representation X Y f P V p
  have hx : (L.obj P).obj.map i.op x =
      (L.obj P).obj.map k.op ((adj.unit.app P).hom.app (op W) z) := by
    exact hp.symm.trans hz
  let g := (prod.fst : P ⟶ FG).hom.app (op W) z
  let s := (prod.snd : P ⟶ F).hom.app (op W) z
  refine ⟨W, k, g, s, ?_, ?_⟩
  · have hh := congrArg ((L.map (prod.fst : P ⟶ FG)).hom.app (op V)) hx
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at hh
    change (L.obj FG).obj.map i.op ((L.map prod.fst).hom.app U x) =
      (L.obj FG).obj.map k.op
        ((L.map prod.fst).hom.app (op (b.obj W))
          ((adj.unit.app P).hom.app (op W) z)) at hh
    rw [hxg] at hh
    have hη := congrArg (fun q ↦ q.hom.app (op W) z)
      (adj.unit_naturality (prod.fst : P ⟶ FG)).symm
    change (adj.unit.app FG).hom.app (op W) g =
      (L.map prod.fst).hom.app (op (b.obj W))
        ((adj.unit.app P).hom.app (op W) z) at hη
    rw [← hη] at hh
    have he := hea G _ (𝟙 _)
    rw [(Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_id]
      at he
    have he' :
        (sheafForget X.smallEtaleTopology).map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G) =
        adj.homEquiv FG _ (ea.inv.app G) := by
      simpa using he
    have hu : (ea.hom.app G).hom.app (op (b.obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
          (op W) g) = (adj.unit.app FG).hom.app (op W) g := by
      rw [Adjunction.homEquiv_unit] at he'
      have h := congrArg (fun q ↦ q.hom.app (op W) g) he'
      change _ = (ea.inv.app G).hom.app (op (b.obj W))
        ((adj.unit.app FG).hom.app (op W) g) at h
      change (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        G).hom.app (op W) g) = _ at h
      erw [h]
      exact congrArg (fun q ↦ q.hom.app (op (b.obj W))
        ((adj.unit.app FG).hom.app (op W) g)) (ea.app G).inv_hom_id
    erw [← hu, ← NatTrans.naturality_apply (ea.hom.app G).hom i.op,
      ← NatTrans.naturality_apply (ea.hom.app G).hom k.op] at hh
    exact (((sheafSections Y.smallEtaleTopology (Type (u + 1))).obj (op V)).mapIso
      (ea.app G)).toEquiv.injective hh
  · have hh := congrArg ((L.map (prod.snd : P ⟶ F)).hom.app (op V)) hx
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at hh
    change (L.obj F).obj.map i.op ((L.map prod.snd).hom.app U x) =
      (L.obj F).obj.map k.op
        ((L.map prod.snd).hom.app (op (b.obj W))
          ((adj.unit.app P).hom.app (op W) z)) at hh
    rw [hxt] at hh
    have hη := congrArg (fun q ↦ q.hom.app (op W) z)
      (adj.unit_naturality (prod.snd : P ⟶ F)).symm
    change (adj.unit.app F).hom.app (op W) s =
      (L.map prod.snd).hom.app (op (b.obj W))
        ((adj.unit.app P).hom.app (op W) z) at hη
    exact hh.trans (congrArg ((L.obj F).obj.map k.op) hη.symm)

end AlgebraicGeometry
