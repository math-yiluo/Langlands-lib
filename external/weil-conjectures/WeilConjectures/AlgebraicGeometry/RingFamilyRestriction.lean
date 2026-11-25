/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
public import WeilConjectures.CategoryTheory.ModuleSheafificationRestriction

/-! # Restriction of sheafified ring-family complexes

Source: Stacks Project, Tag 099E, restriction compatibility of K_{U,I}.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace CategoryTheory
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {L : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J L] [F.IsCocontinuous J L]
variable (O : Sheaf L CommRingCat.{u})
variable (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
variable (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
variable (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- Restrict the given global ring sections along the functor of sites.
Source: Stacks Project, Tag 099E.
(auxiliary; not a blueprint node). -/
def ringFamilyRestrictedSections : Fin r →
    ((((F.sheafPushforwardContinuous CommRingCat.{u} J L).obj O).obj) ⋙
      forget CommRingCat).sections :=
  fun i ↦ ⟨fun X ↦ (f i).val (F.op.obj X), fun a ↦ (f i).property (F.op.map a)⟩

/-- Ring-family complexes commute with restriction and module sheafification.
Source: Stacks Project, Tag 099E, K_{V,I O(V)} = K_{U,I}|_V.
(auxiliary; not a blueprint node).

Proof: the presheaf complexes commute with restriction section by section: both use the
same ring, generated ideal, transition map and differential. Apply the unit-compatible
module-sheafification restriction isomorphism degreewise. Its naturality for each
presheaf differential gives a chain isomorphism. -/
theorem exists_ringFamilySheafModel_restrictionIso :
    ∃ e : (ringFamilySheafModel
        ((F.sheafPushforwardContinuous CommRingCat.{u} J L).obj O)
        K ε m hm r (ringFamilyRestrictedSections F O r f)).1 ≅
      (((SheafOfModules.pushforward (F := F)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj
          ((sheafCompose L (forget₂ CommRingCat RingCat)).obj O)))).mapHomologicalComplex
          (.up ℤ)).obj
        (ringFamilySheafModel O K ε m hm r f).1),
      ∀ (n : ℤ) (X : Cᵒᵖ)
        (x : ((ringFamilyPresheafComplex O K ε m hm r f).X n).obj (F.op.obj X)),
        (e.hom.f n).val.app X
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
                ((F.sheafPushforwardContinuous CommRingCat.{u} J L).obj O)).obj)).unit.app
                  ((ringFamilyPresheafComplex
                    ((F.sheafPushforwardContinuous CommRingCat.{u} J L).obj O)
                    K ε m hm r (ringFamilyRestrictedSections F O r f)).X n)).app X x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose L (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
              ((ringFamilyPresheafComplex O K ε m hm r f).X n)).app (F.op.obj X) x) := by
  let O' := (F.sheafPushforwardContinuous CommRingCat.{u} J L).obj O
  let R := (sheafCompose L (forget₂ CommRingCat RingCat)).obj O
  let P := PresheafOfModules.pushforward (F := F)
    (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R).obj)
  let Q := SheafOfModules.pushforward (F := F)
    (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R))
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let S' := PresheafOfModules.sheafification
    (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R).obj)
  let M := ringFamilyPresheafComplex O K ε m hm r f
  let N := ringFamilyPresheafComplex O' K ε m hm r (ringFamilyRestrictedSections F O r f)
  let c (n : ℤ) : P.obj (M.X n) ≅ N.X n :=
    PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by intro X Y a; rfl)
  obtain ⟨z, hz⟩ := PresheafOfModules.exists_moduleSheafificationRestrictionIso
    (J := J) F R
  let e (n : ℤ) : S'.obj (N.X n) ≅ Q.obj (S.obj (M.X n)) :=
    S'.mapIso (c n).symm ≪≫ z.app (M.X n)
  have hd (n k : ℤ) :
      (e n).hom ≫ Q.map (S.map (M.d n k)) = S'.map (N.d n k) ≫ (e k).hom := by
    change S'.map (c n).inv ≫ (z.app (M.X n)).hom ≫ Q.map (S.map (M.d n k)) = _
    have hh : (z.app (M.X n)).hom ≫ Q.map (S.map (M.d n k)) =
        S'.map (P.map (M.d n k)) ≫ (z.app (M.X k)).hom :=
      (z.hom.naturality (M.d n k)).symm
    rw [hh, ← Category.assoc]
    have hc : (c n).inv ≫ P.map (M.d n k) = N.d n k ≫ (c k).inv := by
      ext X x
      rfl
    rw [← Functor.map_comp, hc, Functor.map_comp, Category.assoc]
    rfl
  have : Q.Additive := ⟨fun {_ _} a b ↦ by ext X x; rfl⟩
  refine ⟨HomologicalComplex.Hom.isoOfComponents e (fun n k _ ↦ hd n k), ?_⟩
  intro n X x
  have hh := congrArg (fun z ↦ z.app X x)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R).obj)).unit.naturality
        (c n).inv)
  change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R).obj)).unit.app
        (P.obj (M.X n))).app X x =
    (S'.map (c n).inv).val.app X
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J L).obj R).obj)).unit.app
          (N.X n)).app X x) at hh
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f, e, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  change (z.app (M.X n)).hom.val.app X
    ((S'.map (c n).inv).val.app X _) = _
  exact (congrArg ((z.app (M.X n)).hom.val.app X) hh.symm).trans (hz (M.X n) X x)

end CategoryTheory
