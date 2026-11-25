/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.RestrictionLocalCompleteness

/-! # Normalizing completed coefficients on the small pro-etale site

Source: Stacks Tags 00YY, 093M and 099C; Bhatt--Scholze, Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace SfbCompletionNormalization

private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

/-- Constant rings commute with transport to the small site.
Source: Stacks Tag 00YY (auxiliary; not a blueprint node). -/
def constants (X : Scheme.{u}) :
    constantSheaf (ProEt.topology X) CommRingCat.{u + 1} ⋙ sfbModelRings X ≅
      constantSheaf (proEtaleModelTopology X) CommRingCat.{u + 1} := by
  let G : proEtaleSiteModel X ⥤ X.ProEt := AsSmall.down
  have : G.IsDenseSubsite (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)) (ProEt.topology X))
  have : G.IsCocontinuous (proEtaleModelTopology X) (ProEt.topology X) := inferInstance
  let e := G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (proEtaleModelTopology X) (ProEt.topology X)
  exact NatIso.ofComponents
    (fun A ↦ (e.app ((Functor.const X.ProEtᵒᵖ).obj A)).symm)
    (fun f ↦ e.inv.naturality ((Functor.const X.ProEtᵒᵖ).map f))

/-- The finite quotient diagrams agree, including all transition maps.
Source: Stacks Tags 00YY and 093M (auxiliary; not a blueprint node). -/
def finiteComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) :
    adicLisseRingSystem X I ⋙ sfbModelRings X ≅
      ConstantCompletion.finiteSystem (proEtaleModelTopology X) A I := by
  let t : adicLisseRingSystem X I ⋙ sfbModelRings X ⟶
      ConstantCompletion.finiteSystem (proEtaleModelTopology X) A I :=
    NatTrans.ofOpSequence
      (fun n ↦ (constants X).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1)))) (by
        intro n
        simpa only [adicLisseRingSystem, ConstantCompletion.finiteSystem,
          Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
          ConstantCompletion.transition] using (constants X).hom.naturality
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))
  have : ∀ n, IsIso (t.app n) := fun n ↦ by
    change IsIso ((constants X).hom.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1))))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The canonical completed-ring comparison, constructed from finite projections.
Source: Stacks Tags 00YY and 093M
(auxiliary; not a blueprint node). -/
def coefficients (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbModelRings X).obj (adicLisseCompletedRing X I) ≅
      ConstantCompletion.completed (proEtaleModelTopology X) A I :=
  preservesLimitIso (sfbModelRings X) (adicLisseRingSystem X I) ≪≫
    HasLimit.isoOfNatIso (finiteComparison X I)

/-- Normalize the actual transported localization representative by scalar restriction
along the inverse of the canonical coefficient isomorphism.
Source: Stacks Tags 00YY and 099C
(auxiliary; not a blueprint node). -/
def object (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I) :=
  letI := HasDerivedCategory.standard
    (ConstantCompletion.Mod ((sfbModelRings X).obj (adicLisseCompletedRing X I)))
  let F : proEtaleRingModules X (adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod ((sfbModelRings X).obj (adicLisseCompletedRing X I)) :=
    proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  let : F.Additive := ⟨by intros; ext U x; rfl⟩
  let M := (ConstantCompletion.Q ((sfbModelRings X).obj (adicLisseCompletedRing X I))).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  (ConstantCompletion.Q _).obj
    (((ConstantCompletion.res (coefficients X I).inv).mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage M))

private theorem projection (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    (coefficients X I).hom ≫
        ConstantCompletion.projection (proEtaleModelTopology X) A I n =
      (sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op n)) ≫
        (constants X).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  dsimp only [coefficients, Iso.trans_hom, ConstantCompletion.projection]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    preservesLimitIso_hom_π]
  rfl

private theorem complete_iso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R B S T : Sheaf J CommRingCat.{u + 1}}
    (q : R ⟶ S) (p : B ⟶ T) (e : R ≅ B) (d : S ≅ T)
    (hq : e.hom ≫ p = q ≫ d.hom) (M : ConstantCompletion.D B) :
    ConstantCompletion.IsComplete q
      ((ConstantCompletion.Q _).obj
        (((ConstantCompletion.res e.hom).mapHomologicalComplex (.up ℤ)).obj
          (DerivedCategory.Q.objPreimage M))) ↔ ConstantCompletion.IsComplete p M := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  let := fun U : C ↦ HasDerivedCategory.standard (ConstantCompletion.Mod (R.over U))
  let := fun U : C ↦ HasDerivedCategory.standard (ConstantCompletion.Mod (B.over U))
  let IR := ConstantCompletion.kernelIdeal q
  let IB := ConstantCompletion.kernelIdeal p
  have hmem (U : C) (b : B.obj.obj (op U)) :
      b ∈ IB.sections U ↔
        b ∈ Ideal.map (e.hom.hom.app (op U)).hom (IR.sections U) := by
    dsimp only [IB, IR, ConstantCompletion.kernelIdeal]
    rw [(ConstantCompletion.kernelIdeal_existsUnique p).exists.choose_spec U,
      (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U,
      Ideal.mem_map_iff_of_surjective _ (ConcreteCategory.bijective_of_isIso
        (e.hom.hom.app (op U))).2]
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
        (e.hom.hom.app (op U))).2 b
      refine ⟨a, ?_, rfl⟩
      apply (ConcreteCategory.bijective_of_isIso (d.hom.hom.app (op U))).1
      have h := congrArg (fun k ↦ k.hom.app (op U) a) hq
      change p.hom.app (op U) (e.hom.hom.app (op U) a) =
        d.hom.hom.app (op U) (q.hom.app (op U) a) at h
      change p.hom.app (op U) (e.hom.hom.app (op U) a) = 0 at hb
      simpa only [map_zero] using h.symm.trans hb
    · rintro ⟨a, ha, rfl⟩
      have h := congrArg (fun k ↦ k.hom.app (op U) a) hq
      change p.hom.app (op U) (e.hom.hom.app (op U) a) =
        d.hom.hom.app (op U) (q.hom.app (op U) a) at h
      change q.hom.app (op U) a = 0 at ha
      change p.hom.app (op U) (e.hom.hom.app (op U) a) = 0
      rw [h, ha, map_zero]
  apply restrictScalars_locallyDerivedComplete_iff J R B e.hom IR IB
  intro U b
  constructor
  · intro hb
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V g _
    exact (hmem V _).mp (IB.restriction g b hb)
  · rintro ⟨W, hW, h⟩
    exact IB.local_mem U b W hW (fun V g hg ↦ (hmem V _).mpr (h V g hg))

/-- The two completed coefficient presentations give the same local completeness test.
Source: Stacks Tags 00YY, 093M and 099C
(auxiliary; not a blueprint node).

Proof: the canonical limit isomorphism commutes with the first projections by its
construction. Its inverse identifies their kernel ideals. Apply preservation and
reflection of local completeness under scalar restriction; the target-ring isomorphism
makes the image-generated ideal exactly the kernel, section by section. -/
theorem complete_iff (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    IsSfbAdicComplete X I K ↔
      ConstantCompletion.IsComplete
        (ConstantCompletion.projection (proEtaleModelTopology X) A I 0) (object X I K) := by
  let F : proEtaleRingModules X (adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod ((sfbModelRings X).obj (adicLisseCompletedRing X I)) :=
    proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  let : F.Additive := ⟨by intros; ext U x; rfl⟩
  let M := (ConstantCompletion.Q ((sfbModelRings X).obj (adicLisseCompletedRing X I))).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  apply Iff.symm
  refine complete_iso _ _ (coefficients X I).symm
    ((constants X).app (CommRingCat.of (A ⧸ I ^ (0 + 1)))).symm ?_ M
  have h := projection X I 0
  apply (cancel_epi (coefficients X I).hom).mp
  simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  change _ = _ ≫ ((constants X).app (CommRingCat.of (A ⧸ I ^ (0 + 1)))).hom ≫
    ((constants X).app (CommRingCat.of (A ⧸ I ^ (0 + 1)))).inv
  simp only [Iso.hom_inv_id, Category.comp_id]

end SfbCompletionNormalization

end AlgebraicGeometry.Scheme
