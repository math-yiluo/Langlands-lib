/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechPresheafDegreeZeroIdentity

/-! # Local alternating Čech cancellation

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every degree-zero endomorphism killed by the first differential factors
through the local augmentation.
Source: Stacks Project, Tag 02FU, exactness at the first Čech term;
Tag 01FM for the ordered alternating convention.
(blueprint: lem-pc-s3-alternating-cech-sheaf-degree-zero-factorization).

Proof: A degree-zero cocycle is a family of sections on the singleton
intersections whose restrictions agree on pairwise intersections. On a test open
V contained in U i, take its i coordinate, which is a section of G(V).
The pairwise agreement with that coordinate shows that its augmentation recovers
every coordinate of the cocycle. The projection is linear and natural in V.
After sheafification, work locally where a section of the sheafified finite
product is represented by presheaf sections. The vanishing differential becomes
local pairwise agreement; taking the i coordinate then gives local sections of
G, and uniqueness glues them. Thus the augmentation identifies G with the
kernel of the first differential on U i. Transport this kernel property through
integer extension and restriction. Apply its universal property to the given
endomorphism f killed by the differential to obtain π, with π ≫ a.f 0 = f.
Empty opens have zero modules, r=0 has no i, and for r=1 the augmentation is
an isomorphism while the first differential has zero target.
-/
theorem alternatingCechSheafAugmentation_restrict_degreeZero_factorization
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∀ f : C.X 0 ⟶ C.X 0, f ≫ C.d 0 1 = 0 →
      ∃ π : C.X 0 ⟶ A.X 0, π ≫ a.f 0 = f := by
  classical
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let : L.Additive := adj.left_adjoint_additive
  let : F.Additive := ⟨by intro A B f g; ext V; rfl⟩
  let T := L ⋙ F
  let : T.Additive := inferInstanceAs (L ⋙ F).Additive
  let K := cechCapPresheafFunctor (U i)
  let ν := cechCapPresheafUnit (U i)
  let P₀ := alternatingCechSheafPresheafTerms U G 0
  let z := alternatingCechSheafPresheafZero U G
  let d := alternatingCechSheafPresheafD U G 0
  let η : G ⟶ L.obj G.val := (SheafOfModules.fullyFaithfulForget _).preimage
    (adj.unit.app G.val)
  have hη : η ≫ adj.counit.app G = 𝟙 G := by
    apply (SheafOfModules.forget _).map_injective
    change adj.unit.app G.val ≫ (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (adj.counit.app G) = 𝟙 _
    exact adj.right_triangle_components G
  have : IsIso η := by
    have : η = inv (adj.counit.app G) := by
      rw [← cancel_mono (adj.counit.app G), hη, IsIso.inv_hom_id]
    rw [this]
    infer_instance
  have : IsIso (T.map (ν.app P₀)) := cechCapPresheafUnit_local_isIso (U i) P₀
  have : IsIso (T.map (ν.app G.val)) := cechCapPresheafUnit_local_isIso (U i) G.val
  obtain ⟨p, h, hp⟩ := alternatingCechSheafPresheaf_degreeZero_identity U G i
  change ν.app P₀ = d ≫ h + p ≫ K.map z at hp
  have hn : T.map z ≫ T.map (ν.app P₀) =
      T.map (ν.app G.val) ≫ T.map (K.map z) := by
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg T.map (ν.naturality z)
  have hlocal (f : T.obj P₀ ⟶ T.obj P₀) (hf : f ≫ T.map d = 0) :
      ∃ q : T.obj P₀ ⟶ F.obj G,
        q ≫ F.map ((alternatingCechSheafAugmentation U G).f 0) = f := by
    refine ⟨f ≫ T.map p ≫ inv (T.map (ν.app G.val)) ≫ inv (F.map η), ?_⟩
    change (f ≫ T.map p ≫ inv (T.map (ν.app G.val)) ≫ inv (F.map η)) ≫
      F.map (η ≫ L.map z) = f
    rw [F.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    apply (cancel_mono (T.map (ν.app P₀))).mp
    simp only [Category.assoc]
    change f ≫ T.map p ≫ inv (T.map (ν.app G.val)) ≫
      T.map z ≫ T.map (ν.app P₀) = f ≫ T.map (ν.app P₀)
    rw [hn, IsIso.inv_hom_id_assoc]
    rw [hp, T.map_add, T.map_comp, T.map_comp, Preadditive.comp_add]
    simp only [← Category.assoc, hf, Limits.zero_comp, zero_add]
  let S := (CochainComplex.single₀ X.Modules).obj G
  let B := alternatingCechSheafComplex U G
  let eS := S.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl
  let eB := B.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl
  let eB₁ := B.extendXIso ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl
  intro f hf
  let f' := F.map eB.inv ≫ f ≫ F.map eB.hom
  have hf' : f' ≫ T.map d = 0 := by
    change (F.map eB.inv ≫ f ≫ F.map eB.hom) ≫ F.map (B.d 0 1) = 0
    have he : (B.extend ComplexShape.embeddingUpNat).d 0 1 =
        eB.hom ≫ B.d 0 1 ≫ eB₁.inv := by
      exact B.extend_d_eq ComplexShape.embeddingUpNat rfl rfl
    change f ≫ F.map ((B.extend ComplexShape.embeddingUpNat).d 0 1) = 0 at hf
    rw [he, F.map_comp, F.map_comp] at hf
    have hz := congrArg (fun t ↦ F.map eB.inv ≫ t ≫ F.map eB₁.hom) hf
    simpa only [Category.assoc, ← F.map_comp, Iso.inv_hom_id,
      F.map_id, Category.comp_id, Limits.comp_zero, Limits.zero_comp] using hz
  obtain ⟨q, hq⟩ := hlocal f' hf'
  refine ⟨F.map eB.hom ≫ q ≫ F.map eS.inv, ?_⟩
  change (F.map eB.hom ≫ q ≫ F.map eS.inv) ≫
    F.map ((HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
      ComplexShape.embeddingUpNat).f 0) = f
  rw [HomologicalComplex.extendMap_f (alternatingCechSheafAugmentation U G)
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl]
  change (F.map eB.hom ≫ q ≫ F.map eS.inv) ≫
    F.map (eS.hom ≫ (alternatingCechSheafAugmentation U G).f 0 ≫ eB.inv) = f
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc eS.inv, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← Category.assoc q, hq]
  dsimp only [f']
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  simp only [← F.map_comp, Iso.hom_inv_id, F.map_id]
  exact Category.comp_id f

end AlgebraicGeometry
