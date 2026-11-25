/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedFactorization
import WeilConjectures.AlgebraicGeometry.FiniteScalarRightAdjointQCoh

/-! # FiniteAffineAdjointCounitComparison

Source: Stacks Project, Duality for Schemes, Section 48.11.
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem iso_of_bijective_on_image
    {C A : Type*} [Category* C] [Category* A] (T : C ⥤ A)
    (V : C) {B : A} (g : T.obj V ⟶ B)
    (hg : ∀ N : C, Function.Bijective (fun h : T.obj N ⟶ T.obj V ↦ h ≫ g))
    (N : C) (e : T.obj N ≅ B) : IsIso g := by
  obtain ⟨v, hv⟩ := (hg N).surjective e.hom
  change v ≫ g = e.hom at hv
  let t : B ⟶ T.obj V := e.inv ≫ v
  have ht : t ≫ g = 𝟙 B := by
    dsimp [t]
    rw [Category.assoc, hv, e.inv_hom_id]
  have hgt : g ≫ t = 𝟙 (T.obj V) := by
    apply (hg V).injective
    simp only [Category.assoc, ht, Category.comp_id, Category.id_comp]
  exact ⟨⟨t, hgt, ht⟩⟩

private theorem pointwise_adjoint_comparison
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    (T : C ⥤ A) (I : D ⥤ B) (L : A ⥤ B)
    (R : C ⥤ D) (a : D ⥤ C) (adj : R ⊣ a)
    (H : B ⥤ A) (adjA : L ⊣ H)
    (hT : T.FullyFaithful) (hI : I.FullyFaithful)
    (β : R ⋙ I ≅ T ⋙ L) (K : D) (N : C) (e : T.obj N ≅ H.obj (I.obj K)) :
    ∃ φ : T.obj (a.obj K) ≅ H.obj (I.obj K),
      L.map φ.hom ≫ adjA.counit.app (I.obj K) =
        β.inv.app (a.obj K) ≫ I.map (adj.counit.app K) := by
  let u := β.inv.app (a.obj K) ≫ I.map (adj.counit.app K)
  let g := (adjA.homEquiv _ _) u
  have hg : L.map g ≫ adjA.counit.app (I.obj K) = u := by
    exact (adjA.homEquiv _ _).symm_apply_apply u
  have hb (M : C) : Function.Bijective
      (fun h : T.obj M ⟶ T.obj (a.obj K) ↦ h ≫ g) := by
    let q : (T.obj M ⟶ T.obj (a.obj K)) ≃ (L.obj (T.obj M) ⟶ I.obj K) :=
      hT.homEquiv.symm |>.trans ((adj.homEquiv M K).symm) |>.trans
        hI.homEquiv |>.trans ((β.app M).homFromEquiv)
    have hq (h : T.obj M ⟶ T.obj (a.obj K)) :
        q h = (adjA.homEquiv _ _).symm (h ≫ g) := by
      obtain ⟨j, rfl⟩ := hT.map_surjective h
      change β.inv.app M ≫ I.map (R.map (hT.preimage (T.map j)) ≫
          adj.counit.app K) = L.map (T.map j ≫ g) ≫ adjA.counit.app (I.obj K)
      simp only [hT.preimage_map, Functor.map_comp, Category.assoc, hg]
      dsimp [u]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun z ↦ z ≫ I.map (adj.counit.app K)) (β.inv.naturality j).symm
    have heq : (fun h : T.obj M ⟶ T.obj (a.obj K) ↦ h ≫ g) =
        fun h ↦ (adjA.homEquiv _ _) (q h) := by
      funext h
      rw [hq]
      exact ((adjA.homEquiv _ _).apply_symm_apply (h ≫ g)).symm
    rw [heq]
    exact (adjA.homEquiv _ _).bijective.comp q.bijective
  have := iso_of_bijective_on_image T (a.obj K) g hb N e
  exact ⟨asIso g, hg⟩

/-- The finite affine comparison of geometric and scalar right adjoints at a
bounded-below quasi-coherent object. No identification with internal Hom or evaluation
at one is asserted here. The boundedness of a(K) is an explicit input.

Source: Stacks Project, Tag 0AX2, comparison-of-right-adjoints paragraph; Tag 0AVW
(blueprint: lem-sc-finite-affine-adjoint-counit-comparison).

Proof:
1. Scalar restriction is exact. On a K-injective representative, Rg_* followed by
   scalar restriction and Rf_* are the same pushforward complex, with different
   scalar structures. Descend this identity to the natural isomorphism c, on the
   whole derived category, keeping the localization comparison maps.
2. Use finite_affine_derived_equivalence to identify D_QCoh(X) with D_QCoh(A).
   The given adjunction R ⊣ a transports to the restriction functor under this
   equivalence; its counit is comparison.inv followed by adj.counit.
3. The affine sheaf-Hom adjunction computes the ambient scalar right adjoint.
   Finite pseudo-coherence and the internal-Hom quasi-coherence lemma put its value
   on K in D+_QCoh(A); uniqueness transports this assertion to the specified rhoR.
   Exact scalar restriction detects vanishing of cohomology. The affine cohomology
   formula therefore makes E preserve lower bounds; its inverse is exact on
   quasi-coherent modules and preserves them too. Thus haK bounds E(a(K)).
4. For this fixed K, both E(a(K)) and rhoR(K) represent the same contravariant
   functor M -> Hom(rho(M),K) on D+_QCoh(A), by the two given adjunctions and the
   equivalence. Pointwise uniqueness of representing objects (Yoneda) gives phi,
   transported through the Rg_* comparison. Its counit equation is the pointwise
   right-adjoint uniqueness equation. No global preservation claim for a is needed.
   The choice of comparison is used to transport the adjunction, so this also works
   for arbitrary specified comparison and adjunction, including their automorphisms.
All statements hold for the zero object and for shifts, with shifted lower bounds. -/
theorem finite_affine_adjoint_counit_comparison {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : R ⊣ a)
    (ρR : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
    (adjA : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ ρR)
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ c : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ≅
        schemeDerivedDirectImage f,
    ∃ φ : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        (a.obj K).obj ≅ ρR.obj K.obj,
      (c.app (a.obj K).obj).inv ≫
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.map
            φ.hom ≫ adjA.counit.app K.obj =
        comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom := by
  obtain ⟨c⟩ := finite_affine_derived_factorization.{u, wX, wY, wA} f
  obtain ⟨E, ⟨eE⟩, _⟩ := finite_affine_derived_equivalence.{u, wX, wY, wA} f
  let G := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let T := (schemeDerivedQCohProperty X).ι ⋙ G
  let ρ := (SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor
  let β : R ⋙ (schemeDerivedQCohProperty Y).ι ≅ T ⋙ ρ :=
    comparison ≪≫ Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι c.symm ≪≫
      (Functor.associator (schemeDerivedQCohProperty X).ι G ρ).symm
  let B : directImageAlgebraDerivedQCohCategory f :=
    ⟨ρR.obj K.obj, finite_scalar_right_adjoint_qcoh f ρR adjA K hK⟩
  let N := E.inverse.obj B
  let e : T.obj N ≅ ρR.obj K.obj :=
    (eE.app N).symm ≪≫
      (directImageAlgebraDerivedQCohProperty f).ι.mapIso (E.counitIso.app B)
  have hT : T.FullyFaithful :=
    (E.fullyFaithfulFunctor.comp
      (directImageAlgebraDerivedQCohProperty f).fullyFaithfulι).ofIso eE
  obtain ⟨φ, hφ⟩ := pointwise_adjoint_comparison T
    (schemeDerivedQCohProperty Y).ι ρ R a adj ρR adjA hT
    (schemeDerivedQCohProperty Y).fullyFaithfulι β K N e
  refine ⟨c, φ, ?_⟩
  have hβ : β.inv.app (a.obj K) =
      (c.app (a.obj K).obj).hom ≫ comparison.inv.app (a.obj K) := by
    dsimp [β, Functor.associator, Functor.isoWhiskerLeft]
    erw [Category.id_comp]
  rw [hβ] at hφ
  simp only [Category.assoc] at hφ
  change (c.app (a.obj K).obj).inv ≫ ρ.map φ.hom ≫ adjA.counit.app K.obj = _
  erw [hφ, (c.app (a.obj K).obj).inv_hom_id_assoc]
  rfl

end AlgebraicGeometry
