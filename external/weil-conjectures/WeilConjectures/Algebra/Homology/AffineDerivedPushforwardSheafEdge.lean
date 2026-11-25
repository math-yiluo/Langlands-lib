/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalization
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # The affine derived edge before choosing module coordinates

Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

private theorem map_map_quotientCompQhIso_hom {A E E' : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* E] [Category* E']
    (G : DerivedCategory A ⥤ E) (H : E ⥤ E')
    (K : CochainComplex A ℤ) :
    H.map (G.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) =
      𝟙 (H.obj (G.obj (DerivedCategory.Q.obj K))) := by
  change H.map (G.map (𝟙 (DerivedCategory.Q.obj K))) = _
  rw [G.map_id, H.map_id]

private theorem map_quotientCompQhIso_inv {A E : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* E] (G : DerivedCategory A ⥤ E)
    (K : CochainComplex A ℤ) :
    G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) =
      𝟙 (G.obj (DerivedCategory.Q.obj K)) := by
  change G.map (𝟙 (DerivedCategory.Q.obj K)) = _
  exact G.map_id _

private theorem map_map_quotientCompQhIso_hom_comp {A E E' : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* E] [Category* E']
    (G : DerivedCategory A ⥤ E) (H : E ⥤ E')
    (K : CochainComplex A ℤ) {Z : E'}
    (f : H.obj (G.obj (DerivedCategory.Q.obj K)) ⟶ Z) :
    H.map (G.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫ f = f := by
  change H.map (G.map (𝟙 (DerivedCategory.Q.obj K))) ≫ f = f
  rw [G.map_id, H.map_id, Category.id_comp]

private theorem map_quotientCompQhIso_inv_comp {A E : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* E] (G : DerivedCategory A ⥤ E)
    (K : CochainComplex A ℤ) {Z : E}
    (f : G.obj (DerivedCategory.Q.obj K) ⟶ Z) :
    G.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫ f = f := by
  change G.map (𝟙 (DerivedCategory.Q.obj K)) ≫ f = f
  rw [G.map_id, Category.id_comp]

/-- Affine direct image is acyclic on quasi-coherent modules.
Source: Stacks, Tags 01EO and 01XJ; the Čech dimension-shifting argument of
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism.
The proof is kept here because that module's finite-complex import reaches
this module in the current library. -/
private theorem affineDirectImage_rightAcyclic {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [HasInjectiveResolutions X.Modules]
    (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pushforward f).rightAcyclic M := by
  let P := Scheme.Modules.pushforward f
  have : PreservesFiniteLimits P := by
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    infer_instance
  apply Functor.rightAcyclic_of_epi_map_g P
    (fun N ↦ Scheme.Modules.cechAcyclicOnAffines X ((Scheme.Modules.toAb X).obj N))
  · intro I _
    have := Scheme.Modules.isFlasque_of_injective I
    exact fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _
  · intro T hT h₁ h₂
    exact Scheme.Modules.cechAcyclicOnAffines_X₃
      (S := T.map (Scheme.Modules.toAb X))
      (hT.map_of_exact (Scheme.Modules.toAb X)) h₁ h₂
  · intro T hT h₁
    refine Scheme.Modules.epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
    obtain ⟨z, hz⟩ := Scheme.Modules.surjective_app_of_cechAcyclicOnAffines
      (hT.map_of_exact (Scheme.Modules.toAb X)) h₁ (hV.preimage f)
      (T.X₃.presheaf.map (homOfLE (f.preimage_mono hVW)).op y)
    exact ⟨V, hVW, hxV, z, hz⟩
  · exact Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent M

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local irreducible] RingedSpace.moduleDirectImage

/-- The sheaf-level affine edge is compatible with the actual derived unit on an
exact family of quasi-coherent sheaves. No tilde/Gamma coordinates or ordinary
comparison isomorphism occur here.
Source: Stacks Project, Tag 0AVW, proof of lemma-affine-morphism-equivalence,
and Tag 08D4, lemma-application-nice-K-injective with bound one.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge).

Proof: On the inverse image of an affine open, higher cohomology of a
quasi-coherent module vanishes. Apply the bound-one truncation calculation of
08D4 to a K-injective resolution, in degree i. Its cycle-class comparison
identifies cohomology of derived sections with sections of the cohomology
sheaf. These comparisons commute with restrictions and derived morphisms;
sheafifying them gives the edge f_*H^i -> H^i Rf_* on D_QCoh. For an exact
functor F with quasi-coherent values, compare the complex F(C) with its
K-injective resolution. The comparison from termwise pushforward is the
right-derived unit. Exactness of F and f_*F identifies its source cohomology
with F(H^i C) and f_*F(H^i C), respectively. On cycles both resulting arrows
send the same section to its class in the resolution; the cokernel universal
property proves the displayed equality. Restriction-compatible equality on
the affine basis proves equality of sheaf morphisms. This applies to unbounded
C by 08D4; neither the zero ring nor zero complexes need to be excluded. -/
theorem exists_affineDerivedPushforwardSheafEdge
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  ∃ ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (F : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
      (_hF : ∀ M, (F.obj M).IsQuasicoherent)
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))),
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        ε.app ⟨_, hC⟩ =
      ((C.sc i).mapHomologyIso
        (F ⋙ RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((F ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
              |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
        (cast (by rfl)
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
            (((RingedSpace.moduleDirectImage
              (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj
                ((F.mapHomologicalComplex (.up ℤ)).obj C))))) := by
  let X := Spec (.of A)
  let Y := Spec (.of B)
  let f := Spec.map (CommRingCat.ofHom φ)
  let S := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let ι := (schemeDerivedQCohProperty X).ι
  let H := DerivedCategory.homologyFunctor D i
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : PreservesFiniteLimits S := by
    let U := SheafOfModules.forget (moduleRings Y.toRingedSpace)
    let V := PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj
    have : PreservesFiniteLimits (S ⋙ U ⋙ V) := by
      dsimp only [S]
      unfold RingedSpace.moduleDirectImage
      change PreservesFiniteLimits
        ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
          PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map f.base).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves S (U ⋙ V)
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have hacyc : ∀ (M : C), M.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
      IsZero ((schemeModuleHigherDirectImage f p).obj M) := by
    intro M hM p hp
    have := hM
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) := ⟨p.toNat, by omega⟩
    have hm : 0 < m := by omega
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 1 := ⟨m - 1, by omega⟩
    have hz := affineDirectImage_rightAcyclic f M q
    have hzS : IsZero ((S.rightDerived (q + 1)).obj M) := by
      dsimp only [S]
      unfold RingedSpace.moduleDirectImage
      exact hz
    exact hzS.of_iso (Functor.homologyRightDerivedFunctorObjSingleFunctorIso S M (q + 1))
  obtain ⟨e⟩ := qcoh_acyclic_derived_pushforward_cohomology f hacyc i
  let γ := Functor.whiskerLeft ι
    (Functor.whiskerRight (Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncGEπ i) S.rightDerivedFunctor) H)
  have (E : schemeDerivedQCohCategory X) : IsIso (γ.app E) := by
    let E' := (DerivedCategory.TStructure.t.truncGE i).obj E.obj
    let Q := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
    have hzero : IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
        PEmpty.{u + 1}) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (SheafOfModules.freeHomEquiv _).injective
      funext j
      exact PEmpty.elim j
    have : Q.ContainsZero :=
      ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
    have hE' : schemeDerivedQCohProperty X E' :=
      DerivedCategory.homologyProperty_truncGE E.property i
    let v : E ⟶ (⟨E', hE'⟩ : schemeDerivedQCohCategory X) :=
      (schemeDerivedQCohProperty X).homMk
        ((DerivedCategory.TStructure.t.truncGEπ i).app E.obj)
    have : IsIso (((schemeDerivedQCohProperty X).ι ⋙
        DerivedCategory.homologyFunctor C i ⋙ S).map v) := by
      change IsIso (S.map ((DerivedCategory.homologyFunctor C i).map
        ((DerivedCategory.TStructure.t.truncGEπ i).app E.obj)))
      have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E.obj i i le_rfl
      infer_instance
    exact (NatIso.isIso_map_iff e v).mpr this
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  obtain ⟨δ, hδ⟩ := S.exists_rightDerivedFunctor_truncated_bottom_unit i
  let ε := (Functor.isoWhiskerLeft ι δ).inv ≫ (asIso γ).inv
  refine ⟨ε, ?_⟩
  intro F _ _ _ _ _ _hF M hM
  let K := (F.mapHomologicalComplex (.up ℤ)).obj M
  let T := (M.sc i).homologyData.left.map F
  let U := (M.sc i).homologyData.left.map (F ⋙ S)
  have hn := hδ K T U (𝟙 _) (by
    simp only [T, U, ShortComplex.LeftHomologyData.map_i, Functor.comp_map,
      Category.id_comp])
  simp only [Category.id_comp] at hn
  have hepi : Epi ((F ⋙ S).map (M.sc i).homologyData.left.π) := by
    change Epi U.π
    infer_instance
  simp only [Functor.map_comp] at hn
  simp only [Category.assoc, map_map_quotientCompQhIso_hom_comp,
    map_quotientCompQhIso_inv_comp] at hn
  apply (cancel_epi ((F ⋙ S).map (M.sc i).homologyData.left.π)).mp
  apply (cancel_mono (γ.app ⟨_, hM⟩ ≫ δ.hom.app (DerivedCategory.Q.obj K))).mp
  simpa only [ε, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, asIso_inv, NatIso.isIso_inv_app, Category.assoc,
    IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app, Category.comp_id,
    γ, S, T, U, K, ι, H, f, X, Y, C, D, Functor.whiskerRight_app, ObjectProperty.ι_obj,
    ShortComplex.LeftHomologyData.map_π, ShortComplex.mapHomologyIso,
    Functor.comp_map, Functor.map_comp, Functor.mapHomologicalComplex, Functor.comp_obj,
    cast_eq]
    using hn.symm

end AlgebraicGeometry
