/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison

/-! # AffineBaseChangeTildeCanonicalGlobalComparison

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-canonical-global-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

private theorem tensorAlgebraMap_isIso
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ)
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    IsIso (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D)) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D))
  have ha : a ≫ (pullbackSpecIso R A B).inv = sq.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSpecIso_inv_fst', IsPullback.isoPullback_hom_fst]
      change Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) = _
      rw [← Spec.map_comp]
      exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q)) hφ
    · simp only [Category.assoc, pullbackSpecIso_inv_snd, IsPullback.isoPullback_hom_snd]
      change Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D)) ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
      rw [← Spec.map_comp]
      exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q)) hψ
  have : IsIso (a ≫ (pullbackSpecIso R A B).inv) := by rw [ha]; infer_instance
  have : IsIso a := IsIso.of_isIso_comp_right _ (pullbackSpecIso R A B).inv
  have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D)).op) := this
  have := isIso_of_reflects_iso
    (CommRingCat.ofHom (algebraMap (A ⊗[R] B) D)).op Scheme.Spec
  exact (isIso_op_iff _).mp this

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Affine mate calculation for the fixed module-derived tensor construction.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof and equation-bc;
more-algebra.tex, Tag 06Y6; perfect.tex, Tag 08IB.
(blueprint: lem-pc-affine-base-change-tilde-canonical-global-comparison).

Proof: unfold the fixed tensor model, whose functor is constructed by an R-K-flat
resolution and extension of scalars. Affine higher-direct-image vanishing, with
unbounded cohomological bound one, identifies derived direct-image cohomology
naturally with ordinary direct image of cohomology. Compose with the tilde/Gamma
counit and restriction-of-scalars comparison to obtain d. Exact tilde identifies
the cohomology of the scalar-extended resolution with the associated sheaf of
its module cohomology. The cartesian tensor-algebra isomorphism transports it to
A', giving eU. On this fixed resolution the scheme mate is the scalar extension
of the augmentation to the restricted A-complex, by the tensor-pullback unit
formula. Its homology is the fixed model's comparison. The localized comparison
is its adjoint after extension to A'. The inverse pullback counit and e give the
target coordinate b. Applying homology to the mate equation gives the square.
There is no comparison of two arbitrary derived functors or tensor actions in
this statement; that is the separate model-independence lemma. Zero rings and
zero complexes obey the same construction; no boundedness is used. -/
theorem exists_affineBaseChangeTildeCanonicalGlobalComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    :
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let a := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b
    ∃ eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L := by
  let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
  let α := algebraMap (A ⊗[R] R') A'
  let j : R' →+* A ⊗[R] R' := Algebra.TensorProduct.includeRight.toRingHom
  let r := ModuleCat.restrictScalars φf'
  let s := ModuleCat.restrictScalars j
  let T := tilde.functor (.of R')
  let ρ := ModuleCat.restrictScalarsComp' j α φf' hφf'.symm
  let η := (ModuleCat.extendRestrictScalarsAdj α).unit.app (m.cohomology i)
  have hα : IsIso (CommRingCat.ofHom α) :=
    tensorAlgebraMap_isIso R A R' A' φg' φf' hφg' hφf' sq
  let ε : (A ⊗[R] R') ≃+* A' :=
    (asIso (CommRingCat.ofHom α)).commRingCatIsoToRingEquiv
  have : (ModuleCat.restrictScalars α).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv ε
  have : IsIso η := inferInstance
  let U := affineBaseChangeTildeModule R A R' A' M m i
  let t : s.obj (m.cohomology i) ⟶ r.obj U := s.map η ≫ ρ.inv.app U
  have : IsIso t := by dsimp only [t]; infer_instance
  obtain ⟨d, eC, heC⟩ := exists_affineBaseChangeTildeOrdinaryComparison
    R A R' A' φg' φf' hφg' hφf' sq.w K hK hL M hM e hc i
  let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
  let V := (affineDerivedCohomologyModules A' i).obj L
  let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
  let a := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b
  let C := (((ModuleCat.extendScalars (α.comp
    (algebraMap A (A ⊗[R] R')))).mapHomologicalComplex (.up ℤ)).obj M)
  let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
    ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
  let z := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A') (.up ℤ) i).map
    (eqToHom (by dsimp only [C, α]; rw [hφg'] : C =
      ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M)) ≫ b.hom
  let c := s.map cE ≫ ρ.inv.app (C.homology i) ≫ r.map z
  have htc : t ≫ r.map a = c := by
    have hn := ρ.inv.naturality (m.localizedComparison i)
    change s.map ((ModuleCat.restrictScalars α).map (m.localizedComparison i)) ≫
        ρ.inv.app (C.homology i) = ρ.inv.app U ≫ r.map (m.localizedComparison i) at hn
    calc
      t ≫ r.map a = s.map η ≫
          (ρ.inv.app U ≫ r.map (m.localizedComparison i)) ≫ r.map z := by
        simp only [t, a, affineBaseChangeTildeModuleMap, z,
          Functor.map_comp, Category.assoc]
      _ = s.map η ≫ (s.map ((ModuleCat.restrictScalars α).map
          (m.localizedComparison i)) ≫ ρ.inv.app (C.homology i)) ≫ r.map z := by rw [← hn]
      _ = s.map (η ≫ (ModuleCat.restrictScalars α).map (m.localizedComparison i)) ≫
          ρ.inv.app (C.homology i) ≫ r.map z := by
        simp only [Functor.map_comp, Category.assoc]
      _ = c := by rw [show η ≫ _ = cE from m.localized_eq i]
  change eC.hom ≫ _ = T.map c ≫ d.hom.app L at heC
  refine ⟨d, T.mapIso (asIso t).symm ≪≫ eC, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv]
  change T.map (inv t) ≫ eC.hom ≫ _ = T.map (r.map a) ≫ d.hom.app L
  rw [heC, ← Category.assoc, ← T.map_comp, ← htc]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]


end AlgebraicGeometry
