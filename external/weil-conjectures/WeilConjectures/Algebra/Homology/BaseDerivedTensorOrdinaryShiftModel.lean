/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCounitShiftSquare

/-! # Transport of the ordinary derived tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB; an explicit shift reduction
for the tensor inheritance in Tag 0DJA(1).
(blueprint: lem-pc-base-derived-tensor-ordinary-shift-model).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- The coefficient map is the transpose of the extension unit for the composite.
Source: Stacks Project, Tag 05G3; this is the proved construction already used
in BaseDerivedTensorCohomologyModel, specialized to one universe. -/
private theorem exists_tensorExtensionMap {S : Type u} {T : Type u} {U : Type u}
    [CommRing S] [CommRing T] [CommRing U] (f : S →+* T) (g : T →+* U)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ∃ φ : ((extendScalars.{_, _, u} f).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((restrictScalars.{u} g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars.{_, _, u} (g.comp f)).mapHomologicalComplex
          (.up ℤ)).obj K),
      ∀ (i : ℤ) (t : T) (k : K.X i), φ.f i (t ⊗ₜ[S,f] k) = g t ⊗ₜ[S,g.comp f] k := by
  let F := extendScalars.{_, _, u} f
  let G := extendScalars.{_, _, u} (g.comp f)
  let H := restrictScalars.{u} g
  let adj := extendRestrictScalarsAdj.{u, _, _} f
  let adj' := extendRestrictScalarsAdj.{u, _, _} (g.comp f)
  let α : 𝟭 (ModuleCat.{u} S) ⟶ G ⋙ H ⋙ restrictScalars f :=
    adj'.unit ≫ Functor.whiskerLeft G (restrictScalarsComp f g).hom
  let β : F ⟶ G ⋙ H :=
    { app := fun M ↦ (adj.homEquiv _ _).symm (α.app M)
      naturality := by
        intro M N a
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply, Functor.id_map, Functor.comp_map]
          using α.naturality a }
  refine ⟨(β.mapHomologicalComplex (.up ℤ)).app K, ?_⟩
  intro i t k
  let _ : Module S (H.obj (G.obj (K.X i))) := Module.compHom _ f
  change ((adj.homEquiv _ _).symm (α.app (K.X i))) (t ⊗ₜ[S,f] k) = _
  change (ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u, u, u} f
    (α.app (K.X i))) (t ⊗ₜ[S,f] k) = _
  erw [ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change g t • ((1 : U) ⊗ₜ[S,g.comp f] k) = _
  rw [ExtendScalars.smul_tmul, mul_one]


/-- Naturality of the derived and homology shift comparisons for scalar multiplication.
Source: Stacks Project, Tag 05SU, and naturality of the supplied shift comparisons. -/
private theorem shiftHomologyIso_smul
    (D : CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} B))
    [D.CommShift ℤ] (K L : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ) (e : L ≅ K⟦-n⟧) (j : ℤ) (a : A) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
    let δ := (H j).mapIso (D.mapIso e ≪≫ (D.commShiftIso (-n)).app K) ≪≫
      ((H 0).shiftIso (-n) j (j - n) (by omega)).app (D.obj K)
    (H j).map (D.map (a • 𝟙 L)) ≫ δ.hom =
      δ.hom ≫ (H (j - n)).map (D.map (a • 𝟙 K)) := by
  dsimp only
  have he : (a • 𝟙 L) ≫ e.hom =
      e.hom ≫ (shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (-n)).map
        (a • 𝟙 K) := by
    change (a • 𝟙 L) ≫ e.hom = e.hom ≫ (a • 𝟙 (K⟦-n⟧))
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have h1 := congrArg (fun f ↦ (DerivedCategory.homologyFunctor
    (ModuleCat.{u} B) j).map (D.map f)) he
  have h2 := congrArg (fun f ↦ (DerivedCategory.homologyFunctor
    (ModuleCat.{u} B) j).map f) ((D.commShiftIso (-n)).hom.naturality (a • 𝟙 K))
  have h3 := ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftIso
    (-n) j (j - n) (by omega)).hom.naturality (D.map (a • 𝟙 K))
  simp only [Functor.map_comp] at h1 h2
  dsimp only [Functor.comp_map] at h2 h3
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-n)).map (D.map (a • 𝟙 K))) ≫
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftIso
        (-n) j (j - n) (by omega)).app (D.obj K)).hom =
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftIso
      (-n) j (j - n) (by omega)).app (D.obj K)).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (j - n)).map
        (D.map (a • 𝟙 K)) at h3
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% h1]
  erw [reassoc_of% h2]
  exact congrArg (fun f ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
    (D.map e.hom) ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
      ((D.commShiftIso (-n)).hom.app K) ≫ f) h3

/-- Transport the derived model and its ordinary comparison over the tensor algebra.
Source: Stacks Project, Tag 06Y6 (exact derived tensor functor) and Tag 08IB
(base-change comparison). The following shift argument is an explicit
algebraic ingredient for the tensor inheritance in Tag 0DJA(1).

Proof: keep mK.derived, mK.counit and mK.universal. The coherent right Kan
shift theorem supplies integer shifts on the derived functor and shift
compatibility of its counit. Compose restriction to R, the homotopy quotient,
Qh and the derived functor into D. For each j, applying D to e and composing
with its shift comparison and the homology shift gives an isomorphism from
derived B-cohomology of L in degree j to that of K in degree j-n.
Set cohomology(j) to mK.cohomology(j-n), and compose mK.cohomologyIso with
the inverse of that shift isomorphism. Naturality for a times identity and
mK.cohomologyIso_smul prove its scalar-action equation. Use the proved ordinary
tensor associativity isomorphism for L, fixed uniquely by its pure tensor formula.
Define comparison(j) as mK.comparison(j-n) followed by the inverse ordinary
homology shift. The B-linear counit shift square and mK.comparison_eq prove
comparison_eq for L by cancellation of restriction homology and shift maps.
Construct ordinaryToLocalized by transposing the extension unit for the composite
coefficient map. Transpose comparison followed by its homology map and the
restriction homology comparison to construct localizedComparison; the adjunction
inverse identity proves localized_eq. These fill every field of mL explicitly.
At j=i+n, reindexing by j-n=i gives eT. Cancel the ordinary shift isomorphism
against its inverse to prove the displayed square. No localized shift square is
asserted. Zero complexes, n=0, nonflat coefficient maps and arbitrary e are
included: no invertibility of a comparison map and no arbitrary model witness
is used.
(blueprint: lem-pc-base-derived-tensor-ordinary-shift-model). -/
theorem exists_baseDerivedTensor_ordinary_shift_model
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧)
    (mK : BaseDerivedTensorCohomologyModel R A B K C) (i : ℤ) :
    let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    let eH := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
      (.up ℤ) (i + n)).mapIso (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} (A ⊗[R] B)) (-n) (i + n) i
        (by omega)).app (F.obj K)
    ∃ (mL : BaseDerivedTensorCohomologyModel R A B L C)
      (eT : mL.cohomology (i + n) ≅ mK.cohomology i),
      mL.comparison (i + n) ≫ eH.hom = eT.hom ≫ mK.comparison i  := by
  classical
  let : mK.derived.IsLeftDerivedFunctor mK.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) := mK.universal
  obtain ⟨hshift, hcounit⟩ := Functor.rightKanExtension_coherentShift
    ((extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh mK.derived mK.counit
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
  let : mK.derived.CommShift ℤ := hshift
  let : NatTrans.CommShift mK.counit ℤ := hcounit
  let D := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
    HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh ⋙ mK.derived
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
  let δ (j : ℤ) := (H j).mapIso (D.mapIso e ≪≫ (D.commShiftIso (-n)).app K) ≪≫
    ((H 0).shiftIso (-n) j (j - n) (by omega)).app (D.obj K)
  let cohomology := fun j : ℤ ↦ mK.cohomology (j - n)
  let cohomologyIso := fun j : ℤ ↦ mK.cohomologyIso (j - n) ≪≫ (δ j).symm
  let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let ε (j : ℤ) := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
    (.up ℤ) j).mapIso (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} (A ⊗[R] B)) (-n) j (j - n)
      (by omega)).app (F.obj K)
  let comparison := fun j : ℤ ↦ mK.comparison (j - n) ≫ (ε j).inv
  obtain ⟨ordinaryIso, ordinaryIso_tmul⟩ := exists_baseTensorOrdinaryIso R A B L
  obtain ⟨ordinaryToLocalized, ordinaryToLocalized_tmul⟩ := exists_tensorExtensionMap
    (algebraMap A (A ⊗[R] B)) (algebraMap (A ⊗[R] B) C) L
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let localizedComparison := fun j : ℤ ↦ (adj.homEquiv _ _).symm
    (comparison j ≫ HomologicalComplex.homologyMap ordinaryToLocalized j ≫
      ((((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) C).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj L).sc j
          |>.mapHomologyIso (restrictScalars.{u} (algebraMap (A ⊗[R] B) C))).hom)
  let mL : BaseDerivedTensorCohomologyModel R A B L C := {
    derived := mK.derived
    counit := mK.counit
    universal := mK.universal
    ordinaryIso := ordinaryIso
    ordinaryIso_tmul := ordinaryIso_tmul
    cohomology := cohomology
    cohomologyIso := cohomologyIso
    cohomologyIso_smul := by
      intro j a
      have hδ := shiftHomologyIso_smul A B D K L n e j a
      apply (cancel_mono (δ j).hom).mp
      dsimp only [cohomologyIso, Iso.trans_hom, Iso.symm_hom]
      change (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
          𝟙 (mK.cohomology (j - n))) ≫
            (mK.cohomologyIso (j - n)).hom ≫ (δ j).inv ≫ (δ j).hom =
        (mK.cohomologyIso (j - n)).hom ≫ (δ j).inv ≫
          (H j).map (D.map (a • 𝟙 L)) ≫ (δ j).hom
      change (H j).map (D.map (a • 𝟙 L)) ≫ (δ j).hom =
        (δ j).hom ≫ (H (j - n)).map (D.map (a • 𝟙 K)) at hδ
      rw [hδ]
      simp only [Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
      exact mK.cohomologyIso_smul (j - n) a
    comparison := comparison
    comparison_eq := by
      intro j
      let S := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
      let G := (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)
      let U := restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
      let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
      let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
      let μK := ((F.obj K).sc (j - n)).mapHomologyIso U
      let μL := ((F.obj L).sc j).mapHomologyIso U
      let cK := (H (j - n)).map (mK.counit.app (πR.obj (S.obj K))) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) (j - n)).hom.app
          (πB.obj (G.obj (S.obj K))) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) (j - n)).hom.app
          (G.obj (S.obj K)) ≫ HomologicalComplex.homologyMap mK.ordinaryIso.hom (j - n) ≫
        μK.hom
      let cL := (H j).map (mK.counit.app (πR.obj (S.obj L))) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) j).hom.app
          (πB.obj (G.obj (S.obj L))) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) j).hom.app
          (G.obj (S.obj L)) ≫ HomologicalComplex.homologyMap ordinaryIso.hom j ≫ μL.hom
      have hs := baseDerivedTensor_counit_shift_square R A B mK.derived mK.counit
        K L n e j mK.ordinaryIso mK.ordinaryIso_tmul ordinaryIso ordinaryIso_tmul
      change (δ j).hom ≫ cK = cL ≫ U.map (ε j).hom at hs
      have hk : U.map (mK.comparison (j - n)) =
          (mK.cohomologyIso (j - n)).hom ≫ cK := by
        have h := congrArg (fun f ↦ f ≫ μK.hom) (mK.comparison_eq (j - n))
        simp only [Category.assoc] at h
        change U.map (mK.comparison (j - n)) ≫ μK.inv ≫ μK.hom =
          (mK.cohomologyIso (j - n)).hom ≫ cK at h
        simpa only [Iso.inv_hom_id, Category.comp_id] using h
      apply (cancel_mono μL.hom).mp
      apply (cancel_mono (U.map (ε j).hom)).mp
      change (U.map (mK.comparison (j - n) ≫ (ε j).inv) ≫ μL.inv) ≫ μL.hom ≫
          U.map (ε j).hom =
        (mK.cohomologyIso (j - n)).hom ≫ (δ j).inv ≫ cL ≫ U.map (ε j).hom
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← hs]
      simp only [Iso.inv_hom_id_assoc]
      rw [← U.map_comp, Iso.inv_hom_id, U.map_id, Category.comp_id]
      exact hk
    ordinaryToLocalized := ordinaryToLocalized
    ordinaryToLocalized_tmul := ordinaryToLocalized_tmul
    localizedComparison := localizedComparison
    localized_eq := fun j ↦ (adj.homEquiv _ _).apply_symm_apply _ }
  have reindex (j k : ℤ) (h : j - n = k) :
      (mK.comparison (j - n) ≫ (ε j).inv) ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) j).mapIso
          (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
          (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} (A ⊗[R] B))
            (-n) j k (by omega)).app (F.obj K)).hom =
        eqToHom (congrArg mK.cohomology h) ≫ mK.comparison k := by
    subst k
    change (mK.comparison (j - n) ≫ (ε j).inv) ≫ (ε j).hom =
      𝟙 _ ≫ mK.comparison (j - n)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hi : i + n - n = i := by omega
  let eT : mL.cohomology (i + n) ≅ mK.cohomology i :=
    eqToIso (congrArg mK.cohomology hi)
  refine ⟨mL, eT, ?_⟩
  exact reindex (i + n) i hi

end ModuleCat
