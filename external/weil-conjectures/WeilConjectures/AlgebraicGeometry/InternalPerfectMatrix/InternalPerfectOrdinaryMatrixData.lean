/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.AlgebraicGeometry.LocallyConstantModuleHomology
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantSections
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.LinearAlgebra.Dimension.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularExtensionComposition
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelOrdinaryScalar
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Explicit finite-matrix evaluation for ordinary perfect reductions

All choices here are taken from proved finite-basis and finite-coefficient
equivalences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Integral scalar ring. -/
abbrev A := Padic.coefficientExtensionIntegers l E

/-- Locally constant scalar modules in the universe of internal morphisms. -/
def sections (W : Scheme.{u}) : ModuleCat.{u} (A l E) ⥤ AddCommGrpCat.{u + 1} :=
  locallyConstantModuleFunctor (ConnectedComponents W) (A l E) ⋙
    ModuleCat.uliftFunctor.{u + 1, u} (A l E) ⋙
      forget₂ (ModuleCat.{u + 1} (A l E)) AddCommGrpCat.{u + 1}

instance sections_additive (W : Scheme.{u}) : (sections l E W).Additive := by
  dsimp only [sections]
  infer_instance

instance sections_preservesHomology (W : Scheme.{u}) :
    (sections l E W).PreservesHomology := by
  classical
  apply CategoryTheory.Functor.preservesHomology_of_map_exact
  intro S hS
  apply (ShortComplex.ab_exact_iff _).2
  intro y hy
  change ULift.{u + 1} (LocallyConstant (ConnectedComponents W) S.X₂) at y
  change ULift.up (LocallyConstant.map S.g y.down) = 0 at hy
  have hy' : LocallyConstant.map S.g y.down = 0 := congrArg ULift.down hy
  have hex := (ShortComplex.moduleCat_exact_iff S).1 hS
  let k : S.X₂ → S.X₁ := fun z ↦ if h : S.g z = 0 then (hex z h).choose else 0
  refine ⟨ULift.up (y.down.map k), ?_⟩
  apply ULift.ext
  apply LocallyConstant.ext
  intro x
  have hx : S.g (y.down x) = 0 :=
    congrArg (fun f : LocallyConstant (ConnectedComponents W) S.X₃ ↦ f x) hy'
  change S.f (k (y.down x)) = y.down x
  dsimp only [k]
  rw [dite_eq_left hx]
  exact (hex (y.down x) hx).choose_spec

/-- The locally constant quotient Hom complex, before taking cohomology. -/
def quotientCochains (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ) (n : ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  ((sections l E W).mapHomologicalComplex (.up ℤ)).obj
    (Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 1))

/-- The transition of locally constant quotient Hom cochains. -/
def quotientStep (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ) (n : ℕ) :
    quotientCochains l E W P (n + 1) ⟶ quotientCochains l E W P n :=
  ((sections l E W).mapHomologicalComplex (.up ℤ)).map
    (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
      (Nat.succ_le_succ (Nat.le_succ n)))

/-- Fixed integral bases, shared by every positive quotient level. -/
def basis (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i : ℤ) : Module.Basis (Fin (Module.finrank (A l E) (P.X i))) (A l E) (P.X i) := by
  let := (hfree i).1
  let := (hfree i).2
  exact Module.finBasis (A l E) (P.X i)

/-- Monoidal inverse image of a regular module, with identity underlying map. -/
def mapRegular {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (S : C) [MonObj S] :
    (F.mapMod S).obj (Mod.regular S) ≅ Mod.regular (F.obj S) :=
  Mod.isoMk (Iso.refl _) (by simp)

/-- The scalar internal module of the scalar ring is its regular module. -/
def scalarRegular :
    (FiniteConstantModel.scalarModules (A l E)).obj
        (ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} (A l E))) :=
  Mod.isoMk (Iso.refl _) (by
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    rfl)

/-- The normalized integral rank-one realization. -/
def integralRegular (W : Scheme.{u}) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (FiniteConstantModel.modelFunctor (A l E) W).obj
        (ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) ≅
      Mod.regular (AdicCompletion.ring l E W) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let S := AddCommGrpCat.of (ULift.{u + 1} (A l E))
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let H := (upperStarFromPoint W).mapMod (Profinite.continuousCoefficientRingObj (A l E))
  exact H.mapIso ((Mod.extendScalars (FiniteConstantModel.scalarToContinuous (A l E))).mapIso
      ((F.mapMod S).mapIso (scalarRegular l E) ≪≫ mapRegular F S) ≪≫
        Mod.regularExtensionIso (FiniteConstantModel.scalarToContinuous (A l E))) ≪≫
    mapRegular (upperStarFromPoint W) _

/-- Realize those same bases in the integral coefficient module category. -/
def integralIso (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (i : ℤ) :
    (internalPerfectIntegralComplex l E W P).X i ≅
      Mod.finiteFree (AdicCompletion.ring l E W) (Module.finrank (A l E) (P.X i)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let r := Module.finrank (A l E) (P.X i)
  let e : (ModuleCat.uliftFunctor.{u + 1, u} (A l E)).obj (P.X i) ≅
      FiniteConstantModel.freeScalars (A l E) r :=
    (((ULift.moduleEquiv : ULift.{u + 1} (P.X i) ≃ₗ[A l E] P.X i).trans
      (basis l E P hfree i).equivFun).trans
      (LinearEquiv.piCongrRight fun _ : Fin r ↦ ULift.moduleEquiv.symm)).toModuleIso
  let F := FiniteConstantModel.modelFunctor (A l E) W
  letI : F.Additive :=
    (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
  exact F.mapIso (e ≪≫
      (ModuleCat.biproductIsoPi (fun _ : Fin r ↦
        ModuleCat.of (A l E) (ULift.{u + 1} (A l E)))).symm) ≪≫
    F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ integralRegular l E W)

/-- The quotient basis is the extension of the fixed integral basis. -/
def quotientIso (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (i : ℤ) :
    (internalPerfectOrdinaryReduction l E W P n).X i ≅
      Mod.finiteFree (AdicCompletion.finiteRing l E W n)
        (Module.finrank (A l E) (P.X i)) := by
  exact Mod.regularFreeExtensionIso (AdicCompletion.quotient l E W n)
    (integralIso l E W P hfree i)

/-- The positive integral quotient has discrete topology. -/
theorem finiteQuotient_discrete (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
  FiniteModelQuotient.finiteTopology_discrete l E n

/-- Locally constant functions on connected components are continuous discrete-valued
functions on the original space, with the necessary coefficient universe lift. -/
def componentsContinuousEquiv (T : Type u) [TopologicalSpace T]
    (B : Type u) [CommRing B] [TopologicalSpace B] [DiscreteTopology B] :
    LocallyConstant (ConnectedComponents T) B ≃+* C(T, ULift.{u + 1} B) := by
  let h : LocallyConstant (ConnectedComponents T) B →+* C(T, ULift.{u + 1} B) :=
    { toFun := fun z ↦ ⟨fun x ↦ ULift.up (z (ConnectedComponents.mk x)),
        continuous_uliftUp.comp (z.continuous.comp ConnectedComponents.continuous_coe)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  apply RingEquiv.ofBijective h
  constructor
  · intro f g he
    apply LocallyConstant.ext
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact ULift.up_injective (congrArg (fun f : C(T, ULift.{u + 1} B) ↦ f x) he)
  · intro f
    let g : C(T, B) := ⟨fun x ↦ (f x).down, continuous_uliftDown.comp f.continuous⟩
    let z : LocallyConstant (ConnectedComponents T) B :=
      ⟨g.continuous.connectedComponentsLift,
        (IsLocallyConstant.iff_continuous _).2
          g.continuous.connectedComponentsLift_continuous⟩
    refine ⟨z, ?_⟩
    ext x
    rfl

/-- The coefficient section comparison, bundled as a ring equivalence. It uses the
normalized finite-discrete coefficient encoding and inverse terminal evaluation. -/
def coefficientRingEquiv (W : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    LocallyConstant (ConnectedComponents W) (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      MonObj.Γ (AdicCompletion.finiteRing l E W n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let e := Classical.choice (FiniteDiscreteOrdinary.encoding_exists B W)
  let θ := (proEtale_finite_constant_sections W (ULift.{u + 1} B)).choose
  let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
  let c := (constantCommuteCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
      (CommRingCat.of (ULift.{u + 1} B))
  let cU := (((sheafToPresheaf (Scheme.ProEt.topology W) RingCat.{u + 1}).mapIso c).app
    (op U)).ringCatIsoToRingEquiv
  let eU := (((sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).mapIso
    e.ringIso).app (op U)).commRingCatIsoToRingEquiv
  exact (componentsContinuousEquiv W B).trans ((θ U).symm.trans
    (cU.trans (eU.trans
      (InternalAbelianSheafModule.sectionGlobalEquiv (Scheme.ProEt.topology W)
        (AdicCompletion.finiteRing l E W n) U (Scheme.ProEt.isTerminalMkId W)).symm)))

/-- A locally constant quotient scalar as a global section of the actual coefficient. -/
def coefficientSection (W : Scheme.{u}) (n : ℕ)
    (z : LocallyConstant (ConnectedComponents W) (Padic.coefficientExtensionRing l E (n + 1))) :
    𝟙_ (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) ⟶
      AdicCompletion.finiteRing l E W n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact (coefficientRingEquiv l E W n z).hom

/-- Constant coefficient functions give the canonical constant scalar section. -/
theorem coefficientSection_const_eval (W : Scheme.{u}) (n : ℕ)
    (b : Padic.coefficientExtensionRing l E (n + 1)) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
    Sheaf.unitHomEval U (coefficientSection l E W n (LocallyConstant.const _ b)) =
      (FiniteDiscreteOrdinary.canonicalAbelianMap
        (Padic.coefficientExtensionRing l E (n + 1)) W).hom.app (op U)
          ((toSheafify (Scheme.ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (n + 1)))))).app (op U) (ULift.up b)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology B := finiteQuotient_discrete l E n
  let J := Scheme.ProEt.topology W
  let U : W.ProEt := Scheme.ProEt.mk (𝟙 W)
  let e := Classical.choice (FiniteDiscreteOrdinary.encoding_exists B W)
  let θ := (proEtale_finite_constant_sections W (ULift.{u + 1} B)).choose
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
      (CommRingCat.of (ULift.{u + 1} B))
  let cU := (((sheafToPresheaf J RingCat.{u + 1}).mapIso c).app
    (op U)).ringCatIsoToRingEquiv
  have heval : Sheaf.unitHomEval U
      (coefficientSection l E W n (LocallyConstant.const _ b)) =
      e.ringIso.hom.hom.app (op U)
        (cU ((θ U).symm (ContinuousMap.const U.left (ULift.up b)))) := by
    change (InternalAbelianSheafModule.sectionGlobalEquiv J
      (AdicCompletion.finiteRing l E W n) U (Scheme.ProEt.isTerminalMkId W))
        ((InternalAbelianSheafModule.sectionGlobalEquiv J
          (AdicCompletion.finiteRing l E W n) U (Scheme.ProEt.isTerminalMkId W)).symm _) = _
    exact RingEquiv.apply_symm_apply _ _
  dsimp only
  erw [heval]
  have hθ : (θ U).symm (ContinuousMap.const U.left (ULift.up b)) =
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B)))).app (op U) (ULift.up b) := by
    apply (θ U).injective
    rw [RingEquiv.apply_symm_apply]
    exact ((proEtale_finite_constant_sections W (ULift.{u + 1} B)).choose_spec.1 U
      (ULift.up b)).symm
  rw [hθ]
  have hu : cU ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
      (RingCat.of (ULift.{u + 1} B)))).app (op U) (ULift.up b)) =
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} B)))).app (op U) (ULift.up b) := by
    apply cU.symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact (congrArg (fun f ↦ f.app (op U) (ULift.up b))
      (realizationRingIso_fac J (ULift.{u + 1} B))).symm
  rw [hu]
  exact e.normalization (op U) (ULift.up b)

/-- Global multiplication identifies locally constant coefficients and regular endomorphisms. -/
def coefficientEndEquiv (W : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    LocallyConstant (ConnectedComponents W) (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      End (Mod.regular (AdicCompletion.finiteRing l E W n)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact (coefficientRingEquiv l E W n).trans
    (RingEquiv.ofBijective _ Mod.regularEndRingHom_bijective)

/-- An integral matrix entry as a linear functional on Hom cochains. -/
def integralEntry (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (CochainComplex.moduleHomComplex P P).X q →ₗ[A l E] A l E where
  toFun f := (basis l E P hfree j).repr (f.v i j hij ((basis l E P hfree i) s)) t
  map_add' := by
    intro f g
    change (basis l E P hfree j).repr
      ((f.v i j hij) ((basis l E P hfree i) s) +
        (g.v i j hij) ((basis l E P hfree i) s)) t = _
    simp
  map_smul' := by
    intro a f
    change (basis l E P hfree j).repr
      (a • (f.v i j hij) ((basis l E P hfree i) s)) t = _
    simp

/-- The uniformizer power vanishes in its specified coefficient quotient. -/
theorem uniformizerPower_zero (n : ℕ) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Reduction of an integral matrix entry to the positive scalar quotient. -/
def reducedEntry (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (CochainComplex.moduleHomComplex P P).X q ⟶
      ModuleCat.of (A l E) (Padic.coefficientExtensionRing l E (n + 1)) :=
  ModuleCat.ofHom
    ((Ideal.Quotient.mkₐ (A l E) (Padic.coefficientExtensionIdeal l E (n + 1))).toLinearMap.comp
      (integralEntry l E P hfree q i j hij s t))

/-- Reduced entries annihilate the uniformizer power acting on the Hom complex. -/
theorem reducedEntry_kills (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
      𝟙 (CochainComplex.moduleHomComplex P P)).f q) ≫
        reducedEntry l E P hfree n q i j hij s t = 0 := by
  ext f
  change (reducedEntry l E P hfree n q i j hij s t)
    (((Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) • f) = 0
  rw [map_smul]
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, uniformizerPower_zero, zero_mul]

/-- A matrix entry on the actual quotient Hom complex, defined by cokernel descent. -/
def quotientEntry (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 1)).X q ⟶
        ModuleCat.of (A l E) (Padic.coefficientExtensionRing l E (n + 1)) :=
  (PreservesCokernel.iso (HomologicalComplex.eval _ _ q)
    ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
      𝟙 (CochainComplex.moduleHomComplex P P))).hom ≫
    cokernel.desc _ (reducedEntry l E P hfree n q i j hij s t)
      (reducedEntry_kills l E P hfree n q i j hij s t)

/-- Quotient coordinates agree with reduced integral entries on the quotient projection. -/
theorem quotientEntry_projection (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (cokernel.π ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
      𝟙 (CochainComplex.moduleHomComplex P P))).f q ≫
        quotientEntry l E P hfree n q i j hij s t =
      reducedEntry l E P hfree n q i j hij s t := by
  dsimp only [quotientEntry]
  rw [← Category.assoc]
  change ((HomologicalComplex.eval (ModuleCat.{u} (A l E)) (.up ℤ) q).map
    (cokernel.π ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
      𝟙 (CochainComplex.moduleHomComplex P P))) ≫ _) ≫ _ = _
  rw [PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- The actual scalar quotient transition, viewed as an integral linear map. -/
def scalarStep (n : ℕ) :
    ModuleCat.of (A l E) (Padic.coefficientExtensionRing l E (n + 2)) ⟶
      ModuleCat.of (A l E) (Padic.coefficientExtensionRing l E (n + 1)) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ (A l E)
    (show Padic.coefficientExtensionIdeal l E (n + 2) ≤
      Padic.coefficientExtensionIdeal l E (n + 1) from
        Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap

/-- Quotient coordinates commute with the actual scalar quotient transition. -/
theorem quotientEntry_step (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q i j : ℤ) (hij : i + q = j)
    (s : Fin (Module.finrank (A l E) (P.X i)))
    (t : Fin (Module.finrank (A l E) (P.X j))) :
    (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
      (Nat.succ_le_succ (Nat.le_succ n))).f q ≫
        quotientEntry l E P hfree n q i j hij s t =
      quotientEntry l E P hfree (n + 1) q i j hij s t ≫ scalarStep l E n := by
  let π := cokernel.π ((Padic.coefficientExtensionUniformizer l E) ^ (n + 2) •
    𝟙 (CochainComplex.moduleHomComplex P P))
  apply (cancel_epi (π.f q)).1
  have hp : π.f q ≫
      (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
        (Nat.succ_le_succ (Nat.le_succ n))).f q =
        (cokernel.π ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
          𝟙 (CochainComplex.moduleHomComplex P P))).f q := by
    change (π ≫ _).f q = _
    rw [Padic.scalarQuotientTransition, cokernel.π_desc]
  rw [← Category.assoc, hp, quotientEntry_projection, ← Category.assoc]
  dsimp only [π]
  rw [quotientEntry_projection]
  ext f
  rfl

/-- The explicit finite matrix attached to a locally constant quotient Hom cochain.
Each entry descends its integral basis coordinate through the actual cokernel,
then forms its actual coefficient section. No chain-map or
bijectivity property is assumed in this construction. -/
def evaluate (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q : ℤ)
    (z : LocallyConstant (ConnectedComponents W)
      ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 1)).X q)) :
    CochainComplex.HomComplex.Cochain (internalPerfectOrdinaryReduction l E W P n)
      (internalPerfectOrdinaryReduction l E W P n) q := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let entry (i j : ℤ) (hij : i + q = j)
      (s : Fin (Module.finrank (A l E) (P.X i)))
      (t : Fin (Module.finrank (A l E) (P.X j))) :=
    z.map (quotientEntry l E P hfree n q i j hij s t)
  exact CochainComplex.HomComplex.Cochain.mk fun i j hij ↦
    (quotientIso l E W P hfree n i).hom ≫
      biproduct.matrix (fun s t ↦ (coefficientEndEquiv l E W n (entry i j hij s t)).asHom) ≫
      (quotientIso l E W P hfree n j).inv

private theorem matrix_zero {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {I J : Type} [Finite I] [Finite J]
    (f : I → C) (g : J → C) :
    biproduct.matrix (fun (i : I) (j : J) ↦ (0 : f i ⟶ g j)) = 0 := by
  ext i j
  simp [biproduct.matrix]

private theorem matrix_add {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {I J : Type} [Finite I] [Finite J]
    {f : I → C} {g : J → C} (a b : ∀ i j, f i ⟶ g j) :
    biproduct.matrix (fun i j ↦ a i j + b i j) =
      biproduct.matrix a + biproduct.matrix b := by
  ext i j
  simp [biproduct.matrix, Preadditive.comp_add, Preadditive.add_comp]

/-- Matrix evaluation takes the zero quotient cochain to zero. -/
theorem evaluate_zero (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q : ℤ) : evaluate l E W P hfree n q 0 = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  dsimp only [evaluate, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.zero_v]
  have hz (s : Fin (Module.finrank (A l E) (P.X i)))
      (t : Fin (Module.finrank (A l E) (P.X j))) :
      (0 : LocallyConstant (ConnectedComponents W)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).X q)).map
            (quotientEntry l E P hfree n q i j hij s t) = 0 := by
    ext x
    exact (quotientEntry l E P hfree n q i j hij s t).hom.map_zero
  simp_rw [hz, map_zero, End.zero_asHom]
  rw [matrix_zero]
  simp only [Limits.comp_zero, Limits.zero_comp]

/-- Matrix evaluation is additive on quotient cochains. -/
theorem evaluate_add (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q : ℤ)
    (z w : LocallyConstant (ConnectedComponents W)
      ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
        (CochainComplex.moduleHomComplex P P) (n + 1)).X q)) :
    evaluate l E W P hfree n q (z + w) =
      evaluate l E W P hfree n q z + evaluate l E W P hfree n q w := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  dsimp only [evaluate, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.add_v]
  have ha (s : Fin (Module.finrank (A l E) (P.X i)))
      (t : Fin (Module.finrank (A l E) (P.X j))) :
      (z + w).map (quotientEntry l E P hfree n q i j hij s t) =
        z.map (quotientEntry l E P hfree n q i j hij s t) +
          w.map (quotientEntry l E P hfree n q i j hij s t) := by
    ext x
    exact (quotientEntry l E P hfree n q i j hij s t).hom.map_add (z x) (w x)
  simp_rw [ha, map_add, End.add_asHom]
  rw [matrix_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The explicit degreewise matrix evaluation as a homomorphism of abelian groups. -/
def evaluationHom (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (n : ℕ) (q : ℤ) :
    (quotientCochains l E W P n).X q ⟶
      (CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W P n)
        (internalPerfectOrdinaryReduction l E W P n)).X q :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦ evaluate l E W P hfree n q z.down
      map_zero' := evaluate_zero l E W P hfree n q
      map_add' := fun z w ↦ evaluate_add l E W P hfree n q z.down w.down }

/-- Successor scalar extension on the full signed Hom complex, with the specified
ordinary balancing maps. -/
def successorMap (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ) (n : ℕ) :
    CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W P (n + 1))
        (internalPerfectOrdinaryReduction l E W P (n + 1)) ⟶
      CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W P n)
        (internalPerfectOrdinaryReduction l E W P n) := by
  let Φ := Mod.extendScalars (AdicCompletion.transition l E W n)
  let α := internalPerfectOrdinaryReductionStep l E W P n
  refine
    { f := fun q ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦
            ((CochainComplex.HomComplex.Cochain.ofHom α.inv).comp (z.map Φ)
              (zero_add q)).comp (CochainComplex.HomComplex.Cochain.ofHom α.hom)
                (add_zero q)
          map_zero' := by simp
          map_add' := by
            intros
            simp [CochainComplex.HomComplex.Cochain.comp_add,
              CochainComplex.HomComplex.Cochain.add_comp] }
      comm' := ?_ }
  intro q r _
  ext z
  change CochainComplex.HomComplex.δ q r
      (((CochainComplex.HomComplex.Cochain.ofHom α.inv).comp (z.map Φ)
        (zero_add q)).comp (CochainComplex.HomComplex.Cochain.ofHom α.hom)
          (add_zero q)) =
    ((CochainComplex.HomComplex.Cochain.ofHom α.inv).comp
      ((CochainComplex.HomComplex.δ q r z).map Φ) (zero_add r)).comp
        (CochainComplex.HomComplex.Cochain.ofHom α.hom) (add_zero r)
  simp only [CochainComplex.HomComplex.δ_comp_ofHom,
    CochainComplex.HomComplex.δ_ofHom_comp, CochainComplex.HomComplex.δ_map]

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
