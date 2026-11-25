/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoefficientLimit
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Ordinary tensor models of finite-free coefficient cones

Source: Stacks Project, Tag 09C6, the finite-free coefficient calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Ordinary completed constant realization, before localization.
Source: Stacks Tags 093J--093M. -/
def finitePerfectAdicOrdinary (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{t} A ⥤ CompletedAdicModules X d :=
  finitePerfectAdicConstant X A ⋙ completedAdicScalarExtension X d

instance finitePerfectAdicOrdinary_additive (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : (finitePerfectAdicOrdinary X d).Additive := by
  have := (finitePerfectAdicConstant_exact X A).1
  unfold finitePerfectAdicOrdinary
  infer_instance

/-- The actual coefficient diagram tensored with a variable module.
Source: Stacks Tag 09C6. -/
def finitePerfectAdicTensorFunctor (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) :
    CompletedAdicModules X d ⥤ (ℕᵒᵖ ⥤ CompletedAdicModules X d) :=
  curriedTensor (CompletedAdicModules X d) ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (CompletedAdicModules X d)
      (CompletedAdicModules X d)).obj (finitePerfectAdicCoefficientDiagram X d)

instance finitePerfectAdicTensorFunctor_additive
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    (finitePerfectAdicTensorFunctor X d).Additive := by
  let : MonoidalPreadditive (CompletedAdicModules X d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing X d)
  unfold finitePerfectAdicTensorFunctor
  infer_instance

private theorem tensorProjection_natural
    {C : Type*} [Category* C] [MonoidalCategory C]
    {M N B : C} (f : M ⟶ N) (q : 𝟙_ C ⟶ B) :
    f ≫ (ρ_ N).inv ≫ N ◁ q = (ρ_ M).inv ≫ M ◁ q ≫ f ▷ B := by
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]

/-- The coefficient projection tensored with an arbitrary completed module.
Source: Stacks Tag 09C6, the maps in the finite-projective coefficient calculation. -/
def finitePerfectAdicTensorProjection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (M : CompletedAdicModules X d) (n : ℕ) :
    M ⟶ ((finitePerfectAdicTensorFunctor X d).obj M).obj (op n) :=
  (ρ_ M).inv ≫ M ◁ finitePerfectAdicCoefficientProjection X d n

/-- Tensor projection commutes with every module map.
Source: Stacks Tag 09C6; functoriality of tensor and its right unitor. -/
theorem finitePerfectAdicTensorProjection_naturality
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : CompletedAdicModules X d} (f : M ⟶ N) (n : ℕ) :
    f ≫ finitePerfectAdicTensorProjection X d N n =
      finitePerfectAdicTensorProjection X d M n ≫
        ((finitePerfectAdicTensorFunctor X d).map f).app (op n) := by
  exact tensorProjection_natural f (finitePerfectAdicCoefficientProjection X d n)

/-- The ordinary tensor cone, with its actual coefficient projections.
Source: Stacks Tag 09C6. -/
def finitePerfectAdicTensorCone (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (M : CompletedAdicModules X d) :
    Cone ((finitePerfectAdicTensorFunctor X d).obj M) :=
  ((tensorLeft M).mapCone (finitePerfectAdicCoefficientCone X d)).extend (ρ_ M).inv

/-- The explicit complex of ordinary completed constant modules.
Source: Stacks Tag 09C6. -/
def finitePerfectAdicOrdinaryComplex (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{t} A) ℤ) :=
  ((finitePerfectAdicOrdinary X d).mapHomologicalComplex (.up ℤ)).obj P

/-- Tensor each term of the ordinary completed realization with the actual coefficient tower.
Source: Stacks Tag 09C6. -/
def finitePerfectAdicTensorComplexDiagram (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{t} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (CompletedAdicModules X d) ℤ :=
  (((finitePerfectAdicTensorFunctor X d).mapHomologicalComplex (.up ℤ)).obj
    (finitePerfectAdicOrdinaryComplex X d P)).asFunctor

/-- The tensor projections form a cone of complexes. Differentials commute because the
projection construction is natural for every module map, including each differential.
Source: Stacks Tag 09C6. -/
def finitePerfectAdicTensorComplexCone (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{t} A) ℤ) :
    Cone (finitePerfectAdicTensorComplexDiagram X d P) where
  pt := finitePerfectAdicOrdinaryComplex X d P
  π :=
    { app := fun n ↦
        { f := fun j ↦ finitePerfectAdicTensorProjection X d
            ((finitePerfectAdicOrdinaryComplex X d P).X j) n.unop
          comm' := fun i j _ ↦ by
            exact (finitePerfectAdicTensorProjection_naturality X d
              ((finitePerfectAdicOrdinaryComplex X d P).d i j) n.unop).symm }
      naturality := by
        intro n m f
        ext j : 1
        change 𝟙 _ ≫ finitePerfectAdicTensorProjection X d
            ((finitePerfectAdicOrdinaryComplex X d P).X j) m.unop =
          finitePerfectAdicTensorProjection X d
            ((finitePerfectAdicOrdinaryComplex X d P).X j) n.unop ≫
            ((finitePerfectAdicTensorFunctor X d).obj
              ((finitePerfectAdicOrdinaryComplex X d P).X j)).map f
        rw [Category.id_comp]
        exact ((finitePerfectAdicTensorCone X d
          ((finitePerfectAdicOrdinaryComplex X d P).X j)).w f).symm }

private def constantUnitMap (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (koszulConstantFunctor X A).obj
        (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)) ⟶
      SheafOfModules.unit (adicModuleRing X A) := by
  have := (koszulConstantUnit_local X A).1
  have := (koszulConstantUnit_local X A).2
  exact (PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit X A)).symm
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars (koszulConstantUnit X A)).obj
          (SheafOfModules.unit (adicModuleRing X A)).val).obj U)
        { toFun := fun x ↦ (koszulConstantUnit X A).app U x
          map_add' := map_add _
          map_smul' := fun a b ↦ by
            change (koszulConstantUnit X A).app U (a * b) =
              (koszulConstantUnit X A).app U a * (koszulConstantUnit X A).app U b
            exact map_mul _ a b }
      naturality := fun {U V} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom ((koszulConstantUnit X A).naturality f) x }

private theorem constantUnitMap_fac (X : Scheme.{t}) (A : Type t) [CommRing A] :
    toSheafify (ProEt.topology X)
        ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).obj
          (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A))).presheaf ≫
      ((SheafOfModules.toSheaf _).map (constantUnitMap X A)).hom =
        Functor.whiskerRight (koszulConstantUnit X A)
          (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1}) := by
  have := (koszulConstantUnit_local X A).1
  have := (koszulConstantUnit_local X A).2
  change (PresheafOfModules.toPresheaf _).map
    (PresheafOfModules.sheafificationHomEquiv _ (constantUnitMap X A)) = _
  unfold constantUnitMap
  rw [Equiv.apply_symm_apply]
  rfl

private theorem constantUnitMap_isIso (X : Scheme.{t}) (A : Type t) [CommRing A] :
    IsIso (constantUnitMap X A) := by
  let J := ProEt.topology X
  let f := (SheafOfModules.toSheaf _).map (constantUnitMap X A)
  let η := toSheafify J
    ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).obj
      (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A))).presheaf
  let α := Functor.whiskerRight (koszulConstantUnit X A)
    (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1})
  have : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U a b hab
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} A)))) a b hab
  have : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U a
    exact Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} A)))) a
  have : Presheaf.IsLocallySurjective J η := inferInstance
  have : Presheaf.IsLocallyInjective J f.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α
      (constantUnitMap_fac X A)
  have : Presheaf.IsLocallySurjective J f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (constantUnitMap_fac X A)
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso (constantUnitMap X A) (SheafOfModules.toSheaf _)

private def ordinaryUnitIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) :
    (finitePerfectAdicOrdinary X d).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit (completedAdicRing X d) := by
  have := constantUnitMap_isIso X A
  let e : ((ModuleCat.uliftFunctor.{t + 1, t} A ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom).obj
      (ModuleCat.of A A)) ≅ ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A) :=
    (LinearEquiv.refl (ULift.{t + 1} A) (ULift.{t + 1} A)).toModuleIso
  let e' := (koszulConstantFunctor X A).mapIso e ≪≫ asIso (constantUnitMap X A)
  let c := completedAdicScalar X d
  let s := (SheafOfModules.scalarExtension_constraint_coherence
    (adicConstantRing X A) (completedAdicCommRing X d) c).some
  exact (completedAdicScalarExtension X d).mapIso e' ≪≫
    eqToIso ((completedAdicChangeData X c).choose_spec.choose _) ≪≫ s.unitIso

section TensorPowers
variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteProducts C]
  {r : ℕ} {M : C} (e₀ : M ≅ ∏ᶜ (fun _ : Fin r ↦ 𝟙_ C))

private def tensorPowerComponent (B : C) : M ⊗ B ≅ ∏ᶜ (fun _ : Fin r ↦ B) :=
  (tensorRight B).mapIso e₀ ≪≫
    PreservesProduct.iso (tensorRight B) (fun _ : Fin r ↦ 𝟙_ C) ≪≫
      Pi.mapIso (fun _ ↦ λ_ B)

@[reassoc]
private theorem tensorPowerComponent_π (B : C) (i : Fin r) :
    (tensorPowerComponent e₀ B).hom ≫ Pi.π (fun _ : Fin r ↦ B) i =
      (e₀.hom ≫ Pi.π (fun _ : Fin r ↦ 𝟙_ C) i) ▷ B ≫ (λ_ B).hom := by
  simp only [tensorPowerComponent, Iso.trans_hom, PreservesProduct.iso_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [Pi.mapIso_hom_π, piComparison_comp_π_assoc, ← Category.assoc, ← Functor.map_comp]
  rfl

omit [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] in
private theorem powerFunctor_π {B B' : C} (f : B ⟶ B') (i : Fin r) :
    (Functor.const (Discrete (Fin r)) ⋙ lim).map f ≫ Pi.π (fun _ : Fin r ↦ B') i =
      Pi.π (fun _ : Fin r ↦ B) i ≫ f :=
  limMap_π ((Functor.const (Discrete (Fin r))).map f) (Discrete.mk i)

private def tensorPowerIso :
    tensorLeft M ≅ Functor.const (Discrete (Fin r)) ⋙ lim :=
  NatIso.ofComponents (tensorPowerComponent e₀) (by
    intro B B' f
    refine Pi.hom_ext (f := fun _ : Fin r ↦ B') _ _ ?_
    intro i
    simp only [Category.assoc, tensorPowerComponent_π, tensorPowerComponent_π_assoc,
      powerFunctor_π]
    change M ◁ f ≫ _ ▷ B' ≫ (λ_ B').hom = _ ▷ B ≫ (λ_ B).hom ≫ f
    rw [whisker_exchange_assoc, leftUnitor_naturality])

private theorem tensorPowerIso_unit {B : C} (q : 𝟙_ C ⟶ B) :
    e₀.hom ≫ (Functor.const (Discrete (Fin r)) ⋙ lim).map q =
      (ρ_ M).inv ≫ M ◁ q ≫ (tensorPowerIso e₀).hom.app B := by
  refine Pi.hom_ext (f := fun _ : Fin r ↦ B) _ _ ?_
  intro i
  rw [Category.assoc, powerFunctor_π]
  change _ = ((ρ_ M).inv ≫ M ◁ q ≫
    (tensorPowerComponent e₀ B).hom) ≫ Pi.π _ i
  simp only [Category.assoc, tensorPowerComponent_π]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  rw [leftUnitor_naturality, ← Category.assoc (ρ_ (𝟙_ C)).inv, unitors_equal]
  simp only [Iso.inv_hom_id, Category.id_comp, Category.assoc]
  rfl

end TensorPowers

/-- A free algebraic module gives precisely a finite power of the coefficient cone.

Source: Stacks Project, Tag 09C6, finite-free case of the displayed coefficient calculation;
Modules on Sites, Tags 093J--093M.
(blueprint: lem-weil-pbc-finite-perfect-adic-free-tensor-cone).

Proof: the constant realization of A is the unit module of the constant ring sheaf.
Ordinary scalar extension sends that unit to the completed-ring unit: on local tensor
sections the isomorphism sends s tensor a to s times the scalar image of a, and the
inverse sends s to s tensor 1. Balancing and local generation prove both identities.
The constant realization and scalar extension are additive, hence preserve finite
biproducts. Apply these unit comparisons to the coordinate decomposition of A^r.
Tensor with a coefficient module also preserves finite biproducts. The left unitor
identifies the tensor of the unit with each coefficient module. These comparisons
are natural for all coefficient maps and hence define the diagram isomorphism e.
On each coordinate the cone square is the equality sending s tensor a to
projection(s) times scalar(a); it follows from naturality of the unitors. Equality
of the coordinate maps proves the displayed cone equation. For r = 0 all objects
are zero and the same argument uses the empty biproduct; no nonzero-ring assumption
is made. This statement concerns only free modules, with no complex or derived data. -/
theorem finitePerfectAdicFreeTensorCone_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (r : ℕ) :
    let M := (finitePerfectAdicOrdinary X d).obj (ModuleCat.of A (Fin r → A))
    let F : CompletedAdicModules X d ⥤ CompletedAdicModules X d :=
      Functor.const (Discrete (Fin r)) ⋙ lim
    ∃ (e : (finitePerfectAdicTensorFunctor X d).obj M ≅
        finitePerfectAdicCoefficientDiagram X d ⋙ F)
      (e₀ : M ≅ F.obj (SheafOfModules.unit (completedAdicRing X d))),
      ∀ n : ℕᵒᵖ, e₀.hom ≫ F.map ((finitePerfectAdicCoefficientCone X d).π.app n) =
        (finitePerfectAdicTensorCone X d M).π.app n ≫ e.hom.app n  := by
  let : MonoidalPreadditive (CompletedAdicModules X d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing X d)
  let H := finitePerfectAdicOrdinary X d
  let M := H.obj (ModuleCat.of A (Fin r → A))
  let V := fun _ : Fin r ↦ ModuleCat.of A A
  let e₀ : M ≅ ∏ᶜ (fun _ : Fin r ↦ 𝟙_ (CompletedAdicModules X d)) :=
    H.mapIso (ModuleCat.piIsoPi V).symm ≪≫
      PreservesProduct.iso H V ≪≫ Pi.mapIso (fun _ ↦ ordinaryUnitIso X d)
  refine ⟨Functor.isoWhiskerLeft (finitePerfectAdicCoefficientDiagram X d)
    (tensorPowerIso e₀), e₀, ?_⟩
  intro n
  exact tensorPowerIso_unit e₀ ((finitePerfectAdicCoefficientCone X d).π.app n)

end AlgebraicGeometry.Scheme
