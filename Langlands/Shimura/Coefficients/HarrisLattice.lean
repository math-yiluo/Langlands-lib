import Langlands.Shimura.Coefficients.HarrisSplitting
import Langlands.Shimura.Coefficients.AlgebraicCompactCoefficient

/-! # Stable lattices in Harris's whole finite-place coefficient module -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Shimura.Coefficients

section Products

variable {ι : Type*} (R : ι → Type*) (V : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, AddCommGroup (V i)] [∀ i, Module (R i) (V i)]

/-- Finite generation for a dependent product over the product of its scalar rings. -/
theorem finite_dependentProduct [Finite ι] [∀ i, Module.Finite (R i) (V i)] :
    Module.Finite ((i : ι) → R i) ((i : ι) → V i) := by
  let (i : ι) : Module ((j : ι) → R j) (V i) :=
    Module.compHom (V i) (Pi.evalRingHom R i)
  let (i : ι) : Module.Finite ((j : ι) → R j) (V i) := by
    let f : V i →ₛₗ[Pi.evalRingHom R i] V i :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (f.finite_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact Module.Finite.pi

variable (Λ : (i : ι) → Submodule (R i) (V i))

/-- The dependent product with its actual componentwise product-ring action. -/
def dependentProductSubmodule : Submodule ((i : ι) → R i) ((i : ι) → V i) where
  carrier := {x | ∀ i, x i ∈ Λ i}
  zero_mem' := fun i => (Λ i).zero_mem
  add_mem' := fun hx hy i => (Λ i).add_mem (hx i) (hy i)
  smul_mem' := fun r _ hx i => (Λ i).smul_mem (r i) (hx i)

@[simp] theorem mem_dependentProductSubmodule (x : (i : ι) → V i) :
    x ∈ dependentProductSubmodule R V Λ ↔ ∀ i, x i ∈ Λ i := Iff.rfl

/-- A product submodule is linearly equivalent to the product of the actual subtypes. -/
def dependentProductSubmoduleEquiv :
    dependentProductSubmodule R V Λ ≃ₗ[((i : ι) → R i)] ((i : ι) → Λ i) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem dependentProductSubmodule_fg [Finite ι] (hfg : ∀ i, (Λ i).FG) :
    (dependentProductSubmodule R V Λ).FG := by
  let (i : ι) : Module.Finite (R i) (Λ i) := Module.Finite.of_fg (hfg i)
  let : Module.Finite ((i : ι) → R i) ((i : ι) → Λ i) :=
    finite_dependentProduct R (fun i => Λ i)
  exact (Module.Finite.iff_fg).mp
    (Module.Finite.equiv (dependentProductSubmoduleEquiv R V Λ).symm)

variable (K : ι → Type*) [∀ i, CommRing (K i)] [∀ i, Algebra (R i) (K i)]
variable [∀ i, Module (K i) (V i)] [∀ i, IsScalarTower (R i) (K i) (V i)]

/-- The product of full lattices is full over the actual product algebra. -/
theorem dependentProductSubmodule_isLattice [Finite ι]
    [∀ i, Submodule.IsLattice (K i) (Λ i)] :
    Submodule.IsLattice ((i : ι) → K i) (dependentProductSubmodule R V Λ) where
  fg := dependentProductSubmodule_fg R V Λ fun _ => Submodule.IsLattice.fg
  span_eq_top := by
    classical
    let := Fintype.ofFinite ι
    apply top_unique
    intro x _
    have hsingle : ∀ i, ∀ y : V i,
        Pi.single i y ∈ Submodule.span ((i : ι) → K i)
          (dependentProductSubmodule R V Λ : Set ((i : ι) → V i)) := by
      intro i y
      have hy : y ∈ Submodule.span (K i) (Λ i : Set (V i)) := by
        rw [Submodule.IsLattice.span_eq_top]
        trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        intro j
        by_cases h : j = i
        · subst j
          simpa using hy
        · simp [Pi.single_eq_of_ne h]
      | zero => simp
      | add y z _ _ hy hz =>
        simpa only [Pi.single_add] using
          (Submodule.span ((i : ι) → K i)
            (dependentProductSubmodule R V Λ : Set ((i : ι) → V i))).add_mem hy hz
      | smul a y _ hy =>
        have heq : Pi.single i (a • y) =
            (Pi.single i a : (j : ι) → K j) • (Pi.single i y) := by
          ext j
          by_cases h : j = i
          · subst j
            simp
          · simp [Pi.single_eq_of_ne h]
        rw [heq]
        exact (Submodule.span ((i : ι) → K i)
          (dependentProductSubmodule R V Λ : Set ((i : ι) → V i))).smul_mem _ hy
    have hsum := (Submodule.span ((i : ι) → K i)
      (dependentProductSubmodule R V Λ : Set ((i : ι) → V i))).sum_mem
        (fun i (_ : i ∈ Finset.univ) => hsingle i (x i))
    simpa only [LinearMap.sum_single_apply] using hsum

end Products

open Langlands.Global AdelicFunctoriality AlgebraInvolution

section Scalars

variable (L : Type u) [Field L] [NumberField L] (p : FinitePlace ℚ)

/-- The product of the actual valuation rings at every coefficient place above `p`. -/
abbrev HarrisCoefficientIntegers :=
  (l : FinitePlacesAbove L p) → CoefficientIntegers l.1

/-- The product of the completed coefficient fields at every place above `p`. -/
abbrev HarrisCoefficientFields :=
  (l : FinitePlacesAbove L p) → FiniteCompletion L l.1

/-- The canonical integral embedding into Harris's original tensor coefficient algebra. -/
def harrisCoefficientIntegersMap :
    HarrisCoefficientIntegers L p →+* L ⊗[ℚ] FiniteCompletion ℚ p :=
  (harrisCoefficientRingEquiv L p).symm.toRingHom.comp
    (RingHom.pi fun l => (algebraMap (CoefficientIntegers l.1) (FiniteCompletion L l.1)).comp
      (Pi.evalRingHom (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1) l))

instance harrisCoefficientIntegersAlgebra :
    Algebra (HarrisCoefficientIntegers L p) (L ⊗[ℚ] FiniteCompletion ℚ p) :=
  (harrisCoefficientIntegersMap L p).toAlgebra

@[simp] theorem harrisCoefficientRingEquiv_integers (r : HarrisCoefficientIntegers L p) :
    harrisCoefficientRingEquiv L p (harrisCoefficientIntegersMap L p r) =
      fun l => algebraMap (CoefficientIntegers l.1) (FiniteCompletion L l.1) (r l) :=
  (harrisCoefficientRingEquiv L p).apply_symm_apply _

theorem harrisCoefficientIntegersMap_injective :
    Function.Injective (harrisCoefficientIntegersMap L p) := by
  intro r s h
  have h' := congrArg (harrisCoefficientRingEquiv L p) h
  simp only [harrisCoefficientRingEquiv_integers] at h'
  funext l
  apply Subtype.ext
  exact congrFun h' l

variable (W : Type w) [AddCommGroup W] [Module L W]

/-- Integral scalars act through their canonical inclusion in the original coefficient algebra. -/
theorem harrisCoefficientIntegers_smul (r : HarrisCoefficientIntegers L p)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :
    r • x = harrisCoefficientIntegersMap L p r • x :=
  (IsScalarTower.algebraMap_smul (L ⊗[ℚ] FiniteCompletion ℚ p) r x).symm

/-- The splitting respects the original coefficient-algebra action component by component. -/
theorem harrisCoefficientEquiv_smul (s : L ⊗[ℚ] FiniteCompletion ℚ p)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :
    harrisCoefficientEquiv L p W (s • x) =
      harrisCoefficientRingEquiv L p s • harrisCoefficientEquiv L p W x := by
  ext l
  induction x using TensorProduct.inductionOn with
  | tmul t x => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy =>
    simp only [smul_add, map_add, Pi.add_apply, hx, hy]

/-- The inverse splitting respects scalars through the inverse canonical ring equivalence. -/
theorem harrisCoefficientEquiv_symm_smul (s : HarrisCoefficientFields L p)
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) :
    (harrisCoefficientEquiv L p W).symm (s • x) =
      (harrisCoefficientRingEquiv L p).symm s • (harrisCoefficientEquiv L p W).symm x := by
  apply (harrisCoefficientEquiv L p W).injective
  rw [LinearEquiv.apply_symm_apply, harrisCoefficientEquiv_smul,
    LinearEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- With the canonical integral scalar action, the splitting is linear over the product ring. -/
def harrisCoefficientIntegralEquiv :
    ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) ≃ₗ[HarrisCoefficientIntegers L p]
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) where
  toEquiv := (harrisCoefficientEquiv L p W).toEquiv
  map_add' := (harrisCoefficientEquiv L p W).map_add
  map_smul' r x := by
    change harrisCoefficientEquiv L p W ((harrisCoefficientIntegersMap L p r) • x) = _
    rw [harrisCoefficientEquiv_smul, harrisCoefficientRingEquiv_integers]
    rfl

end Scalars

section Harris

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ)

/-- The actual completion actions are linear over the whole product of completed fields. -/
def harrisProductFieldAction :
    σ.FiniteAdelicPoints →*
      (((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
        ≃ₗ[HarrisCoefficientFields L p]
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)) where
  toFun g :=
    { toFun := fun x l => ρ.placeAction p l.1 g (x l)
      invFun := fun x l => (ρ.placeAction p l.1 g).symm (x l)
      left_inv := fun x => by ext l; exact (ρ.placeAction p l.1 g).left_inv (x l)
      right_inv := fun x => by ext l; exact (ρ.placeAction p l.1 g).right_inv (x l)
      map_add' := fun x y => by ext l; exact (ρ.placeAction p l.1 g).map_add _ _
      map_smul' := fun r x => by ext l; exact (ρ.placeAction p l.1 g).map_smul _ _ }
  map_one' := by ext x l; simp
  map_mul' g h := by ext x l; simp [LinearEquiv.mul_apply]

@[simp] theorem harrisProductFieldAction_apply (g : σ.FiniteAdelicPoints)
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
    (l : FinitePlacesAbove L p) :
    harrisProductFieldAction ρ p g x l = ρ.placeAction p l.1 g (x l) := rfl

variable [Module.Finite L W] (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- Assemble the constructed compact-level lattices at all coefficient places above `p`. -/
def harrisProductLattice :
    Submodule (HarrisCoefficientIntegers L p)
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) :=
  dependentProductSubmodule
    (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1)
    (fun l => FiniteCompletion L l.1 ⊗[L] W)
    (fun l => (algebraicCompactCoefficientLattice ρ p l.1 U).carrier)

@[simp] theorem mem_harrisProductLattice
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) :
    x ∈ harrisProductLattice ρ p U ↔
      ∀ l, x l ∈ (algebraicCompactCoefficientLattice ρ p l.1 U).carrier := Iff.rfl

instance harrisProductLattice_isLattice :
    Submodule.IsLattice (HarrisCoefficientFields L p) (harrisProductLattice ρ p U) :=
  dependentProductSubmodule_isLattice _ _ _ _

/-- Stability uses the original completion actions and their proved compact-level stability. -/
theorem harrisProductLattice_stable :
    IsStable ((harrisProductFieldAction ρ p).comp U.subgroup.subtype)
      (harrisProductLattice ρ p U) := by
  intro g x hx l
  exact (algebraicCompactCoefficientLattice ρ p l.1 U).stable g (x l) (hx l)

/-- The integral product representation is the restriction of the original field actions. -/
def harrisProductLatticeAction :
    Action (ModuleCat.{u} (HarrisCoefficientIntegers L p)) U.subgroup :=
  latticeAction ((harrisProductFieldAction ρ p).comp U.subgroup.subtype)
    (harrisProductLattice ρ p U) (harrisProductLattice_stable ρ p U)

/-- The full lattice inside Harris's original tensor coefficient module. -/
def harrisLattice :
    Submodule (HarrisCoefficientIntegers L p)
      ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :=
  (harrisProductLattice ρ p U).comap (harrisCoefficientIntegralEquiv L p W).toLinearMap

@[simp] theorem mem_harrisLattice
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :
    x ∈ harrisLattice ρ p U ↔
      ∀ l, harrisCoefficientEquiv L p W x l ∈
        (algebraicCompactCoefficientLattice ρ p l.1 U).carrier := Iff.rfl

/-- The canonical splitting restricts to an equivalence of the actual integral lattices. -/
def harrisLatticeEquiv :
    harrisLattice ρ p U ≃ₗ[HarrisCoefficientIntegers L p] harrisProductLattice ρ p U :=
  (harrisCoefficientIntegralEquiv L p W).ofSubmodule' (harrisProductLattice ρ p U)

@[simp] theorem harrisLatticeEquiv_apply (x : harrisLattice ρ p U) :
    (harrisLatticeEquiv ρ p U x :
      (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) =
        harrisCoefficientEquiv L p W x := rfl

instance harrisLattice_isLattice :
    Submodule.IsLattice (L ⊗[ℚ] FiniteCompletion ℚ p) (harrisLattice ρ p U) where
  fg := by
    exact (Module.Finite.iff_fg).mp
      (Module.Finite.equiv (harrisLatticeEquiv ρ p U).symm)
  span_eq_top := by
    apply top_unique
    intro x _
    have hx : harrisCoefficientEquiv L p W x ∈
        Submodule.span (HarrisCoefficientFields L p)
          (harrisProductLattice ρ p U :
            Set ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)) := by
      rw [Submodule.IsLattice.span_eq_top]
      trivial
    have hspan : ∀ y, y ∈ Submodule.span (HarrisCoefficientFields L p)
        (harrisProductLattice ρ p U :
          Set ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)) →
        (harrisCoefficientEquiv L p W).symm y ∈
          Submodule.span (L ⊗[ℚ] FiniteCompletion ℚ p)
            (harrisLattice ρ p U :
              Set ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        change harrisCoefficientEquiv L p W ((harrisCoefficientEquiv L p W).symm y) ∈
          harrisProductLattice ρ p U
        rw [LinearEquiv.apply_symm_apply]
        exact hy
      | zero => simp
      | add y z _ _ hy hz =>
        simpa only [map_add] using
          (Submodule.span (L ⊗[ℚ] FiniteCompletion ℚ p)
            (harrisLattice ρ p U :
              Set ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W))).add_mem hy hz
      | smul a y _ hy =>
        rw [harrisCoefficientEquiv_symm_smul]
        exact (Submodule.span (L ⊗[ℚ] FiniteCompletion ℚ p)
          (harrisLattice ρ p U :
            Set ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W))).smul_mem _ hy
    simpa only [LinearEquiv.symm_apply_apply] using hspan _ hx

/-- The pulled-back lattice is stable for Harris's original adelic representation. -/
theorem harrisLattice_stable :
    IsStable ((ρ.harrisAdelic p).comp U.subgroup.subtype) (harrisLattice ρ p U) := by
  intro g x hx
  change harrisCoefficientEquiv L p W (ρ.harrisAdelic p g x) ∈ harrisProductLattice ρ p U
  rw [ρ.harrisCoefficientEquiv_adelic]
  intro l
  exact (algebraicCompactCoefficientLattice ρ p l.1 U).stable g
    (harrisCoefficientEquiv L p W x l) (hx l)

/-- The integral representation on the full lattice is the original action restricted to it. -/
def harrisLatticeAction :
    Action (ModuleCat.{u} (HarrisCoefficientIntegers L p)) U.subgroup :=
  latticeAction ((ρ.harrisAdelic p).comp U.subgroup.subtype)
    (harrisLattice ρ p U) (harrisLattice_stable ρ p U)

@[simp] theorem harrisLatticeAction_apply (g : U.subgroup) (x : harrisLattice ρ p U) :
    (harrisLattice ρ p U).subtype (((harrisLatticeAction ρ p U).ρ g).hom x) =
      ρ.harrisAdelic p g x := rfl

/-- Integral lattice splitting intertwines the restrictions of the original actions. -/
theorem harrisLatticeEquiv_action (g : U.subgroup) (x : harrisLattice ρ p U) :
    harrisLatticeEquiv ρ p U (((harrisLatticeAction ρ p U).ρ g).hom x) =
      ((harrisProductLatticeAction ρ p U).ρ g).hom (harrisLatticeEquiv ρ p U x) := by
  apply Subtype.ext
  exact ρ.harrisCoefficientEquiv_adelic p g x

end Harris

end Langlands.Shimura.Coefficients
