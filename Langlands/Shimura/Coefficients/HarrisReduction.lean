import Langlands.Shimura.Coefficients.HarrisLattice
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Simultaneous finite reductions of Harris coefficients -/

noncomputable section

universe u v

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite
open scoped TensorProduct Pointwise

section PrincipalProducts

variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module (R i) (V i)]
variable (a : (i : ι) → R i) (n : ℕ)

/-- Membership in a principal power times the whole module is scalar divisibility. -/
theorem mem_principalPower_smul_top {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] (b : S) (k : ℕ) (x : M) :
    x ∈ ((Ideal.span {b}) ^ k • ⊤ : Submodule S M) ↔ ∃ y, b ^ k • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

/-- A linear equivalence carries each principal-power reduction to the corresponding reduction. -/
def principalPowerReductionEquiv {S M N : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (e : M ≃ₗ[S] N) (b : S) (k : ℕ) :
    (M ⧸ ((Ideal.span {b}) ^ k • ⊤ : Submodule S M)) ≃ₗ[S]
      (N ⧸ ((Ideal.span {b}) ^ k • ⊤ : Submodule S N)) :=
  Submodule.Quotient.equiv _ _ e (by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (mem_principalPower_smul_top b k x).mp hx
      exact (mem_principalPower_smul_top b k _).mpr ⟨e z, (e.map_smul _ _).symm⟩
    · intro hy
      obtain ⟨z, rfl⟩ := (mem_principalPower_smul_top b k y).mp hy
      refine ⟨b ^ k • e.symm z, ?_, ?_⟩
      · exact (mem_principalPower_smul_top b k _).mpr ⟨e.symm z, rfl⟩
      · simp)

@[simp] theorem principalPowerReductionEquiv_mk {S M N : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (e : M ≃ₗ[S] N) (b : S) (k : ℕ) (x : M) :
    principalPowerReductionEquiv e b k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

/-- Coordinatewise reduction over the actual product of scalar rings. -/
def dependentProductReduction :
    ((i : ι) → V i) →ₗ[((i : ι) → R i)]
      ((i : ι) → V i ⧸ ((Ideal.span {a i}) ^ n • ⊤ : Submodule (R i) (V i))) where
  toFun x i := Submodule.Quotient.mk (x i)
  map_add' x y := by ext i; exact map_add (Submodule.mkQ _) _ _
  map_smul' r x := by ext i; exact map_smul (Submodule.mkQ _) _ _

theorem dependentProductReduction_surjective :
    Function.Surjective (dependentProductReduction R V a n) := by
  intro x
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (x i)
  exact ⟨y, funext hy⟩

/-- Divisibility in a product is precisely divisibility in each component. -/
theorem dependentProductReduction_ker :
    LinearMap.ker (dependentProductReduction R V a n) =
      (Ideal.span {a}) ^ n • ⊤ := by
  ext x
  simp only [LinearMap.mem_ker, dependentProductReduction, LinearMap.coe_mk,
    AddHom.coe_mk, funext_iff, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
    mem_principalPower_smul_top]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩ i
    exact ⟨y i, hy i⟩

/-- Reduction of a product is the product of the actual coordinate reductions. -/
def dependentProductReductionEquiv :
    (((i : ι) → V i) ⧸ ((Ideal.span {a}) ^ n • ⊤ :
      Submodule ((i : ι) → R i) ((i : ι) → V i))) ≃ₗ[((i : ι) → R i)]
      ((i : ι) → V i ⧸ ((Ideal.span {a i}) ^ n • ⊤ : Submodule (R i) (V i))) :=
  (Submodule.quotEquivOfEq _ _ (dependentProductReduction_ker R V a n).symm).trans
    ((dependentProductReduction R V a n).quotKerEquivOfSurjective
      (dependentProductReduction_surjective R V a n))

@[simp] theorem dependentProductReductionEquiv_mk (x : (i : ι) → V i) :
    dependentProductReductionEquiv R V a n (Submodule.Quotient.mk x) =
      fun i => Submodule.Quotient.mk (x i) := rfl

/-- Coordinatewise quotient homomorphism for a dependent product of rings. -/
def dependentProductRingReduction :
    ((i : ι) → R i) →+* ((i : ι) → R i ⧸ (Ideal.span {a i}) ^ n) :=
  RingHom.pi fun i => (Ideal.Quotient.mk _).comp (Pi.evalRingHom R i)

theorem dependentProductRingReduction_surjective :
    Function.Surjective (dependentProductRingReduction R a n) := by
  intro x
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  exact ⟨y, funext hy⟩

theorem dependentProductRingReduction_ker :
    RingHom.ker (dependentProductRingReduction R a n) = (Ideal.span {a}) ^ n := by
  ext x
  simp only [RingHom.mem_ker, dependentProductRingReduction, RingHom.pi_apply,
    RingHom.comp_apply, Pi.evalRingHom_apply, funext_iff, Pi.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩ i
    exact ⟨y i, hy i⟩

/-- The quotient of the product ring by a principal power has its canonical product splitting. -/
def dependentProductRingReductionEquiv :
    (((i : ι) → R i) ⧸ (Ideal.span {a}) ^ n) ≃+*
      ((i : ι) → R i ⧸ (Ideal.span {a i}) ^ n) :=
  (Ideal.quotEquivOfEq (dependentProductRingReduction_ker R a n).symm).trans
    ((dependentProductRingReduction R a n).quotientKerEquivOfSurjective
      (dependentProductRingReduction_surjective R a n))

@[simp] theorem dependentProductRingReductionEquiv_mk (x : (i : ι) → R i) :
    dependentProductRingReductionEquiv R a n (Ideal.Quotient.mk _ x) =
      fun i => Ideal.Quotient.mk _ (x i) := rfl

end PrincipalProducts

open Langlands.Global AdelicFunctoriality AlgebraInvolution

section HarrisScalars

variable (L : Type u) [Field L] [NumberField L] (p : FinitePlace ℚ)

/-- Rational scalar powers in the whole integral coefficient algebra. -/
def harrisCoefficientScalarIdeal (m : ℕ) : Ideal (HarrisCoefficientIntegers L p) :=
  Ideal.span {(m : HarrisCoefficientIntegers L p)}

/-- The actual finite coefficient ring for the simultaneous reduction. -/
abbrev HarrisCoefficientReductionRing (m n : ℕ) :=
  HarrisCoefficientIntegers L p ⧸ harrisCoefficientScalarIdeal L p m ^ n

/-- The finite coefficient ring splits into the actual reductions at all places above `p`. -/
def harrisCoefficientReductionRingEquiv (m n : ℕ) :
    HarrisCoefficientReductionRing L p m n ≃+*
      ((l : FinitePlacesAbove L p) → CoefficientReductionRing l.1 m n) :=
  dependentProductRingReductionEquiv
    (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1) (m : _) n

@[simp] theorem harrisCoefficientReductionRingEquiv_mk (m n : ℕ)
    (r : HarrisCoefficientIntegers L p) :
    harrisCoefficientReductionRingEquiv L p m n (Ideal.Quotient.mk _ r) =
      fun l => Ideal.Quotient.mk _ (r l) := rfl

theorem harrisCoefficientReductionRing_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (HarrisCoefficientReductionRing L p m n) := by
  let (l : FinitePlacesAbove L p) : Finite (CoefficientReductionRing l.1 m n) :=
    coefficientReductionRing_finite l.1 m hm n
  exact Finite.of_equiv _ (harrisCoefficientReductionRingEquiv L p m n).symm.toEquiv

end HarrisScalars

section Harris

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- The full lattice is canonically the product of the actual component lattices. -/
def harrisLatticeComponentEquiv :
    (harrisLatticeAction ρ p U).V ≃ₗ[HarrisCoefficientIntegers L p]
      ((l : FinitePlacesAbove L p) → (algebraicCompactCoefficientLattice ρ p l.1 U).action.V) :=
  (harrisLatticeEquiv ρ p U).trans (dependentProductSubmoduleEquiv _ _ _)

/-- The integral product equivalence retains the original completion actions. -/
theorem harrisLatticeComponentEquiv_action (g : U.subgroup)
    (x : (harrisLatticeAction ρ p U).V) :
    harrisLatticeComponentEquiv ρ p U (((harrisLatticeAction ρ p U).ρ g).hom x) =
      fun l : FinitePlacesAbove L p => ((algebraicCompactCoefficientLattice ρ p l.1 U).action.ρ g).hom
        (harrisLatticeComponentEquiv ρ p U x l) := by
  ext l
  apply Subtype.ext
  exact congrFun (ρ.harrisCoefficientEquiv_adelic p g ((harrisLattice ρ p U).subtype x)) l

/-- The simultaneous torsion system of the full stable Harris lattice. -/
def harrisTorsionSystem (m : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u} (HarrisCoefficientIntegers L p)) U.subgroup :=
  torsionSystem (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U)

/-- The original integral action reduced modulo the `n`th rational-scalar power. -/
abbrev harrisTorsionAction (m n : ℕ) := (harrisTorsionSystem ρ p U m).obj (op n)

/-- Full-lattice reduction is canonically the product of the actual one-place reductions. -/
def harrisTorsionEquiv (m n : ℕ) :
    (harrisTorsionAction ρ p U m n).V ≃ₗ[HarrisCoefficientIntegers L p]
      ((l : FinitePlacesAbove L p) →
        (torsionAction (coefficientScalarIdeal l.1 m)
          (algebraicCompactCoefficientLattice ρ p l.1 U).action n).V) :=
  (principalPowerReductionEquiv (harrisLatticeComponentEquiv ρ p U) (m : _) n).trans
    (dependentProductReductionEquiv
      (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1)
      (fun l => (algebraicCompactCoefficientLattice ρ p l.1 U).action.V) (m : _) n)

@[simp] theorem harrisTorsionEquiv_mk (m n : ℕ)
    (x : (harrisLatticeAction ρ p U).V) :
    harrisTorsionEquiv ρ p U m n (Submodule.Quotient.mk x) =
      fun l => Submodule.Quotient.mk (harrisLatticeComponentEquiv ρ p U x l) := rfl

/-- The canonical finite reduction splitting intertwines the original torsion actions. -/
theorem harrisTorsionEquiv_action (m n : ℕ) (g : U.subgroup)
    (x : (harrisTorsionAction ρ p U m n).V) :
    harrisTorsionEquiv ρ p U m n (((harrisTorsionAction ρ p U m n).ρ g).hom x) =
      fun l : FinitePlacesAbove L p => ((torsionAction (coefficientScalarIdeal l.1 m)
        (algebraicCompactCoefficientLattice ρ p l.1 U).action n).ρ g).hom
          (harrisTorsionEquiv ρ p U m n x l) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (fun l => Submodule.Quotient.mk
    (harrisLatticeComponentEquiv ρ p U (((harrisLatticeAction ρ p U).ρ g).hom y) l)) = _
  rw [harrisLatticeComponentEquiv_action]
  rfl

/-- The actual kernel of the action on the full rational-scalar reduction. -/
def harrisCongruenceKernel (m n : ℕ) : Subgroup U.subgroup :=
  congruenceKernel (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U) n

instance harrisCongruenceKernel_normal (m n : ℕ) :
    (harrisCongruenceKernel ρ p U m n).Normal :=
  congruenceKernel_normal _ _ _

/-- An element acts trivially on the full reduction exactly when it does so at every place. -/
theorem mem_harrisCongruenceKernel (m n : ℕ) (g : U.subgroup) :
    g ∈ harrisCongruenceKernel ρ p U m n ↔
      ∀ l : FinitePlacesAbove L p, g ∈ congruenceKernel (coefficientScalarIdeal l.1 m)
        (algebraicCompactCoefficientLattice ρ p l.1 U).action n := by
  classical
  change g ∈ congruenceKernel _ _ _ ↔ _
  rw [mem_congruenceKernel]
  constructor
  · intro hg l
    rw [mem_congruenceKernel]
    intro y
    let z : (i : FinitePlacesAbove L p) →
        (torsionAction (coefficientScalarIdeal i.1 m)
          (algebraicCompactCoefficientLattice ρ p i.1 U).action n).V :=
      Pi.single l (Submodule.Quotient.mk y)
    let x := (harrisTorsionEquiv ρ p U m n).symm z
    have hx : ((harrisTorsionAction ρ p U m n).ρ g).hom x = x := by
      obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← ht]
      exact hg t
    have he := (harrisTorsionEquiv_action ρ p U m n g x).symm.trans
      (congrArg (harrisTorsionEquiv ρ p U m n) hx)
    have hel := congrFun he l
    have hz : z l = Submodule.Quotient.mk y := Pi.single_eq_same l _
    change ((torsionAction (coefficientScalarIdeal l.1 m)
      (algebraicCompactCoefficientLattice ρ p l.1 U).action n).ρ g).hom
        (harrisTorsionEquiv ρ p U m n x l) = harrisTorsionEquiv ρ p U m n x l at hel
    dsimp only [x] at hel
    rw [LinearEquiv.apply_symm_apply, hz] at hel
    exact hel
  · intro hg x
    apply (harrisTorsionEquiv ρ p U m n).injective
    change harrisTorsionEquiv ρ p U m n
      (((harrisTorsionAction ρ p U m n).ρ g).hom (Submodule.Quotient.mk x)) = _
    refine (harrisTorsionEquiv_action ρ p U m n g (Submodule.Quotient.mk x)).trans ?_
    ext l
    exact (mem_congruenceKernel _ _ n g).mp (hg l)
      (harrisLatticeComponentEquiv ρ p U x l)

/-- The full kernel is the finite intersection of the actual component action kernels. -/
theorem harrisCongruenceKernel_eq (m n : ℕ) :
    harrisCongruenceKernel ρ p U m n =
      ⨅ l : FinitePlacesAbove L p, congruenceKernel (coefficientScalarIdeal l.1 m)
        (algebraicCompactCoefficientLattice ρ p l.1 U).action n := by
  ext g
  simpa only [Subgroup.mem_iInf] using mem_harrisCongruenceKernel ρ p U m n g

/-- Nonzero scalar reductions have an open full action kernel. -/
theorem harrisCongruenceKernel_isOpen (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    IsOpen (harrisCongruenceKernel ρ p U m n : Set U.subgroup) := by
  rw [harrisCongruenceKernel_eq, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun l =>
    (algebraicCompactCoefficient_congruenceKernel ρ p l.1 U m hm n).1

/-- The actual image quotient of the level action on the full coefficient reduction. -/
abbrev HarrisCongruenceGroup (m n : ℕ) := U.subgroup ⧸ harrisCongruenceKernel ρ p U m n

theorem harrisCongruenceGroup_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (HarrisCongruenceGroup ρ p U m n) := by
  let : CompactSpace U.subgroup := isCompact_iff_compactSpace.mp U.isCompact
  exact (harrisCongruenceKernel ρ p U m n).quotient_finite_of_isOpen
    (harrisCongruenceKernel_isOpen ρ p U m hm n)

/-- Each full-lattice reduction has a finite underlying carrier. -/
theorem harrisTorsionAction_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (harrisTorsionAction ρ p U m n).V := by
  let : Finite (HarrisCoefficientReductionRing L p m n) :=
    harrisCoefficientReductionRing_finite L p m hm n
  let : Module.Finite (HarrisCoefficientIntegers L p) (harrisLatticeAction ρ p U).V :=
    inferInstanceAs (Module.Finite (HarrisCoefficientIntegers L p) (harrisLattice ρ p U))
  exact torsionAction_finite _ _ _

/-- The full torsion action with scalars in the actual finite quotient ring. -/
def harrisFiniteTorsionAction (m n : ℕ) :
    Action (ModuleCat.{u} (HarrisCoefficientReductionRing L p m n)) U.subgroup :=
  ((Langlands.Coefficients.AdicSystem.reduction
    (harrisCoefficientScalarIdeal L p m ^ n)).mapAction U.subgroup).obj
      (harrisLatticeAction ρ p U)

@[simp] theorem harrisFiniteTorsionAction_mk (m n : ℕ) (g : U.subgroup)
    (x : (harrisLatticeAction ρ p U).V) :
    ((harrisFiniteTorsionAction ρ p U m n).ρ g).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((harrisLatticeAction ρ p U).ρ g).hom x) := rfl

/-- The module splitting respects the actual quotient-ring splitting of scalars. -/
theorem harrisTorsionEquiv_quotient_smul (m n : ℕ)
    (r : HarrisCoefficientReductionRing L p m n)
    (x : (harrisFiniteTorsionAction ρ p U m n).V) :
    harrisTorsionEquiv ρ p U m n (r • x) =
      fun l : FinitePlacesAbove L p =>
        (harrisCoefficientReductionRingEquiv L p m n r l) •
          (show ((algebraicCompactCoefficientLattice ρ p l.1 U).rationalTorsionAction
            l.1 m n).V from harrisTorsionEquiv ρ p U m n x l) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (fun l => Submodule.Quotient.mk
    (harrisLatticeComponentEquiv ρ p U (s • y) l)) = _
  rw [map_smul]
  rfl

/-- Retaining quotient-ring scalars leaves the actual action kernel unchanged. -/
theorem harrisFiniteTorsionAction_ker (m n : ℕ) :
    (harrisFiniteTorsionAction ρ p U m n).ρ.ker = harrisCongruenceKernel ρ p U m n := by
  ext g
  change (harrisFiniteTorsionAction ρ p U m n).ρ g = 1 ↔
    (harrisTorsionAction ρ p U m n).ρ g = 1
  constructor
  · intro h
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : End (harrisFiniteTorsionAction ρ p U m n).V => f.hom x) h
  · intro h
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : End (harrisTorsionAction ρ p U m n).V => f.hom x) h

/-- The full finite coefficient action factored through its actual image quotient group. -/
def harrisFiniteCoefficientAction (m n : ℕ) :
    Action (ModuleCat.{u} (HarrisCoefficientReductionRing L p m n))
      (HarrisCongruenceGroup ρ p U m n) where
  V := (harrisFiniteTorsionAction ρ p U m n).V
  ρ := QuotientGroup.lift _ (harrisFiniteTorsionAction ρ p U m n).ρ
    (by rw [harrisFiniteTorsionAction_ker])

@[simp] theorem harrisFiniteCoefficientAction_mk (m n : ℕ) (g : U.subgroup) :
    (harrisFiniteCoefficientAction ρ p U m n).ρ (QuotientGroup.mk g) =
      (harrisFiniteTorsionAction ρ p U m n).ρ g := rfl

theorem harrisFiniteCoefficientAction_injective (m n : ℕ) :
    Function.Injective (harrisFiniteCoefficientAction ρ p U m n).ρ := by
  unfold harrisFiniteCoefficientAction
  exact (QuotientGroup.injective_lift_iff _ _
    (by rw [harrisFiniteTorsionAction_ker])).mpr (harrisFiniteTorsionAction_ker ρ p U m n).symm

/-- The constructed faithful quotient action has both finite group and finite module. -/
theorem harrisFiniteCoefficientAction_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (HarrisCongruenceGroup ρ p U m n) ∧
      Finite (harrisFiniteCoefficientAction ρ p U m n).V :=
  ⟨harrisCongruenceGroup_finite ρ p U m hm n, harrisTorsionAction_finite ρ p U m hm n⟩

/-- The full coefficient transition maps are the original surjective quotient maps. -/
theorem harrisTorsionSystem_transition_surjective (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (((harrisTorsionSystem ρ p U m).map (homOfLE h).op).hom) :=
  torsion_transition_surjective _ _ h

/-- Splitting the full torsion system commutes with the actual one-place transition maps. -/
theorem harrisTorsionEquiv_transition (m : ℕ) {i j : ℕ} (h : i ≤ j)
    (x : (harrisTorsionAction ρ p U m j).V) :
    harrisTorsionEquiv ρ p U m i
        (((harrisTorsionSystem ρ p U m).map (homOfLE h).op).hom.hom x) =
      fun l : FinitePlacesAbove L p =>
        (((algebraicCompactCoefficientLattice ρ p l.1 U).rationalTorsionSystem l.1 m).map
          (homOfLE h).op).hom.hom (harrisTorsionEquiv ρ p U m j x l) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The congruence quotient groups form the actual inverse system attached to the full lattice. -/
abbrev harrisCongruenceGroups (m : ℕ) : ℕᵒᵖ ⥤ GrpCat.{u} :=
  torsionCongruenceGroups (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U)

/-- Group transitions are induced by the identity on the original compact level. -/
abbrev harrisCongruenceTransition (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    HarrisCongruenceGroup ρ p U m j →* HarrisCongruenceGroup ρ p U m i :=
  torsionCongruenceTransition (harrisCoefficientScalarIdeal L p m) (harrisLatticeAction ρ p U) h

/-- Coefficient transitions intertwine the quotient-group actions along their group transitions. -/
theorem harrisCongruenceTransition_equivariant (m : ℕ) {i j : ℕ} (h : i ≤ j)
    (g : HarrisCongruenceGroup ρ p U m j) (x : (harrisFiniteCoefficientAction ρ p U m j).V) :
    ((harrisTorsionSystem ρ p U m).map (homOfLE h).op).hom.hom
        (((harrisFiniteCoefficientAction ρ p U m j).ρ g).hom x) =
      ((harrisFiniteCoefficientAction ρ p U m i).ρ (harrisCongruenceTransition ρ p U m h g)).hom
        (((harrisTorsionSystem ρ p U m).map (homOfLE h).op).hom.hom x) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

end Harris

end Langlands.Shimura.Coefficients
