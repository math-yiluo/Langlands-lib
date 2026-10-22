import Langlands.Shimura.Coefficients.Algebraic
import Langlands.Coefficients.AdicSystem
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Stable lattices and torsion coefficient representations -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite
open scoped TensorProduct

section Stable

variable {R : Type u} [CommRing R] {K : Type v} [CommRing K] [Algebra R K]
variable {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V))

/-- Stability of a submodule under a given linear group action. -/
def IsStable (Λ : Submodule R V) : Prop :=
  ∀ g : G, ∀ x ∈ Λ, ρ g x ∈ Λ

/-- The smallest stable submodule containing `Λ`, formed by spanning all its translates. -/
def orbitSpan (Λ : Submodule R V) : Submodule R V :=
  Submodule.span R {x | ∃ g : G, ∃ y ∈ Λ, ρ g y = x}

omit [Algebra R K] [IsScalarTower R K V] in
theorem le_orbitSpan (Λ : Submodule R V) : Λ ≤ orbitSpan ρ Λ := by
  intro x hx
  apply Submodule.subset_span
  exact ⟨1, x, hx, by simp⟩

theorem orbitSpan_stable (Λ : Submodule R V) : IsStable ρ (orbitSpan ρ Λ) := by
  intro g x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, hy, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨g * h, y, hy, by simp [LinearEquiv.mul_apply]⟩
  | zero => simp
  | add x y hx hy hxx hyy => simpa using (orbitSpan ρ Λ).add_mem hxx hyy
  | smul r x hx hxx =>
    change (ρ g).restrictScalars R (r • x) ∈ orbitSpan ρ Λ
    simpa using (orbitSpan ρ Λ).smul_mem r hxx

omit [Algebra R K] [IsScalarTower R K V] in
theorem orbitSpan_le {Λ N : Submodule R V} (hN : IsStable ρ N) (h : Λ ≤ N) :
    orbitSpan ρ Λ ≤ N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, x, hx, rfl⟩
  exact hN g x (h hx)

omit [Algebra R K] [IsScalarTower R K V] in
theorem orbitSpan_eq {Λ : Submodule R V} (hΛ : IsStable ρ Λ) : orbitSpan ρ Λ = Λ :=
  le_antisymm (orbitSpan_le ρ hΛ le_rfl) (le_orbitSpan ρ Λ)

/-- The orbit span is a full lattice as soon as it is finitely generated. -/
theorem orbitSpan_isLattice (Λ : Submodule R V) [Submodule.IsLattice K Λ]
    (hfg : (orbitSpan ρ Λ).FG) : Submodule.IsLattice K (orbitSpan ρ Λ) :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg K (le_orbitSpan ρ Λ) hfg

/-- For a finite group, the orbit span of a finitely generated submodule is finitely generated. -/
theorem orbitSpan_fg [Finite G] (Λ : Submodule R V) (hΛ : Λ.FG) :
    (orbitSpan ρ Λ).FG := by
  have heq : orbitSpan ρ Λ = ⨆ g : G, Λ.map ((ρ g).toLinearMap.restrictScalars R) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, y, hy, rfl⟩
      exact le_iSup (fun g : G => Λ.map ((ρ g).toLinearMap.restrictScalars R)) g
        (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
    · apply iSup_le
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact Submodule.subset_span ⟨g, y, hy, rfl⟩
  rw [heq]
  exact Submodule.fg_iSup _ (fun g => hΛ.map _)

/-- Orbit saturation constructs a stable full lattice for every finite group action. -/
theorem finite_orbitSpan_isLattice [Finite G] (Λ : Submodule R V)
    [Submodule.IsLattice K Λ] : Submodule.IsLattice K (orbitSpan ρ Λ) :=
  orbitSpan_isLattice ρ Λ (orbitSpan_fg ρ Λ Submodule.IsLattice.fg)

/-- The actual restricted action on the submodule, with all representation laws proved. -/
def latticeAction (Λ : Submodule R V) (hΛ : IsStable ρ Λ) :
    Action (ModuleCat.{w} R) G where
  V := ModuleCat.of R Λ
  ρ :=
    { toFun := fun g => ModuleCat.ofHom (((ρ g).toLinearMap.restrictScalars R).restrict (hΛ g))
      map_one' := by apply ModuleCat.hom_ext; ext x; simp
      map_mul' := by
        intro g h
        apply ModuleCat.hom_ext
        ext x
        change ρ (g * h) x = ρ g (ρ h x)
        simp [LinearEquiv.mul_apply] }

@[simp] theorem latticeAction_apply (Λ : Submodule R V) (hΛ : IsStable ρ Λ)
    (g : G) (x : Λ) : Λ.subtype (((latticeAction ρ Λ hΛ).ρ g).hom x) = ρ g x := rfl

end Stable

section Systems

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
variable (I : Ideal R) (M : Action (ModuleCat.{w} R) G)

/-- Evaluate the existing equivariant adic system at each index, retaining its action. -/
def torsionSystem : ℕᵒᵖ ⥤ Action (ModuleCat.{w} R) G where
  obj n := ((Langlands.Coefficients.AdicSystem.powerReduction I n.unop).mapAction G).obj M
  map f :=
    { hom := (Langlands.Coefficients.AdicSystem.transition I (leOfHom f.unop)).app M.V
      comm := fun g =>
        (Langlands.Coefficients.AdicSystem.transition I (leOfHom f.unop)).naturality (M.ρ g) }
  map_id n := by
    apply Action.Hom.ext
    exact congrArg (fun e => e.app M.V)
      (Langlands.Coefficients.AdicSystem.transition_refl I n.unop)
  map_comp f g := by
    apply Action.Hom.ext
    exact (congrArg (fun e => e.app M.V)
      (Langlands.Coefficients.AdicSystem.transition_comp I
        (leOfHom g.unop) (leOfHom f.unop))).symm

/-- The `n`th torsion coefficient module and its induced action. -/
abbrev torsionAction (n : ℕ) := (torsionSystem I M).obj (op n)

@[simp] theorem torsionAction_mk (n : ℕ) (g : G) (x : M.V) :
    ((torsionAction I M n).ρ g).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((M.ρ g).hom x) := rfl

/-- Canonical equivariant quotient map from the lattice module to its reduction. -/
def torsionQuotientMap (n : ℕ) : M ⟶ torsionAction I M n where
  hom := ModuleCat.ofHom (Submodule.mkQ (I ^ n • ⊤))
  comm g := by ext x; rfl

theorem torsion_transition_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective ((torsionSystem I M).map (homOfLE h).op).hom :=
  Langlands.Coefficients.AdicSystem.transition_surjective I h M.V

/-- The quotient presentation agrees with tensoring by the quotient ring. -/
def torsionTensorEquiv (n : ℕ) :
    ((R ⧸ I ^ n) ⊗[R] M.V) ≃ₗ[R] (torsionAction I M n).V :=
  TensorProduct.quotTensorEquivQuotSMul M.V (I ^ n)

/-- The congruence kernel consists exactly of the elements acting trivially on the reduction. -/
def congruenceKernel (n : ℕ) : Subgroup G := (torsionAction I M n).ρ.ker

instance congruenceKernel_normal (n : ℕ) : (congruenceKernel I M n).Normal :=
  inferInstanceAs (MonoidHom.ker _).Normal

theorem mem_congruenceKernel (n : ℕ) (g : G) :
    g ∈ congruenceKernel I M n ↔
      ∀ x : M.V, (Submodule.Quotient.mk ((M.ρ g).hom x) : (torsionAction I M n).V) =
        Submodule.Quotient.mk x := by
  change (torsionAction I M n).ρ g = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun f : End (torsionAction I M n).V => f.hom (Submodule.Quotient.mk x)) h
  · intro h
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact h y

/-- Triviality modulo a higher power implies triviality modulo every lower power. -/
theorem congruenceKernel_antitone : Antitone (congruenceKernel I M) := by
  intro m n h g hg
  rw [mem_congruenceKernel] at hg ⊢
  intro x
  exact congrArg (fun y => ((torsionSystem I M).map (homOfLE h).op).hom.hom y) (hg x)

/-- Finite coefficients and a finite module give a finite torsion coefficient carrier. -/
instance torsionAction_finite (n : ℕ) [Module.Finite R M.V] [Finite (R ⧸ I ^ n)] :
    Finite (torsionAction I M n).V :=
  Submodule.finite_quotient_smul (I ^ n) (Module.Finite.fg_top : (⊤ : Submodule R M.V).FG)

/-- Factor the reduction through any normal subgroup contained in its congruence kernel. -/
def quotientTorsionAction (n : ℕ) (N : Subgroup G) [N.Normal]
    (hN : N ≤ congruenceKernel I M n) : Action (ModuleCat.{w} R) (G ⧸ N) where
  V := (torsionAction I M n).V
  ρ := QuotientGroup.lift N (torsionAction I M n).ρ hN

@[simp] theorem quotientTorsionAction_mk (n : ℕ) (N : Subgroup G) [N.Normal]
    (hN : N ≤ congruenceKernel I M n) (g : G) :
    (quotientTorsionAction I M n N hN).ρ (QuotientGroup.mk g) =
      (torsionAction I M n).ρ g := rfl

end Systems

section Harris

open Langlands.Global AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
variable (U : Subgroup σ.FiniteAdelicPoints)

/-- The actual local coefficient ring at `l`. -/
abbrev CoefficientIntegers := l.adicCompletionIntegers L

/-- A full lattice for the `l`-adic coefficient representation, stable under the chosen level. -/
structure StableCoefficientLattice where
  carrier : Submodule (CoefficientIntegers l) (FiniteCompletion L l ⊗[L] W)
  isLattice : Submodule.IsLattice (FiniteCompletion L l) carrier
  stable : IsStable ((ρ.placeAction p l).comp U.subtype) carrier

namespace StableCoefficientLattice

variable {ρ p l U} (Λ : StableCoefficientLattice ρ p l U)

instance : Submodule.IsLattice (FiniteCompletion L l) Λ.carrier := Λ.isLattice

instance : Module.Finite (CoefficientIntegers l) Λ.carrier := inferInstance

instance : Module.Free (CoefficientIntegers l) Λ.carrier := inferInstance

/-- The integral coefficient representation is the restriction of the algebraic local action. -/
def action : Action (ModuleCat.{u} (CoefficientIntegers l)) U :=
  latticeAction ((ρ.placeAction p l).comp U.subtype) Λ.carrier Λ.stable

/-- The actual inverse system of coefficient representations modulo powers of an ideal. -/
def system (I : Ideal (CoefficientIntegers l)) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u} (CoefficientIntegers l)) U :=
  torsionSystem I Λ.action

end StableCoefficientLattice

end Harris

end Langlands.Shimura.Coefficients
