import Langlands.Shimura.Coefficients.HarrisReduction

/-! # Actual Harris lattice inclusions under compact-level refinement -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite Langlands.Global AdelicFunctoriality AlgebraInvolution
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
  {L : Type u} [Field L] [NumberField L]
  {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
  {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
  (p : FinitePlace ℚ)
  (U V : CompactOpenLevel σ.FiniteAdelicPoints) (hVU : V.subgroup ≤ U.subgroup)

include hVU in
/-- The actual compact orbit-span lattice decreases when the acting level decreases. -/
theorem compactCoefficientLattice_mono (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal] :
    compactCoefficientLattice ρ p l V ≤ compactCoefficientLattice ρ p l U := by
  apply Submodule.span_mono
  rintro x ⟨g, y, hy, hgy⟩
  exact ⟨Subgroup.inclusion hVU g, y, hy, hgy⟩

include hVU in
/-- All completion lattices decrease simultaneously in the original product module. -/
theorem harrisProductLattice_mono : harrisProductLattice ρ p V ≤ harrisProductLattice ρ p U := by
  intro x hx l
  exact compactCoefficientLattice_mono ρ p U V hVU l (hx l)

include hVU in
/-- The full lattices in Harris's original tensor coefficient module are nested. -/
theorem harrisLattice_mono : harrisLattice ρ p V ≤ harrisLattice ρ p U := by
  intro x hx
  exact harrisProductLattice_mono ρ p U V hVU hx

/-- The map of the independently constructed full lattices is ambient inclusion. -/
def harrisLatticeInclusion : harrisLattice ρ p V →ₗ[HarrisCoefficientIntegers L p]
    harrisLattice ρ p U :=
  Submodule.inclusion (harrisLattice_mono ρ p U V hVU)

@[simp] theorem harrisLatticeInclusion_coe (x : harrisLattice ρ p V) :
    (harrisLatticeInclusion ρ p U V hVU x :
      (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) = x := rfl

/-- The full-lattice map is injective before any torsion reduction. -/
theorem harrisLatticeInclusion_injective :
    Function.Injective (harrisLatticeInclusion ρ p U V hVU) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : harrisLattice ρ p U =>
    (z : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) hxy

/-- Refining through two actual levels composes the ambient inclusions exactly. -/
@[simp] theorem harrisLatticeInclusion_comp
    (T : CompactOpenLevel σ.FiniteAdelicPoints) (hTV : T.subgroup ≤ V.subgroup) :
    (harrisLatticeInclusion ρ p U V hVU).comp (harrisLatticeInclusion ρ p V T hTV) =
      harrisLatticeInclusion ρ p U T (hTV.trans hVU) := by
  ext x
  rfl

/-- Inclusion intertwines the original full lattice actions after restriction to V. -/
def harrisLatticeActionInclusion :
    harrisLatticeAction ρ p V ⟶
      (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        (Subgroup.inclusion hVU)).obj (harrisLatticeAction ρ p U) where
  hom := ModuleCat.ofHom (harrisLatticeInclusion ρ p U V hVU)
  comm g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

@[simp] theorem harrisLatticeActionInclusion_hom :
    (harrisLatticeActionInclusion ρ p U V hVU).hom =
      ModuleCat.ofHom (harrisLatticeInclusion ρ p U V hVU) := rfl

/-- The action compatibility retains the actual ambient algebraic representation. -/
@[simp] theorem harrisLatticeInclusion_action (g : V.subgroup) (x : harrisLattice ρ p V) :
    harrisLatticeInclusion ρ p U V hVU (((harrisLatticeAction ρ p V).ρ g).hom x) =
      ((harrisLatticeAction ρ p U).ρ (Subgroup.inclusion hVU g)).hom
        (harrisLatticeInclusion ρ p U V hVU x) := rfl

/-- Actual full-lattice inclusion induces a map of every simultaneous torsion reduction. -/
def harrisTorsionSystemInclusion (m : ℕ) :
    harrisTorsionSystem ρ p V m ⟶
      harrisTorsionSystem ρ p U m ⋙
        Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
          (Subgroup.inclusion hVU) where
  app k := ((Langlands.Coefficients.AdicSystem.powerReduction
    (harrisCoefficientScalarIdeal L p m) k.unop).mapAction V.subgroup).map
      (harrisLatticeActionInclusion ρ p U V hVU)
  naturality {i j} f := by
    apply Action.Hom.ext
    exact ((Langlands.Coefficients.AdicSystem.transition
      (harrisCoefficientScalarIdeal L p m) (leOfHom f.unop)).naturality
        (harrisLatticeActionInclusion ρ p U V hVU).hom).symm

/-- The reduction map sends the class of a vector to the class of that same ambient vector. -/
@[simp] theorem harrisTorsionSystemInclusion_mk (m : ℕ) (k : ℕᵒᵖ)
    (x : harrisLattice ρ p V) :
    ((harrisTorsionSystemInclusion ρ p U V hVU m).app k).hom.hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeInclusion ρ p U V hVU x) := rfl

/-- All inclusion maps commute with the original exponent reductions. -/
@[reassoc] theorem harrisTorsionSystemInclusion_transition (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisTorsionSystem ρ p V m).map f ≫
        (harrisTorsionSystemInclusion ρ p U V hVU m).app j =
      (harrisTorsionSystemInclusion ρ p U V hVU m).app i ≫
        (Action.res (ModuleCat.{u} (HarrisCoefficientIntegers L p))
          (Subgroup.inclusion hVU)).map ((harrisTorsionSystem ρ p U m).map f) :=
  (harrisTorsionSystemInclusion ρ p U V hVU m).naturality f

end Langlands.Shimura.Coefficients
