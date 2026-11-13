import Langlands.Representation.Smooth.CompactDistributionActionStatements
import Langlands.Representation.Smooth.DiscreteOrbitProof
import Langlands.HarmonicAnalysis.VectorTestFunctionProof
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionLawsProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Compactly supported distributions act on smooth representations -/

noncomputable section

open scoped BigOperators

namespace Langlands

open HarmonicAnalysis

universe u v

namespace CompactDistributionAction

section VectorPairing

variable {X : Type u} [TopologicalSpace X]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Applying an algebraic linear form preserves vector-valued compact tests. -/
def scalarTest (ℓ : Module.Dual ℂ V) (f : VectorTestFunction.Space X V) :
    SchwartzBruhat X :=
  ⟨fun x => ℓ (f x), f.locallyConstant.comp ℓ,
    f.hasCompactSupport.comp_left (map_zero ℓ)⟩

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- A distribution can be evaluated on a vector-valued test; all scalar forms
recover the scalar evaluation. -/
theorem exists_vector_test (D : Distribution X) (f : VectorTestFunction.Space X V) :
    ∃ w : V, ∀ ℓ : Module.Dual ℂ V, ℓ w = D (scalarTest ℓ f) := by
  classical
  obtain ⟨n, U, hUo, hUc, a, -, hf⟩ :=
    VectorTestFunctionProof.disjointIndicatorDecomposition X V f
  let b (i : Fin n) := Hecke.TestFunction.characteristic (hUo i) (hUc i)
  refine ⟨∑ i, D (b i) • a i, ?_⟩
  intro ℓ
  have he : scalarTest ℓ f = ∑ i, ℓ (a i) • b i := by
    ext x
    have hx := congrArg (fun q : VectorTestFunction.Space X V => q x) hf
    simp only [VectorTestFunctionProof.space_sum_apply,
      VectorTestFunction.compactBilinear_apply] at hx
    change ℓ (f x) = _
    rw [hx]
    simp [b, map_sum, map_smul, mul_comm]
  rw [he, map_sum, map_sum]
  simp [map_smul, smul_eq_mul, mul_comm]

/-- A locally constant vector map can be paired with a compact distribution by
restricting it to that distribution's own compact support. -/
theorem exists_vector (T : Distribution.compactlySupported (X := X))
    (f : LocallyConstant X V) :
    ∃ w : V, ∀ (ℓ : Module.Dual ℂ V) (φ : LocallyConstant X ℂ),
      (∀ x, φ x = ℓ (f x)) →
      ℓ w = Distribution.compactSupportFunctional T φ := by
  let : CompactSpace (Distribution.support (T : Distribution X)) :=
    isCompact_iff_compactSpace.mp T.property
  let F : VectorTestFunction.Space (Distribution.support (T : Distribution X)) V :=
    ⟨⟨fun x => f x.val, f.isLocallyConstant.comp_continuous continuous_subtype_val⟩,
      HasCompactSupport.of_compactSpace _⟩
  obtain ⟨w, hw⟩ := exists_vector_test (Distribution.onSupport T) F
  refine ⟨w, fun ℓ φ hφ => ?_⟩
  rw [hw]
  change Distribution.onSupport T _ = Distribution.onSupport T _
  congr 1
  ext x
  exact (hφ x.val).symm

/-- Algebraic linear forms separate vectors without any dimension assumption. -/
theorem eq_of_dual {a b : V} (h : ∀ ℓ : Module.Dual ℂ V, ℓ a = ℓ b) : a = b := by
  apply Module.eval_apply_injective ℂ
  ext ℓ
  exact h ℓ

end VectorPairing

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The locally constant orbit map of a smooth vector. -/
def orbit (a : V) : LocallyConstant G V := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := discreteTopology_bot V
  exact ⟨fun g => ρ g a, (IsLocallyConstant.iff_continuous _).mpr
    ((isSmoothVector_iff_continuous_orbitMap ρ a).mp (hρ a))⟩

/-- The scalar matrix coefficient, with no topology on the vector space. -/
def coefficient (a : V) (ℓ : Module.Dual ℂ V) : LocallyConstant G ℂ :=
  ⟨fun g => ℓ (ρ g a), (orbit ρ hρ a).isLocallyConstant.comp ℓ⟩

/-- Evaluation on the orbit map, chosen from the finite-support construction. -/
def value (T : Distribution.compactlySupported (X := G)) (a : V) : V :=
  (exists_vector T (orbit ρ hρ a)).choose

theorem value_pairing (T : Distribution.compactlySupported (X := G)) (a : V)
    (ℓ : Module.Dual ℂ V) :
    ℓ (value ρ hρ T a) =
      Distribution.compactSupportPairing T (coefficient ρ hρ a ℓ) :=
  (exists_vector T (orbit ρ hρ a)).choose_spec ℓ _ (fun _ => rfl)

/-- The orbit pairing is a complex-linear action in both arguments. -/
def act : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ V where
  toFun T :=
    { toFun := value ρ hρ T
      map_add' := by
        intro a b
        apply eq_of_dual
        intro ℓ
        rw [map_add, value_pairing, value_pairing, value_pairing]
        have hc : coefficient ρ hρ (a + b) ℓ =
            coefficient ρ hρ a ℓ + coefficient ρ hρ b ℓ := by
          ext g
          exact (congrArg ℓ (map_add (ρ g) a b)).trans (map_add ℓ _ _)
        rw [hc, map_add]
      map_smul' := by
        intro c a
        apply eq_of_dual
        intro ℓ
        rw [map_smul, value_pairing, value_pairing]
        have hc : coefficient ρ hρ (c • a) ℓ = c • coefficient ρ hρ a ℓ := by
          ext g
          change ℓ (ρ g (c • a)) = c • ℓ (ρ g a)
          rw [map_smul, map_smul]
        rw [hc, map_smul]
        rfl }
  map_add' T S := by
    ext a
    apply eq_of_dual
    intro ℓ
    change ℓ (value ρ hρ (T + S) a) =
      ℓ (value ρ hρ T a + value ρ hρ S a)
    rw [map_add, value_pairing, value_pairing, value_pairing]
    exact Distribution.compactSupportPairing_add_left T S _
  map_smul' c T := by
    ext a
    apply eq_of_dual
    intro ℓ
    change ℓ (value ρ hρ (c • T) a) = ℓ (c • value ρ hρ T a)
    rw [map_smul, value_pairing, value_pairing]
    exact Distribution.compactSupportPairing_smul_left c T _

theorem act_pairing (T : Distribution.compactlySupported (X := G)) (a : V)
    (ℓ : Module.Dual ℂ V) (φ : LocallyConstant G ℂ)
    (hφ : ∀ g, φ g = ℓ (ρ g a)) :
    ℓ (act ρ hρ T a) = Distribution.compactSupportFunctional T φ :=
  (exists_vector T (orbit ρ hρ a)).choose_spec ℓ φ hφ

/-- The scalar convolution formula gives multiplicativity of the vector action. -/
theorem act_convolution (T S : Distribution.compactlySupported (X := G)) :
    act ρ hρ (Distribution.convolution T S) = act ρ hρ T * act ρ hρ S := by
  ext a
  apply eq_of_dual
  intro ℓ
  change ℓ (value ρ hρ (Distribution.convolution T S) a) =
    ℓ (value ρ hρ T (value ρ hρ S a))
  rw [value_pairing, value_pairing, Distribution.compactSupportPairing_convolution]
  congr 1
  ext x
  change Distribution.compactSupportPairing S _ = ℓ (ρ x (value ρ hρ S a))
  calc
    _ = Distribution.compactSupportPairing S
        (coefficient ρ hρ a (ℓ.comp (ρ x))) := by
      congr 1
      ext y
      change ℓ (ρ (x * y) a) = ℓ (ρ x (ρ y a))
      rw [map_mul, Module.End.mul_apply]
    _ = (ℓ.comp (ρ x)) (value ρ hρ S a) := (value_pairing ρ hρ S a _).symm

/-- Point masses act by the original group operators. -/
theorem act_dirac (g : G) :
    act ρ hρ (Distribution.compactDirac g) = ρ g := by
  ext a
  apply eq_of_dual
  intro ℓ
  change ℓ (value ρ hρ (Distribution.compactDirac g) a) = ℓ (ρ g a)
  rw [value_pairing, Distribution.compactSupportPairing_dirac]
  rfl

end Action

end CompactDistributionAction

/-- Renard III.1.3, with independent group and representation-space universes. -/
theorem compactDistributionAction : CompactDistributionActionStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ ρ hρ
  exact ⟨CompactDistributionAction.act ρ hρ,
    CompactDistributionAction.act_pairing ρ hρ,
    CompactDistributionAction.act_convolution ρ hρ,
    CompactDistributionAction.act_dirac ρ hρ⟩

end Langlands
