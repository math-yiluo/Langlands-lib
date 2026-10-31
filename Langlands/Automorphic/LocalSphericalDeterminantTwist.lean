import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Automorphic.LocalSphericalHecke
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Unramified.StandardHeckeSum

/-! # Actual spherical fixed spaces under determinant multiplication -/

noncomputable section
open scoped Classical
universe uF uG uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL
open Langlands.Unramified Langlands.Unramified.MinusculeCosets

private def twistFixedEquiv {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ψ : G →* ℂˣ) (ρ : Representation ℂ G V) {σ : Representation ℂ G W}
    (e : (Langlands.twist ψ ρ).Equiv σ) (K : Subgroup G)
    (hK : K ≤ ψ.ker) : Langlands.fixedVectors ρ K ≃ₗ[ℂ] Langlands.fixedVectors σ K :=
  (LinearEquiv.ofEq _ _
    (Langlands.fixedVectors_twist_eq_of_le_ker ψ ρ K hK).symm).trans
      (Langlands.fixedVectorsEquiv e K)

private theorem twistFixedEquiv_val {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ψ : G →* ℂˣ) (ρ : Representation ℂ G V) {σ : Representation ℂ G W}
    (e : (Langlands.twist ψ ρ).Equiv σ) (K : Subgroup G)
    (hK : K ≤ ψ.ker) (f : Langlands.fixedVectors ρ K) :
    (twistFixedEquiv ψ ρ e K hK f : W) = e (f : V) := rfl

private theorem sum_covariance {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ι : Type*} [Fintype ι]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : V ≃ₗ[ℂ] W) (x : ι → G) (c : ℂ)
    (hc : ∀ a f, σ (x a) (e f) = c • e (ρ (x a) f)) (f : V) :
    (∑ a, σ (x a) (e f)) = c • e (∑ a, ρ (x a) f) := by
  simp_rw [hc]
  rw [map_sum, Finset.smul_sum]

private theorem map_scalar_eigen
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (e : V →ₗ[ℂ] W) (a b : ℂ) (x y : V) (h : y = b • x) :
    a • e y = (a * b) • e x := by
  rw [h, map_smul, smul_smul]

variable {F : Type uF} [Field F] [NumberField F]

local instance sphericalTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance sphericalTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance sphericalTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance sphericalTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance sphericalTwistSpaceGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ}


variable (S : LocalRealization F (r + 1) v)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
variable (hlocal : ∀ g ∈ localIntegral F (r + 1) v,
  χ.finiteLocalDeterminant (r + 1) v g = 1)

include hlocal in
private theorem determinantCharacter_spherical_trivial
    (g : FiniteLocalGL F (r + 1) v)
    (hg : g ∈ Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) :
    χ.finiteLocalDeterminant (r + 1) v g = 1 := by
  apply hlocal g
  apply (OpenSubgroup.mem_toSubgroup (U := localIntegral F (r + 1) v)).mp
  rw [localIntegral_eq_sphericalSubgroup F v r]
  exact hg

/-- Actual multiplication restricts to a linear equivalence of the existing
spherical fixed submodules whenever the local character is integral-trivial. -/
def determinantTwistSphericalEquiv :
    S.SphericalVectors ≃ₗ[ℂ] (S.determinantTwist χ hχ).SphericalVectors :=
  twistFixedEquiv (G := FiniteLocalGL F (r + 1) v) (V := S.Space) (W := (S.determinantTwist χ hχ).Space)
    (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom S.representation
    (σ := (S.determinantTwist χ hχ).representation)
    (S.determinantTwistRepresentationEquiv χ hχ)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)
    (fun _ hg => determinantCharacter_spherical_trivial χ hlocal _ hg)

@[simp]
theorem determinantTwistSphericalEquiv_val (f : S.SphericalVectors) :
    (S.determinantTwistSphericalEquiv χ hχ hlocal f :
      (S.determinantTwist χ hχ).Space) =
      S.determinantTwistEquiv χ hχ (f : S.Space) :=
  twistFixedEquiv_val _ _ _ _ _ f

local instance sphericalTwistResidueFintype :
    Fintype (CompletionPadic.padicField v).canonicalTopologicalData.ResidueField :=
  residueFieldFintype (CompletionPadic.padicField v)


private theorem standardHeckeOperator_eq_sum
    (i : Fin (r + 2)) (f : S.SphericalVectors) :
    (S.standardHeckeOperator i f : S.Space) =
      ∑ α : CosetIndex
          (CompletionPadic.padicField v).canonicalTopologicalData.ResidueField
          (r + 1) i.val,
        S.representation
          (labelledRep
            (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
            (residueLift (CompletionPadic.padicField v)) α) f :=
  standardHecke_cornerAction_eq_sum (CompletionPadic.padicField v)
    S.representation S.isSmooth_canonical i f

include hlocal in
private theorem determinantCharacter_labelledRep (i : Fin (r + 2))
    (α : CosetIndex
      (CompletionPadic.padicField v).canonicalTopologicalData.ResidueField
      (r + 1) i.val) :
    χ.finiteLocalDeterminant (r + 1) v
        (labelledRep
          (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
          (residueLift (CompletionPadic.padicField v)) α) =
      χ.finiteLocalDeterminant (r + 1) v
        (standardDiagonal (CompletionPadic.padicField v) r i) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ :=
    labelledRep_mem_doubleCoset (residueLift_mem (CompletionPadic.padicField v))
      (card_initialSegment r i) α
  rw [hx, map_mul, map_mul,
    determinantCharacter_spherical_trivial χ hlocal k₁ hk₁,
    determinantCharacter_spherical_trivial χ hlocal k₂ hk₂,
    one_mul, mul_one, ← standardDiagonal_eq_subsetTorus]

/-- The actual standard double-coset action is multiplied by the value of
the actual local determinant character on its standard diagonal. -/
theorem standardHeckeOperator_determinantTwist
    (i : Fin (r + 2)) (f : S.SphericalVectors) :
    (S.determinantTwist χ hχ).standardHeckeOperator i
        (S.determinantTwistSphericalEquiv χ hχ hlocal f) =
      (χ.finiteLocalDeterminant (r + 1) v
        (standardDiagonal (CompletionPadic.padicField v) r i) : ℂ) •
        S.determinantTwistSphericalEquiv χ hχ hlocal (S.standardHeckeOperator i f) := by
  apply Subtype.ext
  change ((S.determinantTwist χ hχ).standardHeckeOperator i
      (S.determinantTwistSphericalEquiv χ hχ hlocal f) :
      (S.determinantTwist χ hχ).Space) =
    (χ.finiteLocalDeterminant (r + 1) v
      (standardDiagonal (CompletionPadic.padicField v) r i) : ℂ) •
      S.determinantTwistEquiv χ hχ (S.standardHeckeOperator i f : S.Space)
  let c : ℂ := χ.finiteLocalDeterminant (r + 1) v
    (standardDiagonal (CompletionPadic.padicField v) r i)
  let x : CosetIndex (CompletionPadic.padicField v).canonicalTopologicalData.ResidueField
      (r + 1) i.val → FiniteLocalGL F (r + 1) v :=
    labelledRep (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
      (residueLift (CompletionPadic.padicField v))
  have hc : ∀ α f, (S.determinantTwist χ hχ).representation (x α)
      (S.determinantTwistEquiv χ hχ f) =
      c • S.determinantTwistEquiv χ hχ (S.representation (x α) f) := by
    intro α f
    exact (S.determinantTwistEquiv_representation χ hχ (x α) f).trans
      (congrArg (fun z : ℂˣ => (z : ℂ) •
        S.determinantTwistEquiv χ hχ (S.representation (x α) f))
        (determinantCharacter_labelledRep χ hlocal i α))
  calc
    _ = ∑ α, (S.determinantTwist χ hχ).representation (x α)
        (S.determinantTwistEquiv χ hχ (f : S.Space)) := by
      have hs := standardHeckeOperator_eq_sum (S.determinantTwist χ hχ) i
        (S.determinantTwistSphericalEquiv χ hχ hlocal f)
      simpa only [determinantTwistSphericalEquiv_val S χ hχ hlocal f] using hs
    _ = c • S.determinantTwistEquiv χ hχ (∑ α, S.representation (x α) (f : S.Space)) :=
      sum_covariance S.representation (S.determinantTwist χ hχ).representation
        (S.determinantTwistEquiv χ hχ).toLinearEquiv x c hc (f : S.Space)
    _ = _ := congrArg (fun y : S.Space => c • S.determinantTwistEquiv χ hχ y)
      (standardHeckeOperator_eq_sum S i f).symm

/-- Every supplied scalar eigen-equation transports through actual
multiplication, with the proved standard diagonal character multiplier. -/
theorem standardHeckeOperator_determinantTwist_eigen
    (i : Fin (r + 2)) (f : S.SphericalVectors) (c : ℂ)
    (hf : S.standardHeckeOperator i f = c • f) :
    (S.determinantTwist χ hχ).standardHeckeOperator i
        (S.determinantTwistSphericalEquiv χ hχ hlocal f) =
      ((χ.finiteLocalDeterminant (r + 1) v
        (standardDiagonal (CompletionPadic.padicField v) r i) : ℂ) * c) •
        S.determinantTwistSphericalEquiv χ hχ hlocal f := by
  exact (standardHeckeOperator_determinantTwist S χ hχ hlocal i f).trans
    (map_scalar_eigen (S.determinantTwistSphericalEquiv χ hχ hlocal).toLinearMap
      _ c f (S.standardHeckeOperator i f) hf)

end LocalRealization
end Langlands.Automorphic
