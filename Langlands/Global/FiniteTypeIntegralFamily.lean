import Langlands.Global.LinearIntegralFamily

/-! # A compact integral family and its independence of a closed representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace LinearIntegralFamily

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  {N M : ℕ} (ρ : MatrixRepresentation G (Fin N))
  (σ : MatrixRepresentation G (Fin M))

/-- Uniform integrality of the finitely many regular matrix coefficients
compares the integral family of a closed representation with any representation. -/
theorem eventually_subgroup_le (hρ : IsClosedSubgroup ρ) :
    ∀ᶠ v in cofinite, subgroup F G ρ v ≤ subgroup F G σ v := by
  have h₁ : ∀ᶠ v in cofinite, ∀ i j : Fin M,
      ∀ x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        x ∈ subgroup F G ρ v →
          σ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) x i j ∈
            v.adicCompletionIntegers F := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    filter_upwards [eventually_uniform_integral F G ρ hρ
      (σ.hom.hom.left.appTop (GeneralLinear.entrySection (Fin M) (CommRingCat.of F) i j))]
      with v hv x hx
    rw [MatrixRepresentation.affineMatrix_apply,
      GeneralLinear.affinePointsEquiv_entry_evaluation,
      GroupScheme.affinePointEvaluation_postcomp]
    exact hv x hx
  have h₂ : ∀ᶠ v in cofinite, ∀ i j : Fin M,
      ∀ x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        x ∈ subgroup F G ρ v →
          (σ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) x)⁻¹ i j ∈
            v.adicCompletionIntegers F := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    filter_upwards [eventually_uniform_integral F G ρ hρ
      (σ.hom.hom.left.appTop
        (GeneralLinear.inverseEntrySection (Fin M) (CommRingCat.of F) i j))]
      with v hv x hx
    rw [MatrixRepresentation.affineMatrix_apply,
      GeneralLinear.affinePointsEquiv_inverseEntry_evaluation,
      GroupScheme.affinePointEvaluation_postcomp]
    exact hv x hx
  filter_upwards [h₁, h₂] with v h₁ h₂ x hx
  exact (mem_subgroup F G σ v x).mpr ⟨fun i j => h₁ i j x hx, fun i j => h₂ i j x hx⟩

/-- The local subgroups from two fixed closed representations agree
outside one finite set, independently of their dimensions or bases. -/
theorem eventually_subgroup_eq (hρ : IsClosedSubgroup ρ) (hσ : IsClosedSubgroup σ) :
    ∀ᶠ v in cofinite, subgroup F G ρ v = subgroup F G σ v := by
  filter_upwards [eventually_subgroup_le F G ρ σ hρ,
    eventually_subgroup_le F G σ ρ hσ] with v h₁ h₂
  exact le_antisymm h₁ h₂

end LinearIntegralFamily

namespace FiniteTypeIntegralFamily

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The dimension of a fixed closed linear embedding of the affine group. -/
def dimension : ℕ :=
  (affineLinearEmbeddingStatement F G inferInstance inferInstance).choose

/-- A fixed closed linear embedding, chosen before any place, point or function. -/
def representation : MatrixRepresentation G (Fin (dimension F G)) :=
  (affineLinearEmbeddingStatement F G inferInstance inferInstance).choose_spec.choose

theorem isClosed_representation : IsClosedSubgroup (representation F G) :=
  (affineLinearEmbeddingStatement F G inferInstance inferInstance).choose_spec.choose_spec

variable [NumberField F]

local instance localPointsTopology (v : FinitePlace F) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (FiniteCompletion F v))

/-- The actual integral family obtained from the chosen closed representation. -/
def subgroup (v : FinitePlace F) :
    Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  LinearIntegralFamily.subgroup F G (representation F G) v

theorem isCompact_subgroup (v : FinitePlace F) :
    IsCompact (subgroup F G v :
      Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact LinearIntegralFamily.isCompact_subgroup F G (representation F G)
    (isClosed_representation F G) v

theorem eventually_projection_mem (x : FiniteAdelicGroupPoints F G) :
    ∀ᶠ v in cofinite,
      G.affinePointMap
        (CommAlgCat.ofHom
          ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
             commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x ∈
        subgroup F G v :=
  LinearIntegralFamily.eventually_projection_mem F G (representation F G) x

theorem eventually_uniform_integral (a : Γ(G.X.left, ⊤)) :
    ∀ᶠ v in cofinite,
      ∀ x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        x ∈ subgroup F G v →
          G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) x a ∈
            v.adicCompletionIntegers F :=
  LinearIntegralFamily.eventually_uniform_integral F G (representation F G)
    (isClosed_representation F G) a

/-- Every closed linear embedding gives the chosen family at almost all places. -/
theorem eventually_subgroup_eq {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) :
    ∀ᶠ v in cofinite, subgroup F G v = LinearIntegralFamily.subgroup F G ρ v :=
  LinearIntegralFamily.eventually_subgroup_eq F G (representation F G) ρ
    (isClosed_representation F G) hρ

end FiniteTypeIntegralFamily

end Langlands.Global
