import Langlands.Global.IntegralIwasawaFamilyStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Group.GL.IntegralSubgroup
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.AffinePointClosedImmersion
import Langlands.GroupScheme.GeneralLinearPointTopology
import Mathlib.Order.Filter.Finite

/-! # Integral families from actual closed linear embeddings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter MvPolynomial Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme

namespace LinearIntegralFamily

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  {N : ℕ} (ρ : MatrixRepresentation G (Fin N))

local instance localPointsTopology
    (H : GroupScheme (Spec (CommRingCat.of F))) (v : FinitePlace F) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of F (FiniteCompletion F v))

/-- The actual local points whose representation and inverse have integral entries. -/
def subgroup (v : FinitePlace F) :
    Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  (Langlands.GeneralLinearGroup.integralSubgroup (Fin N)
    (v.adicCompletionIntegers F).toSubring).comap
      (ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)))

theorem mem_subgroup (v : FinitePlace F)
    (x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :
    x ∈ subgroup F G ρ v ↔
      (∀ i j, ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) x i j ∈
        v.adicCompletionIntegers F) ∧
      (∀ i j, (ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) x)⁻¹ i j ∈
        v.adicCompletionIntegers F) :=
  Iff.rfl

/-- Every actual finite adelic point is integral in this fixed representation
away from finitely many places. -/
theorem eventually_projection_mem (x : FiniteAdelicGroupPoints F G) :
    ∀ᶠ v in cofinite,
      G.affinePointMap
        (CommAlgCat.ofHom
          ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
             commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x ∈
        subgroup F G ρ v := by
  let g := ρ.affineMatrix (CommAlgCat.of F (FiniteAdeles F)) x
  have h₁ : ∀ᶠ v in cofinite, ∀ i j : Fin N, g i j v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => (g i j).2
  have h₂ : ∀ᶠ v in cofinite, ∀ i j : Fin N, g⁻¹ i j v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => (g⁻¹ i j).2
  filter_upwards [h₁, h₂] with v h₁ h₂
  rw [mem_subgroup]
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom
      ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
         commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x
  change ρ.affineMatrix _ (G.affinePointMap _ x) =
    Matrix.GeneralLinearGroup.map _ g at h
  erw [h]
  exact ⟨h₁, h₂⟩

variable [IsAffine G.X.left]

/-- A closed representation makes its actual integral-point inverse image compact. -/
theorem isCompact_subgroup (hρ : IsClosedSubgroup ρ) (v : FinitePlace F) :
    IsCompact (subgroup F G ρ v :
      Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
    GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  have he := (GeneralLinear.affinePointsHomeomorph (Fin N) (CommRingCat.of F)
    (CommAlgCat.of F (FiniteCompletion F v))).isClosedEmbedding.comp
      (G.isClosedEmbedding_affinePointsTarget
        (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))
        (CommAlgCat.of F (FiniteCompletion F v)) ρ)
  exact he.isCompact_preimage
    (Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin N)
      (v.adicCompletionIntegers F).toSubring (isCompact_adicCompletionIntegers F v))

omit [IsAffine G.X.left] in
private theorem eventually_polynomial_integral
    (q : MvPolynomial (GeneralLinear.Coordinate (Fin N)) F) :
    ∀ᶠ v in cofinite,
      ∀ x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        x ∈ subgroup F G ρ v →
          aeval (GeneralLinear.values
            (ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) x)) q ∈
              v.adicCompletionIntegers F := by
  induction q using MvPolynomial.induction_on with
  | C c =>
      have hc : ∀ᶠ v in cofinite,
          algebraMap F (FiniteCompletion F v) c ∈ v.adicCompletionIntegers F :=
        (algebraMap F (FiniteAdeles F) c).2
      filter_upwards [hc] with v hv x hx
      simpa only [aeval_C] using hv
  | add q r hq hr =>
      filter_upwards [hq, hr] with v hq hr x hx
      rw [map_add]
      exact (v.adicCompletionIntegers F).toSubring.add_mem (hq x hx) (hr x hx)
  | mul_X q κ hq =>
      filter_upwards [hq] with v hq x hx
      rw [map_mul, aeval_X]
      apply (v.adicCompletionIntegers F).toSubring.mul_mem (hq x hx)
      cases κ with
      | entry i j => exact ((mem_subgroup F G ρ v x).mp hx).1 i j
      | inverseEntry i j => exact ((mem_subgroup F G ρ v x).mp hx).2 i j

omit [NumberField F] in
private theorem generalLinear_evaluation
    (A : CommAlgCat.{u} (CommRingCat.of F))
    (x : (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).affinePoints A)
    (a : Γ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left, ⊤)) :
    (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).affinePointEvaluation A x a =
      GeneralLinear.classify (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of F) A x)
        ((Scheme.ΓSpecIso
          (CommRingCat.of (GeneralLinear.CoordinateRing (Fin N) (CommRingCat.of F)))).hom a) := by
  conv_lhs => rw [← (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of F) A).symm_apply_apply x]
  rw [GeneralLinear.affinePointsEquiv_symm_apply,
    GeneralLinear.affinePointEvaluation_map_classify]

omit [IsAffine G.X.left] in
/-- Clearing the coefficients of a polynomial lift gives one exceptional set
for each regular function, uniformly over every member of each local subgroup. -/
theorem eventually_uniform_integral (hρ : IsClosedSubgroup ρ)
    (a : Γ(G.X.left, ⊤)) :
    ∀ᶠ v in cofinite,
      ∀ x : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        x ∈ subgroup F G ρ v →
          G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) x a ∈
            v.adicCompletionIntegers F := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
    GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  obtain ⟨b, hb⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2 a
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso
      (CommRingCat.of (GeneralLinear.CoordinateRing (Fin N) (CommRingCat.of F)))).hom b)
  filter_upwards [eventually_polynomial_integral F G ρ q] with v hv x hx
  rw [← hb, ← GroupScheme.affinePointEvaluation_postcomp]
  rw [generalLinear_evaluation F]
  rw [← hq]
  change GeneralLinear.classify _
    (GeneralLinear.quotient (Fin N) (CommRingCat.of F) q) ∈ _
  rw [GeneralLinear.classify_quotient]
  exact hv x hx

end LinearIntegralFamily

end Langlands.Global
