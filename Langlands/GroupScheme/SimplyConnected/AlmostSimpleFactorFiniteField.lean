import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof

/-! # Finite fields fixing actual almost-simple factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Langlands.AlgebraicGeometry.Picard
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- The endomorphism of the original group projecting onto one actual factor. -/
def factorEndomorphism (i : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  D.projection i ≫ D.inclusion i

/-- The factor endomorphism is an actual idempotent. -/
@[simp] theorem factorEndomorphism_idempotent (i : D.Index) :
    D.factorEndomorphism i ≫ D.factorEndomorphism i =
      D.factorEndomorphism i := by
  simp only [factorEndomorphism, Category.assoc]
  rw [← Category.assoc (D.inclusion i) (D.projection i),
    inclusion_projection, Category.id_comp]

/-- The range of the idempotent is exactly the factor on every test scheme. -/
theorem range_factorEndomorphism (i : D.Index) :
    SubgroupFunctor.range (D.factorEndomorphism i) =
      SubgroupFunctor.range (D.inclusion i) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (D.projection i).hom.hom, ?_⟩
    change (y ≫ (D.projection i).hom.hom) ≫ (D.inclusion i).hom.hom =
      y ≫ (D.projection i ≫ D.inclusion i).hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (D.inclusion i).hom.hom, ?_⟩
    change (y ≫ (D.inclusion i).hom.hom) ≫
      (D.projection i ≫ D.inclusion i).hom.hom = y ≫ (D.inclusion i).hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc, inclusion_projection_points_self]

variable [Algebra.IsAlgebraic k L]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- A finite field model of the actual projection endomorphism. -/
def factorHomModel (i : D.Index) :
    Descent.FiniteStage.HomModel k L (D.factorEndomorphism i) :=
  Descent.FiniteStage.homModel k L (D.factorEndomorphism i)

/-- A finite intermediate field whose pointwise fixer stabilizes the factor. -/
def factorFieldOfDefinition (i : D.Index) : FinIntermediateField k L :=
  (D.factorHomModel i).fieldOfDefinition

variable [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]

/-- Every automorphism fixing the finite endomorphism-model field fixes the
actual factor index. This provides the finite field required for continuity. -/
theorem galoisFactorIndex_eq_of_fixes (i : D.Index) (σ : L ≃ₐ[k] L)
    (hσ : ∀ x ∈ (D.factorFieldOfDefinition i).1, σ x = x) :
    D.galoisFactorIndex σ i = i := by
  let M := D.factorHomModel i
  have hdesc := LatticeGaloisContinuity.descent_comm_of_model
    M.fieldOfDefinition M.hom (D.factorEndomorphism i) M.recovery σ hσ
  let e := descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G
  apply D.range_inclusion_injective
  change SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex σ i)) =
    SubgroupFunctor.range (D.inclusion i)
  calc
    _ = SubgroupFunctor.galoisTransport k L G σ
        (SubgroupFunctor.range (D.inclusion i)) :=
      D.range_inclusion_galoisFactorIndex σ i
    _ = SubgroupFunctor.galoisTransport k L G σ
        (SubgroupFunctor.range (D.factorEndomorphism i)) := by
      rw [range_factorEndomorphism]
    _ = SubgroupFunctor.range
        ((GroupScheme.baseChange (galoisBaseMap k L σ)).map
          (D.factorEndomorphism i) ≫ e.hom) :=
      SubgroupFunctor.descentTransport_range _ _ _ _ _
    _ = SubgroupFunctor.range (e.hom ≫ D.factorEndomorphism i) :=
      congrArg SubgroupFunctor.range hdesc
    _ = SubgroupFunctor.range (D.factorEndomorphism i) :=
      SubgroupFunctor.range_iso_comp e _
    _ = SubgroupFunctor.range (D.inclusion i) := D.range_factorEndomorphism i

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
