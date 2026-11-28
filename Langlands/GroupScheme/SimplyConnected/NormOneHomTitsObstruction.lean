import Langlands.GroupScheme.SimplyConnected.NormOneTitsAlgebra
import Langlands.GroupScheme.Reductive.TitsMaximalWeight
import Langlands.GroupScheme.Reductive.TitsIndexSplitRankProof
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # The Brauer class of a maximal weight in a norm-one chart -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

open Langlands.CentralSimple Langlands.Brauer MatrixRepresentation TitsDescent
open Langlands.Algebra.GaloisTwistedMatrix

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (A : CSA.{u, u} k)

private theorem range_le_normOne (hG : IsSemisimple G)
    (f : G ⟶ CentralSimpleUnits.groupScheme k A) :
    SubgroupFunctor.range f ≤ SubgroupFunctor.range (normOneι k A) := by
  have h : f ≫ reducedNormHom k A = 1 := congrArg Additive.toMul
    (hG.subsingleton_rationalCharacters.elim (Additive.ofMul (f ≫ reducedNormHom k A)) 0)
  intro U _ hU
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hU
  apply (mem_range_kernelι_iff (reducedNormHom k A) _).mpr
  rw [Category.assoc, ← Grp.comp_hom_hom, h]
  exact MonObj.comp_one x

/-- A morphism from a semisimple group to the units of a central simple
algebra has trivial reduced norm. -/
def normOneLift (hG : IsSemisimple G) (f : G ⟶ CentralSimpleUnits.groupScheme k A) :
    G ⟶ normOne k A :=
  (show (SubgroupFunctor.range (normOneι k A)).IsRepresentedBy (normOneι k A) from
    ⟨by change Mono (kernelι (reducedNormHom k A)).hom.hom; infer_instance, rfl⟩).factorHom
      f (range_le_normOne A hG f)

@[simp] theorem normOneLift_comp (hG : IsSemisimple G)
    (f : G ⟶ CentralSimpleUnits.groupScheme k A) :
    normOneLift A hG f ≫ normOneι k A = f :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {L : Type u} [Field L] [Algebra k L] [IsGalois k L]
  (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) L)
  (d : GaloisPinningData k L G) (hG : IsSimplyConnected G)
  (w : d.starFixedWeights) (f : G ⟶ normOne k A)

local notation "I" => Fin (reducedDegree k A)

/-- In the dual of the column chart pulled back along a morphism to the
norm-one group, a star-fixed maximal weight of multiplicity one has the
class of the opposite algebra. -/
def NormOneHomDualTitsObstructionStatement : Prop :=
  let r := (dual (representation k A e)).restrict
    ((GroupScheme.baseChange (algebraBaseMap k L)).map f)
  Module.finrank L (d.toSplitPinning.representationWeightSpace r w.val) = 1 →
  (∀ χ, d.toSplitPinning.representationWeightSpace r χ ≠ ⊥ →
    χ - w.val ∈ d.toSplitPinning.positiveRootMonoid → χ = w.val) →
  d.titsObstruction hG w = -classOf A

theorem normOneHomDualTitsObstruction :
    NormOneHomDualTitsObstructionStatement A e d hG w f := by
  classical
  unfold NormOneHomDualTitsObstructionStatement
  intro r hm hmax
  let : Nonempty I := ⟨⟨0, reducedDegree_pos k A⟩⟩
  let P (σ : L ≃ₐ[k] L) : Matrix I I L := (dualConjugator e σ).val
  have hP : ∀ σ, r.Intertwines (galoisTwist σ r) (P σ) :=
    fun σ => intertwines_restrict_galoisTwist σ (dual_intertwines_galoisTwist A e σ) f
  let B := (matrixAction (oppositeChart e)).fixed
  have hB : B = twistedFixed P := by
    ext X
    exact mem_oppositeFixed_iff_dualConjugator e X
  have hmem (y : L ⊗[k] Aᵐᵒᵖ) :
      oppositeChart e y ∈ Submodule.span L (B : Set (Matrix I I L)) := by
    induction y using TensorProduct.inductionOn with
    | tmul l a =>
      have hh : l • ((1 : L) ⊗ₜ[k] a) = l ⊗ₜ[k] a := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [← hh, map_smul]
      apply Submodule.smul_mem
      have ha : oppositeChart e ((1 : L) ⊗ₜ[k] a) ∈ B :=
        (fixedHom (oppositeChart e) a).property
      exact Submodule.subset_span ha
    | add _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  have hspan : Submodule.span L (B : Set (Matrix I I L)) = ⊤ := by
    rw [eq_top_iff]
    intro X _
    exact (oppositeChart e).apply_symm_apply X ▸ hmem ((oppositeChart e).symm X)
  have hPu (σ : L ≃ₐ[k] L) : IsUnit (P σ) := (dualConjugator e σ).isUnit
  rw [d.titsObstruction_apply,
    d.titsObstructionValue_of_maximal (d.corootSpan_eq_top_of_simplyConnected hG)
    P hP hPu B hB.le hspan ((titsAlgebra_le_twistedFixed _ hP).trans hB.ge)
    (d.isStarFixedWeight_of_mem_starFixedWeights w.property) hm hmax]
  rw [← classOf_opposite A]
  exact classOf_eq_of_algEquiv (fixedEquivOfIsGalois (oppositeChart e)).symm

end Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation
