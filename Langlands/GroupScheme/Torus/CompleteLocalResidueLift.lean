import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationStatement
import Langlands.GroupScheme.Descent.EtaleHomApproximation
import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Langlands.GroupScheme.HomScheme.FiniteSourceHom
import Langlands.GroupScheme.HomScheme.ConjugationMap
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing

/-! # Complete-local lifting with an arbitrary field quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.HomScheme Langlands.GroupScheme.HomScheme.FiniteSource

namespace Langlands.GroupScheme.CompleteLocalResidueLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The complete-local deformation statement applies to any supplied field
quotient, with exact recovery along its actual structure map. -/
theorem exists_lift_of_field_quotient
    (hComplete : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (K : Type u) [Field K] [Algebra B K]
    (hK : Function.Surjective (algebraMap B K))
    (C D : GroupScheme (Spec (CommRingCat.of B)))
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] [Flat D.X.hom]
    (hC : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of B)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((baseChange p).obj C))
    (hD : RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (Spec.algebraMap B K)).obj D))
    (f₀ : RelativeHom C D (specOver B K)) :
    ∃ f : C ⟶ D, (baseChange (Spec.algebraMap B K)).map f = f₀ := by
  let e : IsLocalRing.ResidueField B ≃ₐ[B] K :=
    Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison.residueCoverEquiv hK
  let a : specOver B K ≅ specOver B (IsLocalRing.ResidueField B) :=
    (algSpec (CommRingCat.of B)).mapIso (CommAlgCat.isoMk e).op
  have hD' : RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj D) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_iso
      (Descent.pullbackComparison (Spec.algebraMap B K) a.inv.left _ (Over.w a.inv) D).symm
      (hD.baseChange a.inv.left)
  obtain ⟨f, hf, -⟩ := (hComplete B D C hC hD').1 (evaluate a.inv f₀)
  refine ⟨f, ?_⟩
  have h := congrArg (evaluate a.hom) hf
  rw [← evaluate_comp, a.hom_inv_id, evaluate_id] at h
  exact (evaluate_baseChange a.hom f).symm.trans h

/-- Lift a prescribed special-fibre homomorphism to the completion of the
original noetherian local base, keeping its original residue field. -/
theorem exists_completed_lift
    (hComplete : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    (C D : GroupScheme (Spec (CommRingCat.of P)))
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] [Flat D.X.hom]
    (hC : RelativeMultiplicativeType.IsDiagonalizable C)
    (hD : RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (Spec.algebraMap P (IsLocalRing.ResidueField P))).obj D))
    (f₀ : RelativeHom C D (specOver P (IsLocalRing.ResidueField P))) :
    ∃ f : RelativeHom C D (specOver P (AdicCompletion (IsLocalRing.maximalIdeal P) P)),
      evaluate (specMap (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P))) f = f₀ := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal P) P
  have : IsNoetherianRing B := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  let K := IsLocalRing.ResidueField P
  let ρ : B →ₐ[P] K := AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)
  let : Algebra B K := ρ.toRingHom.toAlgebra
  let p := Spec.algebraMap P B
  let r : specOver P K ⟶ specOver P B := specMap ρ
  let Cb := (baseChange p).obj C
  let Db := (baseChange p).obj D
  have : IsAffineHom Db.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd D.X.hom p)
    infer_instance
  have : LocallyOfFiniteType Db.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.X.hom p)
    infer_instance
  have : Flat Db.X.hom := by
    change Flat (CategoryTheory.Limits.pullback.snd D.X.hom p)
    infer_instance
  let cC := Descent.pullbackComparison p r.left (specOver P K).hom (Over.w r) C
  let cD := Descent.pullbackComparison p r.left (specOver P K).hom (Over.w r) D
  have hCb : ∃ (S' : Scheme.{u}) (q : S' ⟶ Spec (CommRingCat.of B)),
      IsFinite q ∧ Etale q ∧ Surjective q ∧
        RelativeMultiplicativeType.IsDiagonalizable ((baseChange q).obj Cb) :=
    ⟨Spec (CommRingCat.of B), 𝟙 _, inferInstance, inferInstance, inferInstance,
      (hC.baseChange p).baseChange (𝟙 _)⟩
  have hDb : RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (Spec.algebraMap B K)).obj Db) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_iso cD hD
  obtain ⟨f, hf⟩ := exists_lift_of_field_quotient hComplete B K
    (AdicCompletion.evalOneₐ_surjective (IsLocalRing.maximalIdeal P)) Cb Db hCb hDb
    (cC.hom ≫ f₀ ≫ cD.inv)
  refine ⟨f, ?_⟩
  change cC.inv ≫ (baseChange (Spec.algebraMap B K)).map f ≫ cD.hom = f₀
  rw [hf]
  simp

/-- Etale approximation algebraizes a completed lift while preserving the
prescribed special-fibre homomorphism exactly. -/
theorem exists_etale_lift
    (hComplete : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    (happrox : Langlands.CommutativeAlgebra.EtaleCompletionApproximation P)
    (C D : GroupScheme (Spec (CommRingCat.of P)))
    [QuasiCompact C.X.hom] [QuasiSeparated C.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFinitePresentation D.X.hom] [Flat D.X.hom]
    (hC : RelativeMultiplicativeType.IsDiagonalizable C)
    (hD : RelativeMultiplicativeType.IsMultiplicativeType
      ((baseChange (Spec.algebraMap P (IsLocalRing.ResidueField P))).obj D))
    (f₀ : RelativeHom C D (specOver P (IsLocalRing.ResidueField P))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra P E), Algebra.Etale P E ∧
      ∃ (ι : E →ₐ[P] AdicCompletion (IsLocalRing.maximalIdeal P) P)
        (j : RelativeHom C D (specOver P E)),
        evaluate (specMap ((AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp ι)) j = f₀ := by
  obtain ⟨f, hf⟩ := exists_completed_lift hComplete P C D hC hD f₀
  obtain ⟨E, _, _, hE, ι, j, hj⟩ :=
    Descent.EtaleHomApproximation.exists_approximation happrox f
  exact ⟨E, inferInstance, inferInstance, hE, ι, j, hj.trans hf⟩

end Langlands.GroupScheme.CompleteLocalResidueLift
