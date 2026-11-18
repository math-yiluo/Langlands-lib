import Langlands.CommutativeAlgebra.EtaleCompletionApproximation
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.GroupScheme.HomScheme.FiniteSourceHom

/-! # Etale approximation of actual homomorphisms into a completion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.HomScheme Langlands.GroupScheme.HomScheme.FiniteSource

namespace Langlands.GroupScheme.Descent.EtaleHomApproximation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {P : Type u} [CommRing P] [IsLocalRing P]
  {C D : GroupScheme (Spec (CommRingCat.of P))}
  [QuasiCompact C.X.hom] [QuasiSeparated C.X.hom]
  [LocallyOfFinitePresentation D.X.hom]

/-- A completed homomorphism has an etale approximation with exactly the
same special-fibre homomorphism. -/
theorem exists_approximation
    (happrox : Langlands.CommutativeAlgebra.EtaleCompletionApproximation P)
    (f : RelativeHom C D (specOver P (AdicCompletion (IsLocalRing.maximalIdeal P) P))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra P E), Algebra.Etale P E ∧
      ∃ (ι : E →ₐ[P] AdicCompletion (IsLocalRing.maximalIdeal P) P)
        (j : RelativeHom C D (specOver P E)),
        evaluate (specMap ((AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp ι)) j =
          evaluate (specMap (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P))) f := by
  let Pc := AdicCompletion (IsLocalRing.maximalIdeal P) P
  obtain ⟨T, hT, -, g, hg⟩ := FiniteCoefficient.homGeneral P Pc C D f ∅
  have : Algebra.FiniteType P T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hgf : evaluate (specMap T.val) g = f := by
    have hc : Spec.algebraMap T Pc ≫ Spec.algebraMap P T = Spec.algebraMap P Pc := by
      rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    change (pullbackComparison (Spec.algebraMap P T) (Spec.algebraMap T Pc)
      (Spec.algebraMap P Pc) hc C).inv ≫
      (baseChange (Spec.algebraMap T Pc)).map g ≫
      (pullbackComparison (Spec.algebraMap P T) (Spec.algebraMap T Pc)
        (Spec.algebraMap P Pc) hc D).hom = f
    rw [hg, Iso.inv_hom_id_assoc]
  obtain ⟨E, _, _, hE, a, ι, ha⟩ := happrox T T.val 1
  have hres : ((AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp ι).comp a =
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp T.val := by
    ext x
    have h := congrArg (Ideal.Quotient.factor
      (show IsLocalRing.maximalIdeal P ^ 1 ≤ IsLocalRing.maximalIdeal P by simp))
      (AlgHom.congr_fun ha x)
    simpa only [AlgHom.comp_apply, AdicCompletion.factorₐ_evalₐ_one] using h
  refine ⟨E, inferInstance, inferInstance, hE, ι, evaluate (specMap a) g, ?_⟩
  rw [← evaluate_comp, ← hgf, ← evaluate_comp]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      ((AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp ι).toRingHom) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom T.val.toRingHom)
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun k : T →ₐ[P] IsLocalRing.ResidueField P =>
    Spec.map (CommRingCat.ofHom k.toRingHom)) hres

end Langlands.GroupScheme.Descent.EtaleHomApproximation
