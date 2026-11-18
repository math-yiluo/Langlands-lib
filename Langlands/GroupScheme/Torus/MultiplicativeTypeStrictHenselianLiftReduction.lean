import Langlands.GroupScheme.Torus.CompleteLocalResidueLift
import Langlands.GroupScheme.Torus.HenselianClopenTransfer
import Langlands.GroupScheme.Torus.PrescribedDiagonalizableLift
import Langlands.GroupScheme.Descent.SplitResidueNoetherianModel
import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianLiftStatement

/-! # Strictly Henselian lifting from complete-local deformation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.HomScheme Langlands.GroupScheme.HomScheme.FiniteSource

namespace Langlands.GroupScheme.StrictHenselianLiftReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem specMap_comp {P E B A : Type u} [CommRing P]
    [CommRing E] [Algebra P E] [CommRing B] [Algebra P B]
    [CommRing A] [Algebra P A] (f : E →ₐ[P] B) (g : B →ₐ[P] A) :
    specMap g ≫ specMap f = specMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- A split-special-fibre noetherian local model with etale approximation
has a clopen diagonalizable lift over any Henselian local algebra. -/
theorem exists_clopen_over_henselian
    (hComplete : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    {P A : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [CommRing A] [HenselianLocalRing A] [Algebra P A] [IsLocalHom (algebraMap P A)]
    (happrox : Langlands.CommutativeAlgebra.EtaleCompletionApproximation P)
    (D : GroupScheme (Spec (CommRingCat.of P)))
    [IsAffineHom D.X.hom] [Flat D.X.hom] [LocallyOfFinitePresentation D.X.hom]
    (hD : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap P (IsLocalRing.ResidueField P))).obj D)) :
    ∃ C : GroupScheme (Spec (CommRingCat.of A)),
      RelativeMultiplicativeType.IsDiagonalizable C ∧
      ∃ j : C ⟶ (baseChange (Spec.algebraMap P A)).obj D,
        IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left ∧
          IsIso ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j) := by
  obtain ⟨N, _, _, ⟨eD⟩⟩ := hD
  let C := (Diagonalizable.groupScheme (CommRingCat.of P) N).toGrp
  have hC : RelativeMultiplicativeType.IsDiagonalizable C :=
    Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of P) N
  have : IsAffineHom C.X.hom := by
    change IsAffineHom (Diagonalizable.groupScheme (CommRingCat.of P) N).X.hom
    infer_instance
  let sp := Spec.algebraMap P (IsLocalRing.ResidueField P)
  let e₀ : (baseChange sp).obj C ≅ (baseChange sp).obj D :=
    Diagonalizable.baseChangeIso sp N ≪≫
      Diagonalizable.relativeModelIso (CommRingCat.of (IsLocalRing.ResidueField P)) N ≪≫ eD.symm
  have hDmt : RelativeMultiplicativeType.IsMultiplicativeType ((baseChange sp).obj D) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      ⟨N, inferInstance, inferInstance, ⟨eD⟩⟩
  obtain ⟨E, _, _, hE, ι, j, hj⟩ :=
    CompleteLocalResidueLift.exists_etale_lift hComplete P happrox C D hC hDmt e₀.hom
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing P E
  let k := IsLocalRing.ResidueField A
  let α : IsLocalRing.ResidueField P →ₐ[P] k :=
    IsScalarTower.toAlgHom P (IsLocalRing.ResidueField P) k
  let φ₀ : E →ₐ[P] IsLocalRing.ResidueField P :=
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal P)).comp ι
  let φ : E →ₐ[P] k := α.comp φ₀
  have : IsIso (evaluate (specMap φ₀) j) := by
    rw [hj]
    infer_instance
  have hφeval : evaluate (specMap φ) j =
      evaluate (specMap α) (evaluate (specMap φ₀) j) := by
    rw [← evaluate_comp, specMap_comp]
  have : IsIso (evaluate (specMap φ) j) := by
    rw [hφeval]
    exact (LocalClopenFibre.isIso_evaluate_iff (specMap α)
      (evaluate (specMap φ₀) j)).mpr inferInstance
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  obtain ⟨σ, hσ, hop, hcl⟩ :=
    HenselianClopenTransfer.exists_clopen_evaluation C D hC j φ IsLocalRing.residue_surjective
  let jA := evaluate (specMap σ) j
  let r : A →ₐ[P] k := (Algebra.ofId A k).restrictScalars P
  have hres : evaluate (specMap r) jA = evaluate (specMap φ) j := by
    dsimp only [jA, r]
    rw [← evaluate_comp, specMap_comp, hσ]
  have : IsIso (evaluate (specMap r) jA) := by rw [hres]; infer_instance
  have hspecial : IsIso ((baseChange (Spec.algebraMap A k)).map jA) :=
    (LocalClopenFibre.isIso_evaluate_iff (specMap r) jA).mp inferInstance
  exact ⟨(baseChange (Spec.algebraMap P A)).obj C, hC.baseChange _, jA, hop, hcl, hspecial⟩

/-- The exact strictly Henselian clopen-lifting proposition follows from the
complete-local deformation proposition, with all other inputs discharged. -/
theorem multiplicativeTypeStrictHenselianLift_of_completeLocalDeformation
    (hComplete : MultiplicativeTypeCompleteLocalDeformationStatement.{u}) :
    MultiplicativeTypeStrictHenselianLiftStatement.{u} := by
  intro A _ _ _ H _ _ _ _ M _ _ _sp e
  let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
  let C₀ := RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of A)) M
  have hC₀ : RelativeMultiplicativeType.IsDiagonalizable C₀ :=
    ⟨M, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hSpecial : RelativeMultiplicativeType.IsDiagonalizable ((baseChange sp).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso e.symm (hC₀.baseChange sp)
  obtain ⟨d⟩ := Descent.SplitResidueNoetherianModel.nonempty_model H hSpecial
  let P := Localization.AtPrime d.prime.asIdeal
  have : IsNoetherianRing P := d.noetherian
  have : IsLocalHom (algebraMap P A) := d.localMap
  have : IsAffineHom d.group.X.hom := d.affine
  have : Flat d.group.X.hom := d.flat
  have : LocallyOfFinitePresentation d.group.X.hom := d.finitePresentation
  obtain ⟨C₁, hC₁, j₁, hop, hcl, hspecial⟩ :=
    exists_clopen_over_henselian hComplete (A := A) d.approximation d.group d.specialSplit
  let jH : C₁ ⟶ H := j₁ ≫ d.iso.inv
  have hopH : IsOpenImmersion jH.hom.hom.left := by
    change IsOpenImmersion (j₁.hom.hom.left ≫ d.iso.inv.hom.hom.left)
    infer_instance
  have hclH : IsClosedImmersion jH.hom.hom.left := by
    change IsClosedImmersion (j₁.hom.hom.left ≫ d.iso.inv.hom.hom.left)
    infer_instance
  have : IsIso ((baseChange sp).map jH) := by
    dsimp only [jH]
    rw [Functor.map_comp]
    infer_instance
  exact PrescribedDiagonalizableLift.reparametrize_clopen_lift hC₀ hC₁ jH hopH hclH e

end Langlands.GroupScheme.StrictHenselianLiftReduction
