import Langlands.GroupScheme.MatrixRepresentation.CompositionFactors
import Langlands.GroupScheme.MatrixRepresentation.DirectSum
import Langlands.GroupScheme.MatrixRepresentation.UnipotentPointMatrices
import Langlands.GroupScheme.AffineKernelQuotient
import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient

/-! # The finite map supplied by actual simple factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.SimpleFactorFamily

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} {N M : ℕ}
  {ρ : MatrixRepresentation G (Fin N)} {τ : MatrixRepresentation G (Fin M)}
  (F : SimpleFactorFamily ρ τ)

/-- The direct sum of the chosen actual simple factors. -/
def factorSum : MatrixRepresentation G (Σ i : Fin F.length, Fin (F.dimension i)) :=
  directSum F.factor

/-- Triviality of the factor sum detects precisely the common all-test kernel. -/
theorem factorSum_pointMatrix_eq_one_iff
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    F.factorSum.pointMatrix T x = 1 ↔ ∀ i, (F.factor i).pointMatrix T x = 1 :=
  directSum_pointMatrix_eq_one_iff F.factor T x

/-- On the common kernel the original quotient representation acts unipotently. -/
theorem isNilpotent_of_factorSum_pointMatrix_eq_one
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (hx : F.factorSum.pointMatrix T x = 1) :
    IsNilpotent ((τ.pointMatrix T x : Matrix (Fin M) (Fin M) Γ(T.left, ⊤)) - 1) :=
  ⟨F.length, F.nilpotent T x ((F.factorSum_pointMatrix_eq_one_iff T x).mp hx)⟩

/-- Every group homomorphism killed by the factor sum acts unipotently in the
original quotient representation on all scheme tests. -/
theorem hasUnipotentPointMatrices_restrict (i : H ⟶ G)
    (hi : i ≫ F.factorSum = 0) :
    (τ.restrict i).HasUnipotentPointMatrices := by
  intro T x
  rw [pointMatrix_restrict]
  apply F.isNilpotent_of_factorSum_pointMatrix_eq_one
  rw [pointMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, hi]
  change GeneralLinear.pointsEquiv _ _ T (x ≫ 1) = 1
  rw [MonObj.comp_one, map_one]

section Finiteness

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {ρ : MatrixRepresentation G (Fin N)} (F : SimpleFactorFamily ρ ρ)

/-- With trivial ambient unipotent radical and a closed faithful original
representation, the simple-factor sum is a finite morphism, even if its
scheme-theoretic kernel is not smooth. -/
theorem isFinite_factorSum (hG : HasTrivialUnipotentRadical G)
    (hc : IsClosedSubgroup ρ) : IsFinite F.factorSum.hom.hom.left := by
  let σ := F.factorSum
  let L := GeneralLinear.groupScheme (Σ i : Fin F.length, Fin (F.dimension i))
    (CommRingCat.of k)
  have : Smooth L.X.hom := GeneralLinear.smoothStatement _ _
  let q : G ⟶ AffineHomImage.image σ := AffineHomImage.projection σ
  obtain ⟨hs, hf, hsurj, hl, hqc⟩ := AffineHomImage.projection_geometry σ
  have : Flat q.hom.hom.left := hf
  have : Surjective q.hom.hom.left := hsurj
  have : QuasiCompact q.hom.hom.left := hqc
  have hk : kernelι q ≫ σ = 0 :=
    AffineQuotient.kernelι_comp_eq_zero
      (AffineHomImage.kernel_range_projection σ).le
  have hU : (ρ.restrict (kernelι q)).HasUnipotentPointMatrices :=
    F.hasUnipotentPointMatrices_restrict (kernelι q) hk
  have : IsFinite (kernel q).X.hom :=
    isFinite_of_normal_of_unipotentPointMatrices hG ρ hc (kernelι q)
      (inferInstance : IsClosedImmersion (kernelι q).hom.hom.left)
      (HopfPrimitive.isNormal_range_kernelι q) hU
  have : IsFinite q.hom.hom.left := isFinite_of_finite_kernel q
  have hσ : σ = q ≫ AffineHomImage.inclusion σ :=
    (AffineHomImage.projection_inclusion σ).symm
  change IsFinite σ.hom.hom.left
  rw [hσ, Grp.comp_hom_hom, Over.comp_left]
  infer_instance

end Finiteness

end Langlands.GroupScheme.MatrixRepresentation.SimpleFactorFamily
