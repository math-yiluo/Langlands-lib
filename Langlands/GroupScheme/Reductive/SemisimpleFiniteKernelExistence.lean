import Langlands.GroupScheme.MatrixRepresentation.FactorSum
import Langlands.GroupScheme.MatrixRepresentation.ReindexedSemisimpleDirectSum
import Langlands.GroupScheme.Reductive.UnipotentPointKernel
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Semisimple representations with finite kernel of reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every connected reductive group over any field has a semisimple actual
finite-dimensional representation with finite scheme-theoretic kernel. -/
theorem IsConnectedReductive.exists_semisimple_finiteKernel
    (hG : IsConnectedReductive G) :
    ∃ (n : ℕ) (σ : MatrixRepresentation G (Fin n)),
      sSup {W : Submodule k (Fin n → k) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), σ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤ ∧ IsFinite (kernel σ).X.hom := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨N, ρ, hc⟩ := affineLinearEmbeddingStatement_viaCorepresented k G
    hG.isAffineHom (inferInstance : LocallyOfFiniteType G.X.hom)
  let F := simpleFactorFamily ρ
  let J := Σ i : Fin F.length, Fin (F.dimension i)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let σ := Chevalley.reindexRepresentation e (CommRingCat.of k) F.factorSum
  refine ⟨Fintype.card J, σ, semisimple_reindex_directSum F.factor F.simple e, ?_⟩
  apply hG.isFinite_of_normal_of_unipotentPointMatrices ρ hc (kernelι σ)
    (inferInstance : IsClosedImmersion (kernelι σ).hom.hom.left)
    (HopfPrimitive.isNormal_range_kernelι σ)
  intro T x
  rw [pointMatrix_restrict]
  apply F.isNilpotent_of_factorSum_pointMatrix_eq_one
  have hpoint : (x ≫ (kernelι σ).hom.hom) ≫ σ.hom.hom = 1 :=
    (kernelPointsEquiv σ T x).property
  have hσ : σ.pointMatrix T (x ≫ (kernelι σ).hom.hom) = 1 := by
    rw [pointMatrix_apply, hpoint, map_one]
  change (Chevalley.reindexRepresentation e (CommRingCat.of k) F.factorSum).pointMatrix T
    (x ≫ (kernelι σ).hom.hom) = 1 at hσ
  rw [Chevalley.reindexRepresentation_pointMatrix] at hσ
  apply Units.ext
  ext a b
  have hh := congrArg (fun M : GL (Fin (Fintype.card J)) Γ(T.left, ⊤) => M (e a) (e b)) hσ
  simpa only [Chevalley.reindexGL_apply, Equiv.symm_apply_apply,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, e.injective.eq_iff] using hh

end Langlands.GroupScheme
