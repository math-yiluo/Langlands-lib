import Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorStatement
import Langlands.GroupScheme.OrthogonalMatrix.CoverNumberedWeights
import Langlands.GroupScheme.OrthogonalMatrix.CoverVectorBasis

/-! # Numbered vector eigenbasis of an aligned split orthogonal cover -/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {k : Type u} [Field k] {n : ℕ}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : SplitPinning G} {e : p.base.support ≃ Fin n}
  {pi : G ⟶ identityComponent (groupScheme (Fin n) (CommRingCat.of k))}
  {tr : StandardTorusTransport p.inclusion pi}

namespace CoverNumberedWeights

variable (w : CoverNumberedWeights p e tr.torusMap)

/-- Reverse the weight sign for the inverse-right action and apply the stored
signed coordinate permutation. -/
def inverseRightIndexEquiv : (Fin n × ℤˣ) ≃ (Fin n ⊕ Fin n) :=
  (Equiv.prodShear w.permutation (fun i => Equiv.mulRight (-w.sign i))).trans
    signedWeightIndexEquiv

theorem neg_weightChar_inverseRightIndexEquiv (a : Fin n × ℤˣ) :
    -weightChar (Fin n) k (w.inverseRightIndexEquiv a) =
      (a.2 : ℤ) • w.standard a.1 := by
  rw [inverseRightIndexEquiv, Equiv.trans_apply, weightChar_signedWeightIndexEquiv]
  change -(((a.2 * -w.sign a.1 : ℤˣ) : ℤ) •
      weightChar (Fin n) k (Sum.inl (w.permutation a.1))) = _
  simp [w.standard_eq, smul_smul]

/-- The numbered characters act on one base-field basis over every coefficient
algebra, with the inverse-right row convention of the target. -/
theorem exists_eigenbasis [Nontrivial (Fin n)] :
    ∃ b : Basis (Fin n × ℤˣ) k ((Fin n ⊕ Fin n) → k),
      ∀ (R : CommAlgCat.{u} (CommRingCat.of k))
        (t : GroupScheme.affinePoints p.torus.toGrp R) (a : Fin n × ℤˣ),
        Matrix.vecMul (fun j => algebraMap k R (b a j))
            ((MatrixRepresentation.affineMatrix
              (pi ≫ identityComponentι (groupScheme (Fin n) (CommRingCat.of k)) ≫
                inclusion (Fin n) (CommRingCat.of k)) R (t ≫ p.inclusion.hom.hom))⁻¹ :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
          fun j => ((Gm.affineUnitsEquiv (CommRingCat.of k) R
            (t ≫ (CommGroupScheme.groupHom ((a.2 : ℤ) • w.weight a.1)).hom.hom) : Rˣ) : R) *
              algebraMap k R (b a j) := by
  obtain ⟨b, hb⟩ := tr.exists_inverseRight_eigenbasis
  refine ⟨b.reindex w.inverseRightIndexEquiv.symm, ?_⟩
  intro R t a
  have hchar : tr.torusMap ≫ (-weightChar (Fin n) k (w.inverseRightIndexEquiv a)) =
      (a.2 : ℤ) • w.weight a.1 := by
    rw [w.neg_weightChar_inverseRightIndexEquiv, Preadditive.comp_zsmul, w.pullback]
  have hvalue : (Lie.characterValue ((a.2 : ℤ) • w.weight a.1) t : R) =
      (Gm.affineUnitsEquiv (CommRingCat.of k) R
        (t ≫ (CommGroupScheme.groupHom ((a.2 : ℤ) • w.weight a.1)).hom.hom) : R) := by
    dsimp only [Lie.characterValue, Gm.affineUnitsEquiv, Gm.affinePointsEquiv]
    rfl
  simpa only [Basis.reindex_apply, Equiv.symm_symm, hchar, hvalue,
    Matrix.GeneralLinearGroup.coe_inv] using hb R t (w.inverseRightIndexEquiv a)

end CoverNumberedWeights

/-- The exact numbered vector statement, for every field and supplied aligned
simply connected cover. -/
theorem numberedCoverVector : NumberedCoverVectorStatement.{u} := by
  intro k _ n hn
  dsimp only
  intro G _ p hG pi hpi e hcartan halign
  let : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  let tr := standardTorusTransport p.isConnectedReductive p.isSplitTorus
    p.inclusion p.isMaximalTorus pi hpi
  let w := coverNumberedWeights p hn hG hpi e hcartan halign tr
  refine ⟨w.weight, w.chain, w.last, ?_, w.exists_eigenbasis⟩
  intro i j hij s t
  exact CoverNumberedWeights.signed_roots (p := p) (w := w)
    (coverRootCoordinates p hn hpi tr) i j hij s t

end Langlands.GroupScheme.OrthogonalMatrix
