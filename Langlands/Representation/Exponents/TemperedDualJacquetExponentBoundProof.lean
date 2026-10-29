import Langlands.Representation.Exponents.TemperedDualJacquetExponentBoundStatement
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof

/-!
# Proof of the weak opposite dual Jacquet exponent bound for tempered `GL_n`

An opposite dual exponent `ψ` along `C` of an irreducible tempered representation is a
generalized eigencharacter of the opposite Jacquet module, hence, after reversing the block
labels, an exponent of the upper Jacquet module along `C.reverse`. The upper bound on the
monotone chamber, proved from the product-Levi necessity theorem, applied to the reversed
tuple gives the bound on the antitone chamber.
-/

namespace Langlands

universe uF uV

/-- Every opposite Jacquet dual exponent of an irreducible tempered representation of `GL_n`
has absolute value at most one on block scalars whose normalized absolute values decrease
along the blocks. -/
theorem glTemperedDualJacquetExponentBound :
    GLTemperedDualJacquetExponentBoundStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn C A hirr htemp ψ hψ a ha
  have hadm : IsAdmissible A.ρ := htemp.isAdmissible
  have hgen := ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent T C A hirr hadm hψ
  have hJexp := ScalarLayer.isJacquetExponent_reverse T C A hψ.1 hgen
  have h := ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity
    glProductLeviTemperedExponentNecessity.{uF, uV} p F T n hn A A.ρ hirr htemp
    C.reverse _ hJexp (a ∘ Fin.rev) (fun i j hij => ha (Fin.rev_le_rev.mpr hij))
  have ha' : (a ∘ Fin.rev) ∘ Fin.rev = a := by
    funext k
    simp
  change ‖(ψ ((a ∘ Fin.rev) ∘ Fin.rev) : ℂ)‖ ≤ 1 at h
  rwa [ha'] at h

end Langlands
