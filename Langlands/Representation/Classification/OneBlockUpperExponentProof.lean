import Langlands.Representation.Classification.OneBlockUpperExponentStatement
import Langlands.Representation.Geometric.SingleBlockJacquetTransport
import Langlands.Group.GL.SingleBlock

/-!
# Upper exponent bounds of `GL_n` on the single-block product Levi

Proof of `GLOneBlockUpperExponentStatement`. Evaluation at the unique block is
the actual block-diagonal embedding of the single-block Levi, so the published
single-block normalized Jacquet comparison identifies every refined generalized
exponent with an ordinary Jacquet exponent and the blockwise chamber with the
ordinary one.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Evaluation at the unique block is the block-diagonal embedding of the
single-block Levi. -/
theorem ScalarLayer.oneBlockLeviEquiv_toMonoidHom {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) :
    (ScalarLayer.oneBlockLeviEquiv T hn).toMonoidHom =
      (CuspidalSupport.LeviAdmissibility.oneBlock n hn).leviEmbedding F.Carrier := by
  have hC : (CuspidalSupport.LeviAdmissibility.oneBlock n hn).length = 1 := rfl
  refine MonoidHom.ext fun m => Units.ext (Matrix.ext fun x y => ?_)
  have hx : (CuspidalSupport.LeviAdmissibility.oneBlock n hn).index
      ((CuspidalSupport.LeviAdmissibility.oneBlock n hn).singleBlockIndex hC) x = x :=
    Fin.ext (BlockShape.singleBlock_index_val _ hC _ x)
  have hy : (CuspidalSupport.LeviAdmissibility.oneBlock n hn).index
      ((CuspidalSupport.LeviAdmissibility.oneBlock n hn).singleBlockIndex hC) y = y :=
    Fin.ext (BlockShape.singleBlock_index_val _ hC _ y)
  have h := (CuspidalSupport.LeviAdmissibility.oneBlock n hn).leviEmbedding_apply_same
    F.Carrier m ((CuspidalSupport.LeviAdmissibility.oneBlock n hn).singleBlockIndex hC) x y
  rw [hx, hy] at h
  exact h.symm

/-- The ordinary upper exponent bounds of an admissible representation of
`GL_n(F)` give the refined upper exponent hypothesis on the single-block Levi. -/
theorem glOneBlockUpperExponent : GLOneBlockUpperExponentStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ π _ hbound
  let := T.topology
  have hC : (CuspidalSupport.LeviAdmissibility.oneBlock n hn).length = 1 := rfl
  rw [ScalarLayer.oneBlockLeviEquiv_toMonoidHom T hn]
  intro D ψ hψ hgen a ha
  have hχ := (T.singleBlock_isJacquetExponent_iff_flattened
    (CuspidalSupport.LeviAdmissibility.oneBlock n hn) hC D π ψ).mp ⟨hψ, hgen⟩
  have hmono := (T.singleBlockScalar_forall_block_monotone_iff
    (CuspidalSupport.LeviAdmissibility.oneBlock n hn) hC D a).mp ha
  have hb := hbound _ _ hχ _ hmono
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    using hb

end Langlands
