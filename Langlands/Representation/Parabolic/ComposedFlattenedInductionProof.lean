import Langlands.Representation.Parabolic.ComposedFlattenedInductionStatement
import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof

/-! Canonical flattened specialization of the coordinate normalization theorem. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

namespace GeneralLinear.BlockShape

/-- The generic Levi coordinate map at the canonical flattened coordinates is
the published actual flattened Levi equivalence. -/
theorem leviRefinementEquiv_flatten (R : Type uF) [CommRing R] {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) :
    (B.flatten S).leviRefinementEquiv B S (B.flattenBlockEquiv S)
        (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) R =
      flattenedLeviEquiv R B S := by
  apply MulEquiv.ext
  intro m
  apply (refinedLeviEquiv R B S).symm.injective
  simp only [leviRefinementEquiv, flattenedLeviEquiv,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  funext i j
  rw [nestedLeviEquiv_apply, flattenedLeviProductEquiv_apply]

end GeneralLinear.BlockShape

namespace Parabolic

/-- Direct composed and flattened normalized induction agree through the
function-preserving equivalence in the exact published statement. -/
theorem composedFlattenedInduction :
    ComposedFlattenedInductionStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B S V _ _ σ
  let := T.generalLinearTopologicalGroup n
  let e := B.flattenBlockEquiv S
  let hs := fun a => (B.flatten_size_flattenBlockEquiv S a).symm
  have hc : ∀ i k x, B.index i ((S i).index k x) =
      (B.flatten S).index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) :=
    fun i k x => B.index_index_eq_flatten S ⟨i, k⟩ x
  have hlevi : (B.flatten S).leviRefinementEquiv B S e hs F.Carrier =
      flattenedLeviEquiv F.Carrier B S :=
    B.leviRefinementEquiv_flatten F.Carrier S
  have hσ :
      (σ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom).comp
        ((B.flatten S).leviRefinementEquiv B S e hs F.Carrier).symm.toMonoidHom =
      σ := by
    apply MonoidHom.ext
    intro m
    change σ (flattenedLeviEquiv F.Carrier B S
      (((B.flatten S).leviRefinementEquiv B S e hs F.Carrier).symm m)) = σ m
    rw [hlevi, MulEquiv.apply_symm_apply]
  have h := (refinementCoordinatesNormalization p F T n (B.flatten S) B S
    e hs hc).2.2 V (σ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
  dsimp only at h
  rw [hσ] at h
  exact h

end Parabolic
end Langlands
