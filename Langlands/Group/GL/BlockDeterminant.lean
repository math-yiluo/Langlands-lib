import Langlands.Group.GL.Blocks

/-! # Determinants of standard block parabolic elements -/

noncomputable section
open scoped BigOperators

namespace Langlands.GeneralLinear

universe uF

/-- The determinant of a standard block parabolic element is the product
of the determinants of its actual Levi projection blocks. -/
theorem determinant_blockParabolic {R : Type uF} [CommRing R]
    {n : ℕ} (B : BlockShape n) (g : B.parabolic R) :
    determinant g.val = ∏ i, determinant (B.leviProjection R g i) := by
  let M : Matrix B.Index B.Index R := g.val.val.submatrix B.indexEquiv B.indexEquiv
  have hM : M.BlockTriangular Sigma.fst := g.property
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_submatrix_equiv_self B.indexEquiv]
  change M.det = _
  rw [hM.det_fintype, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (B.size i) ≃ {a : B.Index // a.1 = i} :=
    Equiv.ofBijective (fun a => ⟨⟨i, a⟩, rfl⟩) (by
      constructor
      · intro a b h
        exact Sigma.mk.inj_iff.mp (congrArg Subtype.val h) |>.2 |> eq_of_heq
      · rintro ⟨⟨j, a⟩, h⟩
        dsimp only at h
        subst j
        exact ⟨a, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

end Langlands.GeneralLinear
