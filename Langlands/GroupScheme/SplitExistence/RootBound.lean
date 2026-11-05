import Langlands.GroupScheme.SplitExistence.LieWeights
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Nonzero weights on the Lie algebra are roots

Let `x` be a nonzero element of the Lie algebra of the Chevalley group whose matrix is a weight
matrix of a nonzero weight `ξ`. If `ℓ(ξ) > 0`, then `x` lies in the Lie algebra of `U_G(λ)`
(Library `dynamicLie`), so its matrix is a combination of the `e_γ`, `γ > 0`, and `ξ` is a root.
If `ℓ(ξ) < 0` the same argument applies to the opposite data. If `ℓ(ξ) = 0`, then `x` lies in the
Lie algebra of `Z_G(λ) = T`, whose matrices are diagonal; this forces `x = 0`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

/-- A nonzero weight matrix in the span of root operators has a root as its weight. -/
theorem exists_root_of_mem_span {F : Type u} [Field F] {ξ : X}
    {N : Matrix (Fin D.n) (Fin D.n) F} (hN0 : N ≠ 0) (hw : D.IsWeightMatrix ξ N) (S : Set J)
    (hspan : N ∈ Submodule.span F (Set.range fun j : S => D.eF (F := F) (j : J))) :
    ∃ j ∈ S, P.root j = ξ := by
  classical
  by_contra hno
  push Not at hno
  let π : Matrix (Fin D.n) (Fin D.n) F →ₗ[F] Matrix (Fin D.n) (Fin D.n) F :=
    { toFun := fun M => Matrix.of fun c d => if D.wt c - D.wt d = ξ then M c d else 0
      map_add' := fun M M' => by
        ext c d
        simp only [Matrix.of_apply, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun a M => by
        ext c d
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp }
  have hπN : π N = N := by
    ext c d
    change (if D.wt c - D.wt d = ξ then N c d else 0) = N c d
    split_ifs with h
    · rfl
    · by_contra h'
      exact h (hw c d (Ne.symm h'))
  have hπe : ∀ j ∈ S, π (D.eF (F := F) j) = 0 := by
    intro j hj
    ext c d
    change (if D.wt c - D.wt d = ξ then D.eF (F := F) j c d else 0) = 0
    split_ifs with h
    · by_contra h'
      have hne : D.e j 1 c d ≠ 0 := by
        intro h0
        apply h'
        simp [eF, h0]
      have hwt := D.e_weight j 1 c d hne
      rw [one_smul] at hwt
      apply hno j hj
      rw [← h, hwt]
      abel
    · rfl
  have hle : Submodule.span F (Set.range fun j : S => D.eF (F := F) (j : J)) ≤
      LinearMap.ker π := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hπe j j.2
  apply hN0
  rw [← hπN]
  exact hle hspan

namespace ChevGroup

variable {D} {k : Type u} [Field k] (G : D.ChevGroup k)

/-- The case `ℓ(ξ) > 0`: the element lies in the Lie algebra of `U_G(λ)`. -/
theorem exists_root_of_pos [P.IsReduced] [Fintype J] [DecidableEq J] [IsAffineHom G.H.X.hom]
    [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    (x : Additive (lieKernel G.H k)) (hx : x ≠ 0) {ξ : X}
    (hw : D.IsWeightMatrix ξ (G.lieMat k x)) (hpos : 0 < D.ℓ ξ) :
    ∃ j, P.root j = ξ := by
  have hws := G.mem_weightSpace_cochar x hw
  have hU : x.toMul.val ∈ (Dynamic.unipotent G.cochar).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (DualNumber k)))) := by
    rw [(dynamicLie k G.H G.cochar x.toMul).2.2]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, D.ℓ ξ = (n : ℤ) + 1 := ⟨(D.ℓ ξ).toNat - 1, by omega⟩
    refine Submodule.mem_iSup_of_mem n ?_
    rw [hn] at hws
    exact hws
  have hspan := G.coefficients_mem_span_of_unipotent x.toMul hU
  have hN0 : G.lieMat k x ≠ 0 := fun h =>
    hx (G.lieMat_injective k (h.trans (map_zero _).symm))
  obtain ⟨j, -, hj⟩ := D.exists_root_of_mem_span hN0 hw {j | b.IsPos j} hspan
  exact ⟨j, hj⟩

/-- **Nonzero weights of the Lie algebra are roots.** -/
theorem exists_root_of_isWeightMatrix [Finite J] [P.IsReduced] [Module.Finite ℤ X]
    [IsAffineHom G.H.X.hom] [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    (x : Additive (lieKernel G.H k)) (hx : x ≠ 0) {ξ : X} (hξ : ξ ≠ 0)
    (hw : D.IsWeightMatrix ξ (G.lieMat k x)) :
    ∃ j, P.root j = ξ := by
  classical
  have := Fintype.ofFinite J
  rcases lt_trichotomy (D.ℓ ξ) 0 with hneg | hzero | hpos
  · have hpos' : 0 < D.neg.ℓ ξ := by
      change 0 < -D.ℓ ξ
      omega
    have : IsAffineHom G.neg.H.X.hom := ‹IsAffineHom G.H.X.hom›
    have : IsAffine G.neg.H.X.left := ‹IsAffine G.H.X.left›
    have : LocallyOfFiniteType G.neg.H.X.hom := ‹LocallyOfFiniteType G.H.X.hom›
    exact G.neg.exists_root_of_pos x hx hw hpos'
  · exfalso
    have hws := G.mem_weightSpace_cochar x hw
    rw [hzero] at hws
    have hZ : x.toMul.val ∈ (Dynamic.centralizer G.cochar).carrier
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (DualNumber k)))) :=
      ((dynamicLie k G.H G.cochar x.toMul).1).2 hws
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 (G.centralizer_le _ hZ)
    let S : CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of k (DualNumber k)
    have hdiag : ∀ c d, c ≠ d → (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) S
        (x.toMul.val ≫ G.i.hom.hom) : Matrix (Fin D.n) (Fin D.n) (DualNumber k)) c d = 0 := by
      intro c d hcd
      apply (affSecEquiv k S).injective
      rw [map_zero, ← D.pointsEquiv_apply_eq_affine k S, ← hy, Category.assoc, ← Grp.comp_hom_hom,
        G.t_comp, pointsEquiv_torusToGL, coe_torusHom, Matrix.diagonal_apply_ne _ hcd]
    apply hx
    apply G.lieMat_injective k
    rw [map_zero]
    ext c d
    by_cases hcd : c = d
    · subst hcd
      by_contra h
      exact hξ (by rw [← hw c c h, sub_self])
    · rw [G.lieMat_apply, GeneralLinear.DualNumber.coefficients, Matrix.of_apply, hdiag c d hcd]
      rfl
  · exact G.exists_root_of_pos x hx hw hpos

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
