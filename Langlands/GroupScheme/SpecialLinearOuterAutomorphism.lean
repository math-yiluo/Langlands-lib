import Langlands.GroupScheme.SpecialLinearCenterAutomorphisms
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Centre-moving special-linear automorphisms on every test scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

attribute [local instance] isAffineHom_groupScheme

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝐒𝐋" => groupScheme (Fin (n + 1)) (CommRingCat.of k)

/-- After a rational inner conjugation, an automorphism preserves a prescribed
split pinned maximal torus. -/
theorem exists_inner_torusCompatible (p : SplitPinning 𝐒𝐋) (f : 𝐒𝐋 ≅ 𝐒𝐋) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ 𝐒𝐋.X)
      (t : p.torus ≅ p.torus),
      p.inclusion ≫ (f.trans (GroupScheme.innerIso 𝐒𝐋 g)).hom =
        CommGroupScheme.groupHom t.hom ≫ p.inclusion := by
  have hmax := p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus
  obtain ⟨g, e, he⟩ :=
    (maximalSplitTorusConjugacy k 𝐒𝐋 p.isConnectedReductive).1
      p.torus p.torus (p.inclusion ≫ f.hom) p.inclusion
      (hmax.comp_iso f) hmax
  exact ⟨g, CommGroupScheme.isoOfGroupIso e, by
    simpa only [Iso.trans_hom, Category.assoc, CommGroupScheme.isoOfGroupIso,
      CommGroupScheme.groupHom, toMul_ofMul] using he⟩

/-- Every centre-moving automorphism of the actual split special-linear group is
matrix conjugation composed with inverse transpose, on every test scheme. -/
theorem exists_outer_matrix (f : 𝐒𝐋 ≅ 𝐒𝐋) (hf : ¬ AutomorphismFixesCenter f) :
    ∃ X : GL (Fin (n + 1)) k,
      ∀ (Z : Over (Spec (CommRingCat.of k))) (z : Z ⟶ 𝐒𝐋.X),
        (pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
          (z ≫ f.hom.hom.hom) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap Z) X : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (((pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z z)⁻¹ :
              Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
            (Matrix.GeneralLinearGroup.map (scalarMap Z) X⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) := by
  classical
  obtain ⟨p, -⟩ := FinSucc.exists_splitPinning n k
  obtain ⟨g, t, hsq⟩ := exists_inner_torusCompatible p f
  let q := GroupScheme.innerIso 𝐒𝐋 g
  have hfq : ¬ AutomorphismFixesCenter (f.trans q) :=
    fun h => hf ((AutomorphismFixesCenter.trans_right_iff f
      (AutomorphismFixesCenter.innerIso g)).mp h)
  have hnon := specialLinearTorusAutomorphism_nontrivial_of_not_fixesCenter
    k n p (f.trans q) t hsq hfq
  obtain ⟨X, hX⟩ := SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism
    k n p (f.trans q) t hsq
  obtain ⟨C, hC⟩ := SpecialLinearTorusAutomorphism.exists_pointsEquiv_constantPoint g
  let c := Matrix.SpecialLinearGroup.toGL C
  refine ⟨c⁻¹ * X, fun Z z => ?_⟩
  let φ := scalarMap Z
  let pe := pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
  have hmat := (hX Z (pe z)).2 hnon
  dsimp only [pe] at hmat
  rw [MulEquiv.symm_apply_apply] at hmat
  have hGL : Matrix.SpecialLinearGroup.toGL (pe (z ≫ (f.trans q).hom.hom.hom)) =
      Matrix.GeneralLinearGroup.map φ X *
        Matrix.SpecialLinearGroup.toGL (matrixContragredient (Fin (n + 1))
          Γ(Z.left, ⊤) (pe z)) * (Matrix.GeneralLinearGroup.map φ X)⁻¹ := by
    apply Units.ext
    simpa only [Units.val_mul, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      matrixContragredient_coe] using hmat
  have hc : Matrix.SpecialLinearGroup.toGL
      (pe (GroupScheme.constantPoint 𝐒𝐋 g Z)) = Matrix.GeneralLinearGroup.map φ c := by
    rw [hC Z, SpecialLinearTorusAutomorphism.toGL_map]
  change Matrix.SpecialLinearGroup.toGL (pe ((z ≫ f.hom.hom.hom) ≫ q.hom.hom.hom)) = _
    at hGL
  rw [GroupScheme.comp_innerIso_hom, map_mul, map_mul, map_inv,
    map_mul, map_mul, map_inv, hc] at hGL
  have hfinal : Matrix.SpecialLinearGroup.toGL (pe (z ≫ f.hom.hom.hom)) =
      Matrix.GeneralLinearGroup.map φ (c⁻¹ * X) *
        Matrix.SpecialLinearGroup.toGL (matrixContragredient (Fin (n + 1))
          Γ(Z.left, ⊤) (pe z)) * (Matrix.GeneralLinearGroup.map φ (c⁻¹ * X))⁻¹ := by
    rw [map_mul, map_inv]
    have he := congrArg (fun y : GL (Fin (n + 1)) Γ(Z.left, ⊤) =>
      (Matrix.GeneralLinearGroup.map φ c)⁻¹ * y * Matrix.GeneralLinearGroup.map φ c) hGL
    group at he ⊢
    exact he
  have he := congrArg (fun y : GL (Fin (n + 1)) Γ(Z.left, ⊤) =>
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) hfinal
  simpa only [Units.val_mul, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    matrixContragredient_coe] using he

/-- A chosen matrix, together with its all-test inverse-transpose formula, for a
centre-moving automorphism of a split special-linear group. -/
def outerMatrixData (f : 𝐒𝐋 ≅ 𝐒𝐋) (hf : ¬ AutomorphismFixesCenter f) :
    {X : GL (Fin (n + 1)) k //
      ∀ (Z : Over (Spec (CommRingCat.of k))) (z : Z ⟶ 𝐒𝐋.X),
        (pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
          (z ≫ f.hom.hom.hom) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap Z) X :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (((pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z z)⁻¹ :
              Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
            (Matrix.GeneralLinearGroup.map (scalarMap Z) X⁻¹ :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))} :=
  Classical.indefiniteDescription _ (exists_outer_matrix f hf)

end Langlands.GroupScheme.SpecialLinear
