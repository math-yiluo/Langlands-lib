import Langlands.Global.AdelicEisensteinAmbientParametersStatement
import Langlands.GroupScheme.Rational.ParabolicCorootLiftUniqueness
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof

/-! # Ambient character parameters for Eisenstein series -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Plancherel AdelicGroupPoints RealTorusSpace

/-- The restriction through the Levi is the orthogonal lift used in regularity. -/
theorem eisensteinAmbientParameterLift : EisensteinAmbientParameterLiftStatement.{u} := by
  intro F _ _ G P M A _ _ p l a r _ _ _ hA hT t hG ht x
  obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG r.data.T r.data.i
    r.isCompatible.maximalSplit
  have hp := r.isCompatible.parabolic.isClosedSubgroup
  have hpOver : Mono p.hom.hom := by
    let := hp.mono
    exact Over.mono_of_mono_left _
  let : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hpOver
  have hLevi := r.isCompatible.levi.isClosedSubgroup.comp hp
  let : Mono (l ≫ p).hom.hom.left := hLevi.mono
  have hrep : (standardLevi r.data.i r.data.ν r.data.J).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.isCompatible.levi_eq⟩
  have hAnn := standardLeviCharacterAnnihilator F G hG r.data.T r.data.i
    r.isCompatible.maximalSplit r.data.ν r.isCompatible.generic r.data.J
    r.isCompatible.subset_simpleRoots M (l ≫ p) hLevi hrep t ht D
  have hInRange : realParameterRestriction (t ≫ l) x ∈
      (rationalCharacterRestrictReal t).range := by
    refine ⟨rationalCharacterRestrictReal l x, ?_⟩
    induction x using TensorProduct.inductionOn with
    | tmul s χ =>
      change s ⊗ₜ[ℤ] characterRestrict t (characterRestrict l χ) =
        s ⊗ₜ[ℤ] characterRestrict (t ≫ l) χ
      rw [characterRestrict_comp, AddMonoidHom.comp_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [hAnn] at hInRange
  have hforms := weylInducedCharacterForm_compatible hA hT r.data.f r.data.i
  apply r.eq_of_restrict_eq_of_selectedCoroot_pair_eq_zero hG D _ _
    ((mem_corootAnnihilator r.data.i D r.data.J _).mp hInRange)
  · intro α hα
    let B := relativeWeylInvariantForm r.data.i hT
    have hB : IsWeylInvariantInnerProduct r.data.i B :=
      ⟨relativeWeylInvariantForm_symm r.data.i hT,
        fun _ => relativeWeylInvariantForm_pos r.data.i hT,
        relativeWeylInvariantForm_invariant r.data.i hT⟩
    apply (D.coroot_eq_zero_iff r.data.i B hB α _).mpr
    dsimp only [B]
    rw [hforms.2, rationalCharacterRestrictReal_tmul]
    change weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) x) ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ α.val)) = 0
    rw [r.selectedRoot_restrict_eq_zero hα, tmul_zero, map_zero]
  · rw [hforms.1]
    have hcomp : CommGroupScheme.groupHom r.data.f ≫ t ≫ l = a ≫ l := by
      apply (cancel_mono p).mp
      simpa only [Category.assoc, ht] using r.isCompatible.factor_comp
    clear hInRange
    induction x using TensorProduct.inductionOn with
    | tmul s χ =>
      change s ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom r.data.f)
          (characterRestrict (t ≫ l) χ) = s ⊗ₜ[ℤ] characterRestrict (a ≫ l) χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hcomp]
    | add y z hy hz => simp only [map_add, hy, hz]

/-- The actual torus restrictions intertwine Levi conjugation and the Weyl action. -/
theorem eisensteinAmbientWeylParameter : EisensteinAmbientWeylParameterStatement.{u} := by
  intro F _ _ G P M Q M' T i _ p _ l q l' t t' π' n c ht ht' hπ hw lam
  have hnorm := (isNormalizingPoint_normalizingAut i n).inv
  rw [IsNormalizingPoint, innerIso_inv_hom] at hnorm
  change i ≫ (G.innerIso n.val).inv =
    CommGroupScheme.groupHom (normalizingAut i n).inv ≫ i at hnorm
  have hcT : t' ≫ c ≫ l = CommGroupScheme.groupHom (normalizingAut i n).inv ≫ t ≫ l := by
    apply (cancel_mono p).mp
    calc
      (t' ≫ c ≫ l) ≫ p = t' ≫ l' ≫ q ≫ (G.innerIso n.val).inv := by
        simp only [Category.assoc, hw.comp_eq]
      _ = i ≫ (G.innerIso n.val).inv := by
        simpa only [Category.assoc] using
          congrArg (fun j => j ≫ (G.innerIso n.val).inv) ht'
      _ = (CommGroupScheme.groupHom (normalizingAut i n).inv ≫ t ≫ l) ≫ p := by
        simpa only [Category.assoc, ht] using hnorm
  have hcomp : (t' ≫ l') ≫ π' ≫ c ≫ l =
      CommGroupScheme.groupHom (normalizingAut i n).inv ≫ t ≫ l := by
    rw [Category.assoc, ← Category.assoc l', hπ, Category.id_comp, hcT]
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [weylParameter_tmul, parameterRealPart_tmul, parameterRealPart_tmul,
      relativeWeylRealCharacterAction_mk]
    change s.re ⊗ₜ[ℤ] characterRestrict (t' ≫ l') (characterRestrict (π' ≫ c ≫ l) χ) =
      s.re ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom (normalizingAut i n).inv)
        (characterRestrict (t ≫ l) χ)
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hcomp, characterRestrict_comp,
      AddMonoidHom.comp_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Both ambient parameter comparisons. -/
theorem eisensteinAmbientParameters : EisensteinAmbientParametersStatement.{u} :=
  ⟨eisensteinAmbientParameterLift, eisensteinAmbientWeylParameter⟩

end Langlands.Global
