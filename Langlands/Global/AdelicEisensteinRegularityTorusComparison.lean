import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicEisensteinRootSigns
import Langlands.Global.AdelicWeylTorusAlignment
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone

/-! # Cofinal Eisenstein regularity tests after changing the presentation torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme RealTorusSpace AdelicGroupPoints Langlands.Plancherel

section Forms

variable {F : Type u} [Field F]
  {T T' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]

omit [IsAffineHom G.X.hom] in
private theorem realCharacterAction_congr (e : T ≅ T')
    (h : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (w : relativeWeylGroup i) (x : Vstar T) :
    characterRealCongr e (relativeWeylRealCharacterAction i w x) =
      relativeWeylRealCharacterAction j (relativeWeylTransportEquiv e (Iso.refl G) h w)
        (characterRealCongr e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    simp only [relativeWeylRealCharacterAction_tmul, characterRealCongr_tmul]
    exact congrArg (fun χ' => s ⊗ₜ[ℤ] χ')
      (relativeWeylCharacterAction_transport e (Iso.refl G) h w χ).symm
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem invariantForms_root_proportional
    (D : RelativeRootReflectionData i) (B C : LinearMap.BilinForm ℝ (Vstar T))
    (hB : IsWeylInvariantInnerProduct i B) (hC : IsWeylInvariantInnerProduct i C) :
    ∃ c : relativeRoots i → ℝ, (∀ β, 0 < c β) ∧ ∀ β x,
      C x ((1 : ℝ) ⊗ₜ[ℤ] β.val) = c β * B x ((1 : ℝ) ⊗ₜ[ℤ] β.val) := by
  let b (β : relativeRoots i) : Vstar T := (1 : ℝ) ⊗ₜ[ℤ] β.val
  have hbp (β : relativeRoots i) : 0 < B (b β) (b β) :=
    hB.2.1 _ (D.one_tmul_ne_zero i β)
  refine ⟨fun β => C (b β) (b β) / B (b β) (b β), fun β =>
    div_pos (hC.2.1 _ (D.one_tmul_ne_zero i β)) (hbp β), ?_⟩
  intro β x
  change C x (b β) = C (b β) (b β) / B (b β) (b β) * B x (b β)
  rw [div_mul_eq_mul_div, eq_div_iff (hbp β).ne']
  have hb := D.coroot_mul_form i B hB β x
  have hc := D.coroot_mul_form i C hC β x
  change _ * B (b β) (b β) = 2 * B x (b β) at hb
  change _ * C (b β) (b β) = 2 * C x (b β) at hc
  linear_combination (C (b β) (b β) / 2) * hb - (B (b β) (b β) / 2) * hc

end Forms

/-- When two presentations of the same parabolic, Levi, and split component
have isomorphic ambient torus inclusions and corresponding component factors,
every old regularity threshold is reached by a sufficiently strong new one. -/
def EisensteinRegularityTorusComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r s : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Mono s.data.i.hom.hom.left] [Fintype (relativeWeylGroup s.data.i)]
    [Mono (CommGroupScheme.groupHom s.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hT' : IsSplitTorus s.data.T.toGrp) (e : r.data.T ≅ s.data.T),
    IsConnectedReductive G → r.data.i = CommGroupScheme.groupHom e.hom ≫ s.data.i →
    s.data.f = r.data.f ≫ e.hom →
    ∀ R : ℝ, ∃ S : ℝ, ∀ lam : ComplexCharacterParameter F P,
      s.IsRegularParameter hA hT' S lam → r.IsRegularParameter hA hT R lam

theorem eisensteinRegularityTorusComparison : EisensteinRegularityTorusComparisonStatement.{u} := by
  classical
  intro F _ _ G P M A _ _ p l a r s _ _ _ _ _ _ hA hT hT' e hG he hf R
  have hsq : r.data.i ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom e.hom ≫ s.data.i := by simpa only [Iso.refl_hom, Category.comp_id]
  let := hG.smooth
  have hroots : r.unipotentRoots = s.unipotentRoots := by
    rw [r.unipotentRoots_eq_intrinsicPositiveRoots hG, s.unipotentRoots_eq_intrinsicPositiveRoots hG]
    exact r.intrinsicPositiveRoots_eq s
  obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG r.data.T r.data.i
    r.isCompatible.maximalSplit
  let B := relativeWeylInvariantForm r.data.i hT
  let C' := relativeWeylInvariantForm s.data.i hT'
  let E := characterRealCongr e
  let C := C'.compl₁₂ E.toLinearMap E.toLinearMap
  have hB : IsWeylInvariantInnerProduct r.data.i B :=
    ⟨relativeWeylInvariantForm_symm r.data.i hT,
      fun _ => relativeWeylInvariantForm_pos r.data.i hT,
      relativeWeylInvariantForm_invariant r.data.i hT⟩
  have hC : IsWeylInvariantInnerProduct r.data.i C := by
    refine ⟨fun x y => relativeWeylInvariantForm_symm s.data.i hT' (E x) (E y), ?_, ?_⟩
    · intro x hx
      exact relativeWeylInvariantForm_pos s.data.i hT'
        (fun h => hx (E.injective (h.trans E.map_zero.symm)))
    · intro w x y
      change C' (E (relativeWeylRealCharacterAction r.data.i w x))
        (E (relativeWeylRealCharacterAction r.data.i w y)) = C' (E x) (E y)
      dsimp only [E]
      rw [realCharacterAction_congr e hsq w x, realCharacterAction_congr e hsq w y]
      exact relativeWeylInvariantForm_invariant s.data.i hT' _ _ _
  obtain ⟨c, hc, hscale⟩ := invariantForms_root_proportional D B C hB hC
  let := (hT.finite_relativeRoots r.data.i).fintype
  let S := ∑ β : relativeRoots r.data.i, max (c β * R) 0
  have hS (β : relativeRoots r.data.i) : c β * R ≤ S :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun ζ => max (c ζ * R) 0)
      (fun ζ _ => le_max_right (c ζ * R) 0) (Finset.mem_univ β))
  obtain ⟨t, _, ht⟩ := r.exists_leviTorusLift
  let t' := CommGroupScheme.groupHom e.inv ≫ t
  have ht' : t' ≫ l ≫ p = s.data.i := by
    dsimp only [t']
    rw [Category.assoc, ht, he, ← Category.assoc]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ s.data.i = s.data.i
    rw [Iso.inv_hom_id]
    exact Category.id_comp _
  have hrestrict (x : RealCharacterParameter F P) :
      E (realParameterRestriction (t ≫ l) x) = realParameterRestriction (t' ≫ l) x := by
    induction x using TensorProduct.inductionOn with
    | tmul u χ =>
      change E (u ⊗ₜ[ℤ] characterRestrict (t ≫ l) χ) =
        u ⊗ₜ[ℤ] characterRestrict (t' ≫ l) χ
      rw [characterRealCongr_tmul]
      change u ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom e.inv)
          (characterRestrict (t ≫ l) χ) = u ⊗ₜ[ℤ] characterRestrict (t' ≫ l) χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, Category.assoc]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨S, fun lam hregular α hα => ?_⟩
  have hα' : α ∈ s.unipotentRoots := hroots ▸ hα
  obtain ⟨_, β, hβ, hrβ⟩ := hα
  have hrβ' : characterRestrict (CommGroupScheme.groupHom r.data.f) β = α := hrβ
  let root : relativeRoots r.data.i := ⟨β, hβ.1⟩
  let β' := characterLattice.congr e β
  have hsβ : characterRestrict (CommGroupScheme.groupHom s.data.f) β' = α := by
    change s.data.f ≫ e.inv ≫ β = α
    rw [hf, Category.assoc, Iso.hom_inv_id_assoc]
    exact hrβ
  let x := parameterRealPart F P lam
  let xA := realParameterRestriction (a ≫ l) x
  have hx0 := eisensteinAmbientParameterLift F G P M A p l a r hA hT t hG ht x
  have hx1 := eisensteinAmbientParameterLift F G P M A p l a s hA hT' t' hG ht' x
  have hlarge := (weylInducedCharacterForm_root_inequality_iff hA hT' s.data.f s.data.i
    xA β' S).mpr (by rw [hsβ]; exact hregular α hα')
  rw [← hx1, ← hrestrict] at hlarge
  have hscaled : S < C (realParameterRestriction (t ≫ l) x) ((1 : ℝ) ⊗ₜ[ℤ] β) :=
    hlarge
  rw [show β = root.val from rfl, hscale] at hscaled
  have hold := lt_of_mul_lt_mul_left ((hS root).trans_lt hscaled) (hc root).le
  rw [hx0] at hold
  simpa only [hrβ'] using
    (weylInducedCharacterForm_root_inequality_iff hA hT r.data.f r.data.i xA β R).mp
      (by simpa only [root] using hold)

end Langlands.Global
