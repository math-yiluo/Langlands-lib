import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport
import Langlands.Representation.Plancherel.RationalPlancherelConstantConjugation

/-! # Regular Eisenstein parameters under ambient transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
  AdelicGroupPoints

section Forms

variable {F : Type u} [Field F]
  {G G' : GroupScheme (Spec (CommRingCat.of F))}
  {T A : CommGroupScheme (Spec (CommRingCat.of F))}
  (e : G ≅ G') (i : T.toGrp ⟶ G)

/-- The same torus carries the same rational Weyl character action
after transporting its ambient group. -/
private theorem relativeWeylRealCharacterAction_comp_ambientIso
    [Mono i.hom.hom.left] [Mono (i ≫ e.hom).hom.hom.left]
    (h : i ≫ e.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ e.hom))
    (w : relativeWeylGroup i) (x : Vstar T) :
    relativeWeylRealCharacterAction (i ≫ e.hom) (relativeWeylTransportEquiv (Iso.refl T) e h w) x =
      relativeWeylRealCharacterAction i w x := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [relativeWeylRealCharacterAction_tmul, relativeWeylRealCharacterAction_tmul]
    congr 1
    simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] using
      relativeWeylCharacterAction_transport (Iso.refl T) e h w χ
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- The Weyl-averaged form is unchanged on the same torus when the ambient
group is transported. -/
theorem relativeWeylInvariantForm_comp_ambientIso
    [Mono i.hom.hom.left] [Mono (i ≫ e.hom).hom.hom.left]
    [Fintype (relativeWeylGroup i)] [Fintype (relativeWeylGroup (i ≫ e.hom))]
    (hT : IsSplitTorus T.toGrp) :
    relativeWeylInvariantForm (i ≫ e.hom) hT = relativeWeylInvariantForm i hT := by
  have h : i ≫ e.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ e.hom) := by
    change i ≫ e.hom = (𝟙 T.toGrp) ≫ (i ≫ e.hom)
    rw [Category.id_comp]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [relativeWeylInvariantForm_apply]
  exact (Fintype.sum_equiv (relativeWeylTransportEquiv (Iso.refl T) e h).toEquiv _ _
    (fun w => by simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      relativeWeylRealCharacterAction_comp_ambientIso e i h])).symm

/-- The induced character form on the split component is unchanged as well. -/
theorem weylInducedCharacterForm_comp_ambientIso
    [Mono i.hom.hom.left] [Mono (i ≫ e.hom).hom.hom.left]
    [Fintype (relativeWeylGroup i)] [Fintype (relativeWeylGroup (i ≫ e.hom))]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp) (f : A ⟶ T)
    [Mono (CommGroupScheme.groupHom f).hom.hom.left] :
    weylInducedCharacterForm hA hT f (i ≫ e.hom) = weylInducedCharacterForm hA hT f i := by
  unfold weylInducedCharacterForm
  congr 1
  exact relativeWeylInvariantForm_comp_ambientIso e i hT

end Forms

/-- Transporting the parabolic presentation through an ambient isomorphism
preserves its exact Eisenstein regularity test. -/
def EisensteinRegularityAmbientTransportStatement : Prop :=
  ∀ (F : Type u) [Field F]
    (G G' P M : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
    (r : ParabolicRootPresentation p l a) (e : G ≅ G')
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Mono (r.compAmbientIso e).data.i.hom.hom.left]
    [Fintype (relativeWeylGroup (r.compAmbientIso e).data.i)]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
      (R : ℝ) (lam : ComplexCharacterParameter F P),
    haveI : Mono (CommGroupScheme.groupHom (r.compAmbientIso e).data.f).hom.hom.left :=
      inferInstanceAs (Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (r.compAmbientIso e).IsRegularParameter hA hT R lam ↔ r.IsRegularParameter hA hT R lam

theorem eisensteinRegularityAmbientTransport : EisensteinRegularityAmbientTransportStatement.{u} := by
  intro F _ G G' P M _ _ A p l a r e _ _ _ _ _ hA hT R lam
  have hroots : (r.compAmbientIso e).unipotentRoots = r.unipotentRoots := by
    change {α | α ≠ 0 ∧ ∃ χ ∈ positiveRelativeRoots (r.data.i ≫ e.hom) r.data.ν,
      r.data.f ≫ χ = α} = r.unipotentRoots
    rw [positiveRelativeRoots_comp_iso]
    rfl
  let : Mono (r.data.i ≫ e.hom).hom.hom.left :=
    inferInstanceAs (Mono (r.compAmbientIso e).data.i.hom.hom.left)
  let : Fintype (relativeWeylGroup (r.data.i ≫ e.hom)) :=
    inferInstanceAs (Fintype (relativeWeylGroup (r.compAmbientIso e).data.i))
  unfold ParabolicRootPresentation.IsRegularParameter
  rw [hroots]
  have hform := weylInducedCharacterForm_comp_ambientIso e r.data.i hA hT r.data.f
  change (∀ α ∈ r.unipotentRoots, R < weylInducedCharacterForm hA hT r.data.f (r.data.i ≫ e.hom)
    (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α)) ↔ _
  rw [hform]

end Langlands.Global
