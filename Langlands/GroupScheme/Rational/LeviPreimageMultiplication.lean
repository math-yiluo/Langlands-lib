import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient

/-! # Original-Levi multiplication in actual inverse images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {R Q N V : GroupScheme S}
    (t : R ⟶ Q) (n : N ⟶ Q) (s : V ⟶ Q) (nR : N ⟶ R)

/-- A supplied two-factor multiplication decomposition lifts along any
homomorphism admitting a lift of its exact original first factor. -/
theorem isIso_subgroupMultiplication_preimage
    (hn : nR ≫ t = n) [IsIso (subgroupMultiplication n s)] :
    IsIso (subgroupMultiplication nR (SubgroupPreimage.inclusion t s)) := by
  let W := SubgroupPreimage.groupScheme t s
  let i := SubgroupPreimage.inclusion t s
  let p := SubgroupPreimage.projection t s
  let m := subgroupMultiplication n s
  let mR := subgroupMultiplication nR i
  let f : N.X ⊗ W.X ⟶ N.X ⊗ V.X := lift (fst _ _) (snd _ _ ≫ p.hom.hom)
  have hn' : nR.hom.hom ≫ t.hom.hom = n.hom.hom :=
    congrArg (fun f : N ⟶ Q => f.hom.hom) hn
  have hf : f ≫ m = mR ≫ t.hom.hom := by
    simp only [f, m, mR, subgroupMultiplication, MonObj.comp_mul,
      MonObj.mul_comp, lift_fst_assoc, lift_snd_assoc, Category.assoc]
    rw [hn', (SubgroupPreimage.isPullback t s).w]
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨fun w w' h => ?_, fun x => ?_⟩
  · change w ≫ mR = w' ≫ mR at h
    have h' : w ≫ f = w' ≫ f := by
      apply (cancel_mono m).mp
      rw [Category.assoc, Category.assoc, hf, ← Category.assoc,
        ← Category.assoc, h]
    have ha : w ≫ fst N.X W.X = w' ≫ fst N.X W.X := by
      simpa only [f, Category.assoc, lift_fst, Category.comp_id] using
        congrArg (fun z => z ≫ fst N.X V.X) h'
    have hp : (w ≫ snd N.X W.X) ≫ p.hom.hom =
        (w' ≫ snd N.X W.X) ≫ p.hom.hom := by
      simpa only [f, Category.assoc, lift_snd] using
        congrArg (fun z => z ≫ snd N.X V.X) h'
    dsimp only [mR] at h
    rw [comp_subgroupMultiplication_eq, comp_subgroupMultiplication_eq] at h
    change (w ≫ fst N.X W.X ≫ nR.hom.hom) * (w ≫ snd N.X W.X ≫ i.hom.hom) =
      (w' ≫ fst N.X W.X ≫ nR.hom.hom) * (w' ≫ snd N.X W.X ≫ i.hom.hom) at h
    have hi : (w ≫ snd N.X W.X) ≫ i.hom.hom =
        (w' ≫ snd N.X W.X) ≫ i.hom.hom := by
      apply mul_left_cancel (a := w' ≫ fst N.X W.X ≫ nR.hom.hom)
      simpa only [← Category.assoc, ha] using h
    exact CartesianMonoidalCategory.hom_ext _ _ ha
      ((SubgroupPreimage.isPullback t s).hom_ext hi hp)
  · let z : T ⟶ N.X ⊗ V.X := x ≫ t.hom.hom ≫ inv m
    let a : T ⟶ N.X := z ≫ fst N.X V.X
    let c : T ⟶ V.X := z ≫ snd N.X V.X
    have hfac : (a ≫ n.hom.hom) * (c ≫ s.hom.hom) = x ≫ t.hom.hom := by
      change (z ≫ fst N.X V.X ≫ n.hom.hom) *
        (z ≫ snd N.X V.X ≫ s.hom.hom) = _
      rw [← comp_subgroupMultiplication_eq]
      simp only [z, m, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    let y : T ⟶ R.X := (a ≫ nR.hom.hom)⁻¹ * x
    have hy : y ≫ t.hom.hom = c ≫ s.hom.hom := by
      simp only [y, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
      rw [← Grp.comp_hom_hom, hn, ← hfac, inv_mul_cancel_left]
    let b : T ⟶ W.X := (SubgroupPreimage.isPullback t s).lift y c hy
    refine ⟨lift a b, ?_⟩
    change lift a b ≫ subgroupMultiplication nR i = x
    rw [comp_subgroupMultiplication]
    have hb : b ≫ i.hom.hom = y := (SubgroupPreimage.isPullback t s).lift_fst _ _ _
    rw [hb]
    exact mul_inv_cancel_left _ _

/-- The actual multiplication isomorphism with the supplied original first
factor and the group-scheme inverse image of the second factor. -/
def subgroupPreimageMultiplicationIso
    (hn : nR ≫ t = n) [IsIso (subgroupMultiplication n s)] :
    N.X ⊗ (SubgroupPreimage.groupScheme t s).X ≅ R.X := by
  letI := isIso_subgroupMultiplication_preimage t n s nR hn
  exact asIso (subgroupMultiplication nR (SubgroupPreimage.inclusion t s))

@[simp]
theorem subgroupPreimageMultiplicationIso_hom
    (hn : nR ≫ t = n) [IsIso (subgroupMultiplication n s)] :
    (subgroupPreimageMultiplicationIso t n s nR hn).hom =
      subgroupMultiplication nR (SubgroupPreimage.inclusion t s) := rfl

end Langlands.GroupScheme
