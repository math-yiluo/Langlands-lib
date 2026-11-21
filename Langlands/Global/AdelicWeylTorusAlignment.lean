import Langlands.Global.AdelicWeylSetAssociation
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor

/-! # Aligning the split tori of two Weyl-related parabolic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The presentation's maximal split torus factors through the specified Levi
as a maximal split torus of that Levi. -/
theorem exists_leviTorusLift (r : ParabolicRootPresentation p l a) :
    ∃ t : r.data.T.toGrp ⟶ M, IsMaximalSplitTorus t ∧ t ≫ l ≫ p = r.data.i := by
  have hj : IsClosedSubgroup (l ≫ p) :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  let := hj.mono
  let : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  exact r.isCompatible.maximalSplit.exists_standardLevi_lift r.data.i r.data.ν r.data.J
    ⟨inferInstance, r.isCompatible.levi_eq⟩ hj

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- A Weyl conjugation of the prescribed Levis can be adjusted by a right source
Levi point so that its inverse conjugation also identifies their presentation
tori. -/
def WeylTorusAlignmentStatement : Prop :=
  ∀ (F : Type u) [Field F] (G P M Q M' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    (q : Q ⟶ G) (l' : M' ⟶ Q) (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsWeylConjugation p l q l' w c →
      ∃ (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X)
        (e : r'.data.T.toGrp ≅ r.data.T.toGrp),
        r'.data.i ≫ (G.innerIso (w * (z ≫ (l ≫ p).hom.hom))).inv = e.hom ≫ r.data.i

theorem weylTorusAlignment : WeylTorusAlignmentStatement.{u} := by
  intro F _ G P M Q M' _ A A' p l a r q l' a' r' w c hw
  obtain ⟨t, htmax, ht⟩ := r.exists_leviTorusLift
  obtain ⟨t', ht'max, ht'⟩ := r'.exists_leviTorusLift
  let := hw.isIso
  let : Smooth M.X.hom := r.isCompatible.levi.isConnectedReductive.smooth
  let : IsAffineHom M.X.hom := r.isCompatible.levi.isConnectedReductive.isAffineHom
  let : ConnectedSpace M.X.left := r.isCompatible.levi.isConnectedReductive.connectedSpace
  obtain ⟨z, e, he⟩ := smoothMaximalSplitTorusConjugacy F M r'.data.T r.data.T
    (t' ≫ c) t (ht'max.comp_iso (asIso c)) htmax
  refine ⟨z⁻¹, e, ?_⟩
  have h_old : r'.data.i ≫ (G.innerIso w).inv = (t' ≫ c) ≫ l ≫ p := by
    rw [← ht', Category.assoc, Category.assoc, ← hw.comp_eq, Category.assoc]
  have hz : (G.innerIso (z⁻¹ ≫ (l ≫ p).hom.hom)).inv =
      (G.innerIso (z ≫ (l ≫ p).hom.hom)).hom := by
    rw [GrpObj.inv_comp, innerIso_inv_point_inv]
  rw [innerIso_mul_inv, ← Category.assoc, h_old, hz, Category.assoc (t' ≫ c) (l ≫ p),
    ← innerIso_hom_comp (l ≫ p) z, ← Category.assoc, he, Category.assoc, ht]

end Langlands.Global
