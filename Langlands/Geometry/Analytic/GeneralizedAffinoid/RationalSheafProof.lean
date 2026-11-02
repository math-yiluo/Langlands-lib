import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSheafStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalGluingProof
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.Ring.Limits

/-! # The positive-radius rational algebra sheaf -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

private theorem hom_unique {K : Type u} [NormedField K] [IsUltrametricDist K]
    {P : PresentedAffinoidAlgebra K} {d e : RationalChart K P} (f g : d ⟶ e) :
    f = g :=
  (inferInstance : Subsingleton (Restriction d e)).elim f g

section Conversion

variable (hglue : FiniteRationalGluingStatement.{u})
  {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem restriction_comp_apply {c d e : RationalChart K P}
    (f : c ⟶ d) (g : d ⟶ e) (a : e.algebra) :
    f.restriction (g.restriction a) = (f ≫ g).restriction a := by
  rw [Restriction.restriction_comp]
  rfl

include hglue

private theorem eq_of_restrictions {d : RationalChart K P}
    {I : Type u} [Finite I] (D : I → RationalChart K P) (f : ∀ i, D i ⟶ d)
    (hcover : FamilyCovers d D) {a b : d.algebra}
    (hab : ∀ i, (f i).restriction a = (f i).restriction b) : a = b := by
  have hcompat : ∀ i j,
      (interLeft (D i) (D j)).restriction ((f i).restriction a) =
      (interRight (D i) (D j)).restriction ((f j).restriction a) := by
    intro i j
    rw [restriction_comp_apply, restriction_comp_apply]
    rw [hom_unique (interLeft (D i) (D j) ≫ f i) (interRight (D i) (D j) ≫ f j)]
  obtain ⟨c, _, hc⟩ := hglue K P d I D f hcover (fun i => (f i).restriction a) hcompat
  exact (hc a (fun _ => rfl)).trans (hc b (fun i => (hab i).symm)).symm

private theorem rationalUnderlyingIsSheaf :
    Presieve.IsSheaf (finiteRationalTopology K P)
      (algebraPresheaf K P ⋙ forget (CommAlgCat K)) := by
  intro d S hS x hx
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  let : Finite I := hI
  have hcompat : ∀ i j,
      (interLeft (D i) (D j)).restriction (x (f i) (hf i)) =
      (interRight (D i) (D j)).restriction (x (f j) (hf j)) := by
    intro i j
    exact hx (interLeft (D i) (D j)) (interRight (D i) (D j))
      (hf i) (hf j) (hom_unique _ _)
  obtain ⟨a, ha, huniq⟩ := hglue K P d I D f hcover (fun i => x (f i) (hf i)) hcompat
  refine ⟨a, ?_, ?_⟩
  · intro e g hg
    change g.restriction a = x g hg
    have hintercover : FamilyCovers e (fun i => e.inter (D i)) := by
      intro z hz
      obtain ⟨i, hi⟩ := hcover z (g.subset hz)
      exact ⟨i, by rw [locus_inter]; exact ⟨hz, hi⟩⟩
    apply eq_of_restrictions hglue (fun i => e.inter (D i))
      (fun i => interLeft e (D i)) hintercover
    intro i
    calc
      (interLeft e (D i)).restriction (g.restriction a) =
          (interRight e (D i)).restriction ((f i).restriction a) := by
        rw [restriction_comp_apply, restriction_comp_apply]
        rw [hom_unique (interLeft e (D i) ≫ g) (interRight e (D i) ≫ f i)]
      _ = (interRight e (D i)).restriction (x (f i) (hf i)) := by rw [ha i]
      _ = (interLeft e (D i)).restriction (x g hg) :=
        (hx (interLeft e (D i)) (interRight e (D i)) hg (hf i) (hom_unique _ _)).symm
  · intro b hb
    exact huniq b (fun i => hb (f i) (hf i))

private theorem rationalPresheafIsSheaf_of_finiteGluing :
    RationalPresheafSheafStatement.{u} := by
  intro K _ _ _ P
  let : PreservesLimits (forget (CommAlgCat K)) := by
    change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
      Under.forget (CommRingCat.of K) ⋙ forget CommRingCat)
    infer_instance
  apply (Presheaf.isSheaf_iff_isSheaf_forget (finiteRationalTopology K P)
    (algebraPresheaf K P) (forget (CommAlgCat K))).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  exact rationalUnderlyingIsSheaf hglue

end Conversion

/-- The actual rational algebra presheaf is a sheaf for the finite rational topology. -/
theorem rationalPresheafIsSheaf : RationalPresheafSheafStatement.{u} :=
  rationalPresheafIsSheaf_of_finiteGluing finiteRationalGluing

/-- Finite section gluing and the categorical sheaf property for the actual rational site. -/
theorem rationalSheaf : RationalSheafStatement.{u} :=
  ⟨finiteRationalGluing, rationalPresheafIsSheaf⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
