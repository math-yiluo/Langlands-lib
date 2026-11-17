import Langlands.GroupScheme.Dynamic.IntrinsicFirstCut
import Langlands.GroupScheme.RelativeUnipotent.RootWeightPolynomial
import Langlands.GroupScheme.Rational.ClosedIntrinsicWeight

/-! # Intrinsic cyclic conjugation cutoffs on actual affine groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineCorepresentation

open Corepresented Corepresented.UnipotentPrimitive AffineLine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {B : CommAlgCat.{u} R} (ψ : (algSpec R).obj (op B) ≅ G.X)

/-- The actual group isomorphism between an affine presentation and its group. -/
def modelGroupIso : model G ψ ≅ G where
  hom := Grp.homMk (iso G ψ).hom
  inv := toModel G ψ
  hom_inv_id := by apply Grp.hom_ext; exact ψ.hom_inv_id
  inv_hom_id := by apply Grp.hom_ext; exact ψ.inv_hom_id

/-- Rank-one conjugation on actual coefficient points in an arbitrary affine
presentation; the underlying group law is the actual original group law. -/
def cyclicConjugationAction (χ : (Gm (Spec R)).toGrp ⟶ G) :
    TorusAction G.affinePointFunctor PUnit :=
  rankOneAction (corep G ψ) (χ ≫ (modelGroupIso ψ).inv)

/-- The actual coefficient formula for the presentation's conjugation action. -/
theorem cyclicConjugationAction_act (χ : (Gm (Spec R)).toGrp ⟶ G)
    {A : CommAlgCat.{u} R} (s : PUnit → Aˣ) (x : G.affinePointFunctor.obj A) :
    (cyclicConjugationAction ψ χ).act s x =
      (show G.affinePointFunctor.obj A from
        unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (s PUnit.unit) ≫
          χ.hom.hom) * x *
      (show G.affinePointFunctor.obj A from
        unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) (s PUnit.unit) ≫
          χ.hom.hom)⁻¹ := by
  have h := congrArg (fun y => y ≫ (modelGroupIso ψ).hom.hom.hom)
    (affinePoint_rankOneAction (corep G ψ) (χ ≫ (modelGroupIso ψ).inv) s x)
  have hr (y : G.affinePointFunctor.obj A) :
      affinePoint (corep G ψ) y ≫ (modelGroupIso ψ).hom.hom.hom = y := by
    have he := affinePointsEquiv_eq G ψ A
      (affinePoint (corep G ψ) y)
    exact he.symm.trans ((affinePointsEquiv G.affinePointFunctor (corep G ψ) A).apply_symm_apply y)
  simp only [MonObj.mul_comp, GrpObj.inv_comp] at h
  simp only [hr] at h
  simpa only [cyclicConjugationAction, Grp.comp_hom_hom, Category.assoc,
    iso_inv_hom_hom, Category.comp_id] using h

/-- The intrinsic cyclic cutoff on the original actual affine group. -/
def cyclicConjugationCutoff (χ : (Gm (Spec R)).toGrp ⟶ G) (r : ℕ) :
    SubgroupFunctor G :=
  intrinsicWeightSubgroup ψ (cyclicConjugationAction ψ χ)
    (cyclicTail (fun _ : PUnit => (1 : ℤ)) r)

/-- Its first positive cutoff is exactly the dynamic contracting subgroup on
all scheme tests, over the arbitrary original ring. -/
theorem cyclicConjugationCutoff_one (χ : (Gm (Spec R)).toGrp ⟶ G) :
    cyclicConjugationCutoff ψ χ 1 = Dynamic.unipotent χ := by
  change (rankOneFirstCut (corep G ψ) (χ ≫ (modelGroupIso ψ).inv)).comap
    (modelGroupIso ψ).inv = _
  rw [rankOne_firstCut_eq_unipotent]
  exact (Dynamic.unipotent_eq_comap_of_iso χ (modelGroupIso ψ).symm).symm

/-- Later positive cutoffs lie in the actual contracting subgroup. -/
theorem cyclicConjugationCutoff_le_unipotent (χ : (Gm (Spec R)).toGrp ⟶ G)
    (r : ℕ) (hr : 0 < r) :
    cyclicConjugationCutoff ψ χ r ≤ Dynamic.unipotent χ := by
  rw [← cyclicConjugationCutoff_one ψ χ]
  intro T x hx
  rw [cyclicConjugationCutoff, intrinsicWeightSubgroup, SubgroupFunctor.mem_comap,
    mem_cutSubgroupFunctor] at hx ⊢
  have ht : cyclicTail (fun _ : PUnit.{u + 1} => (1 : ℤ)) r ≤
      cyclicTail (fun _ : PUnit.{u + 1} => (1 : ℤ)) 1 := by
    rintro m ⟨n, hn, hpos, he⟩
    exact ⟨n, by omega, hpos, he⟩
  intro b m hm
  exact hx b m (fun hmr => hm (ht hmr))

end Langlands.GroupScheme.AffineCorepresentation
