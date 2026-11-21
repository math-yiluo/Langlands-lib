import Langlands.AlgebraicGeometry.ClosedRationalPoints
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientReduction

/-! # Lifting a conjugate family parameter through a smooth product cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

private theorem exists_lift_at_henselian_point {A : Type u} [CommRing A]
    [HenselianLocalRing A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Smooth p] [Surjective p]
    (x : Spec (CommRingCat.of A) ⟶ Y) :
    ∃ a : Spec (CommRingCat.of A) ⟶ X, a ≫ p = x := by
  let k := IsLocalRing.ResidueField A
  let i := Spec.algebraMap A k
  let Xk := Over.mk (pullback.snd p (i ≫ x))
  have : LocallyOfFiniteType Xk.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p (i ≫ x)))
  obtain ⟨w, _⟩ := (show Surjective (pullback.snd p (i ≫ x)) from inferInstance).surj
    (IsLocalRing.closedPoint k)
  obtain ⟨q, _⟩ := Langlands.AlgebraicGeometry.ClosedRationalPoints.exists_rationalPoint_mem
    (X := Xk) ⊤ ⟨w, trivial⟩
  obtain ⟨a, ha, _⟩ :=
    Langlands.AlgebraicGeometry.PointTopology.exists_smooth_lift_of_residue_point
      (IsLocalRing.residue_surjective (R := A)) p x (q.left ≫ pullback.fst p (i ≫ x))
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, show q.left ≫
        pullback.snd p (i ≫ x) = 𝟙 (Spec (CommRingCat.of k)) from Over.w q, Category.id_comp])
  exact ⟨a, ha⟩

section Compare

variable {S W : Scheme.{u}} {D Q L : GroupScheme S} {M : Over S} {K : GroupScheme M.left}

/-- Conjugacy of the lift of an evaluated inclusion identifies its subgroup
range with the corresponding actual conjugate in the ambient group. -/
theorem evaluate_eq_range_conjugatePullback_of_factor
    (a : W ⟶ S) (m : Q ⟶ L) (d : D ⟶ Q)
    (j : K ⟶ (baseChange M.hom).obj L) (b : Over.mk a ⟶ M)
    (c : (baseChange b.left).obj K ⟶ (baseChange a).obj Q)
    (hc : c ≫ (baseChange a).map m = familyHom j b)
    (z : Over.mk (𝟙 W) ⟶ ((baseChange a).obj Q).X)
    (σ : (baseChange a).obj D ≅ (baseChange b.left).obj K)
    (hσ : (baseChange a).map d ≫ (((baseChange a).obj Q).innerIso z).hom = σ.hom ≫ c) :
    evaluate j b = range (conjugatePullback a (d ≫ m) (z ≫ ((baseChange a).map m).hom.hom)) := by
  have h : conjugatePullback a (d ≫ m) (z ≫ ((baseChange a).map m).hom.hom) =
      σ.hom ≫ familyHom j b := by
    rw [conjugatePullback, Functor.map_comp, Category.assoc, ← innerIso_hom_comp,
      ← Category.assoc, hσ, Category.assoc, hc]
  rw [h, range_iso_comp, evaluate]

end Compare

section Lift

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
variable {S : Scheme.{u}} {G D Q L : GroupScheme S} {M : Over S} {K : GroupScheme M.left}

/-- A conjugator lifted through a smooth cover by `G × D` gives a `G`-parameter
of the evaluated subgroup. The factor from `D` normalizes the image of `D`, so
it does not change the conjugate family. -/
theorem exists_parameter_of_conjugate_of_smooth_product
    (a : Spec (CommRingCat.of A) ⟶ S) (ρ : G ⟶ L) (e : D ⟶ L) (m : Q ⟶ L)
    (p : G.X ⊗ D.X ⟶ Q.X) [Smooth p.left] [Surjective p.left]
    (hp : p ≫ m.hom.hom = (fst G.X D.X ≫ ρ.hom.hom) * (snd G.X D.X ≫ e.hom.hom))
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j)
    (f : G.X ⟶ M) (hf : evaluate j f = range (conjugateFamily e ρ.hom.hom))
    (b : Over.mk a ⟶ M) (z : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ ((baseChange a).obj Q).X)
    (hz : evaluate j b = range (conjugatePullback a e (z ≫ ((baseChange a).map m).hom.hom))) :
    ∃ h : Over.mk a ⟶ G.X, h ≫ f = b := by
  let z₀ := baseChangeBasePointsEquiv a Q z
  obtain ⟨x₀, hx₀⟩ := exists_lift_at_henselian_point p.left z₀.left
  let x : Over.mk a ⟶ G.X ⊗ D.X := Over.homMk x₀ (by
    change x₀ ≫ (G.X ⊗ D.X).hom = a
    rw [← Over.w p, ← Category.assoc, hx₀]
    exact Over.w z₀)
  have hx : x ≫ p = z₀ := Over.OverMorphism.ext hx₀
  let h := x ≫ fst G.X D.X
  let δ := x ≫ snd G.X D.X
  have hp' : z₀ ≫ m.hom.hom = (h ≫ ρ.hom.hom) * (δ ≫ e.hom.hom) := by
    rw [← hx, Category.assoc, hp, MonObj.comp_mul]
    simp only [h, δ, Category.assoc]
  have hnormal : (h ≫ ρ.hom.hom)⁻¹ * (z₀ ≫ m.hom.hom) ∈ (range e).normalizer.carrier _ := by
    apply (range e).le_normalizer
    rw [hp', inv_mul_cancel_left]
    exact mem_range.mpr ⟨δ, rfl⟩
  have hz' : conjugateFamily e (z₀ ≫ m.hom.hom) =
      conjugatePullback a e (z ≫ ((baseChange a).map m).hom.hom) := by
    change conjugatePullback a e ((baseChangeBasePointsEquiv a L).symm (z₀ ≫ m.hom.hom)) = _
    rw [show z₀ ≫ m.hom.hom = _ from (baseChangeBasePointsEquiv_comp a m z).symm,
      MulEquiv.symm_apply_apply]
  refine ⟨h, huni.evaluate_injective hK hj ?_⟩
  calc
    evaluate j (h ≫ f) = range (conjugateFamily e (h ≫ ρ.hom.hom)) := by
      rw [← evaluate_comp j f h]
      exact (evaluate_eq_of_range_eq (familyHom j f) _ hf h).trans
        (evaluate_conjugateFamily e ρ.hom.hom h)
    _ = range (conjugateFamily e (z₀ ≫ m.hom.hom)) :=
      range_conjugateFamily_eq_of_normalizer e _ _ hnormal
    _ = evaluate j b := by rw [hz', ← hz]

/-- Choose the `G`-parameter supplied by the smooth product lift, retaining the
exact equality with the original parameter. -/
def parameterOfConjugateOfSmoothProduct
    (a : Spec (CommRingCat.of A) ⟶ S) (ρ : G ⟶ L) (e : D ⟶ L) (m : Q ⟶ L)
    (p : G.X ⊗ D.X ⟶ Q.X) [Smooth p.left] [Surjective p.left]
    (hp : p ≫ m.hom.hom = (fst G.X D.X ≫ ρ.hom.hom) * (snd G.X D.X ≫ e.hom.hom))
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j)
    (f : G.X ⟶ M) (hf : evaluate j f = range (conjugateFamily e ρ.hom.hom))
    (b : Over.mk a ⟶ M) (z : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ ((baseChange a).obj Q).X)
    (hz : evaluate j b = range (conjugatePullback a e (z ≫ ((baseChange a).map m).hom.hom))) :
    {h : Over.mk a ⟶ G.X // h ≫ f = b} :=
  ⟨(exists_parameter_of_conjugate_of_smooth_product a ρ e m p hp j hj hK huni f hf b z hz).choose,
    (exists_parameter_of_conjugate_of_smooth_product a ρ e m p hp j hj hK huni f hf b z hz).choose_spec⟩

end Lift

end Langlands.GroupScheme.TorusSubgroupModuli
