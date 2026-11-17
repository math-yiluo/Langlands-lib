import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.Rational.Characters

/-! # The left-right action attached to two group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} {H G : GroupScheme S}

/-- The morphism `(h, x) ↦ f(h) x g(h)⁻¹`. -/
def leftRightHom (f g : H ⟶ G) : H.X ⊗ G.X ⟶ G.X :=
  (fst H.X G.X ≫ f.hom.hom) * snd H.X G.X *
    (fst H.X G.X ≫ g.hom.hom)⁻¹

@[simp] theorem lift_leftRightHom (f g : H ⟶ G) {V : Over S}
    (h : V ⟶ H.X) (x : V ⟶ G.X) :
    lift h x ≫ leftRightHom f g =
      (h ≫ f.hom.hom) * x * (h ≫ g.hom.hom)⁻¹ := by
  simp only [leftRightHom, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd]

/-- Left translation through `f` and right inverse translation through `g` give
a lawful scheme action for arbitrary homomorphisms `f` and `g`. -/
@[instance_reducible] def leftRightAction (f g : H ⟶ G) : SchemeAction H G.X :=
  schemeActionOfPointLaws (leftRightHom f g)
    (fun x => by simp only [lift_leftRightHom, MonObj.one_comp, one_mul, inv_one, mul_one])
    (fun h h' x => by
      simp only [lift_leftRightHom, MonObj.mul_comp, mul_inv_rev]
      simp only [mul_assoc])

@[simp] theorem leftRightAction_hom (f g : H ⟶ G) :
    (leftRightAction f g).hom = leftRightHom f g := rfl

@[simp] theorem leftRightAction_act (f g : H ⟶ G) {V : Over S}
    (h : V ⟶ H.X) (x : V ⟶ G.X) :
    (leftRightAction f g).act h x =
      (h ≫ f.hom.hom) * x * (h ≫ g.hom.hom)⁻¹ :=
  lift_leftRightHom f g h x

/-- The left-right action is trivial exactly when the homomorphisms agree
and their common value is central. -/
theorem leftRightHom_eq_snd_iff (f g : H ⟶ G) :
    leftRightHom f g = snd H.X G.X ↔ f = g ∧ IsCentral f := by
  have htriv (he : leftRightHom f g = snd H.X G.X)
      {V : Over S} (h : V ⟶ H.X) (x : V ⟶ G.X) :
      (h ≫ f.hom.hom) * x * (h ≫ g.hom.hom)⁻¹ = x := by
    rw [← lift_leftRightHom, he, lift_snd]
  constructor
  · intro he
    have hfg : f = g := by
      apply Grp.hom_ext
      simpa only [Category.id_comp, mul_one, mul_inv_eq_one] using
        htriv he (𝟙 H.X) (1 : H.X ⟶ G.X)
    refine ⟨hfg, ?_⟩
    intro V h
    apply mem_center.mpr
    intro V' b x
    change (b ≫ (h ≫ f.hom.hom)) * x = x * (b ≫ (h ≫ f.hom.hom))
    have hx := htriv he (b ≫ h) x
    rw [← hfg] at hx
    simpa only [Category.assoc] using (mul_inv_eq_iff_eq_mul).mp hx
  · rintro ⟨rfl, hc⟩
    have hp := (commute_of_mem_center (hc (H.X ⊗ G.X) (fst H.X G.X))
      (snd H.X G.X)).eq
    change (_ * _) * _⁻¹ = _
    rw [hp, mul_inv_cancel_right]

/-- The actual left-right morphism commutes with arbitrary base change. -/
theorem baseChange_leftRightHom (b : T ⟶ S) (f g : H ⟶ G) :
    Functor.LaxMonoidal.μ (Over.pullback b) H.X G.X ≫
        (Over.pullback b).map (leftRightHom f g) =
      leftRightHom ((baseChange b).map f) ((baseChange b).map g) := by
  simp only [leftRightHom, Functor.map_mul, Functor.map_inv', Functor.map_comp,
    MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd]
  rfl

/-- Rigidity of actions under a given base change implies uniqueness of two
homomorphisms with the same central reduction. -/
theorem eq_of_central_reduction_of_action_rigidity (b : T ⟶ S)
    (hrig : ∀ a : SchemeAction H G.X,
      Functor.LaxMonoidal.μ (Over.pullback b) H.X G.X ≫
          (Over.pullback b).map a.hom =
        snd ((baseChange b).obj H).X ((baseChange b).obj G).X →
      a.hom = snd H.X G.X)
    (f g : H ⟶ G)
    (he : (baseChange b).map f = (baseChange b).map g)
    (hc : IsCentral ((baseChange b).map f)) :
    f = g := by
  apply ((leftRightHom_eq_snd_iff f g).mp ?_).1
  apply hrig (leftRightAction f g)
  rw [leftRightAction_hom, baseChange_leftRightHom]
  exact (leftRightHom_eq_snd_iff _ _).mpr ⟨he, hc⟩

end Langlands.GroupScheme
