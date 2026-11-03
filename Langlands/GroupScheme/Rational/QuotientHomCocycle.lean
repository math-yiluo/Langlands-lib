import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Difference cocycles for homomorphisms with equal quotient maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientHomCocycle

variable {S : Scheme.{u}} {H N G Q : GroupScheme S}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    (i₀ i₁ : H ⟶ G) (hi : i₀ ≫ q = i₁ ≫ q)

include hn in
/-- The given actual kernel is normalized by the first homomorphism. -/
theorem normalized :
    (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range i₀) := by
  intro T g x _ hx
  rw [hn, mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx]
  group

include hn hi in
/-- The difference of the two homomorphisms factors through the actual kernel. -/
theorem exists_difference :
    ∃ c : H.X ⟶ N.X, c ≫ n.hom.hom = i₁.hom.hom * i₀.hom.hom⁻¹ := by
  apply SubgroupFunctor.mem_range.1
  rw [hn, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp]
  have h : i₀.hom.hom ≫ q.hom.hom = i₁.hom.hom ≫ q.hom.hom :=
    congrArg (fun f : H ⟶ Q => f.hom.hom) hi
  rw [h, mul_inv_cancel]

/-- The actual kernel-valued difference morphism. -/
def difference : H.X ⟶ N.X :=
  Classical.choose (exists_difference n q hn i₀ i₁ hi)

@[reassoc]
theorem difference_comp :
    difference n q hn i₀ i₁ hi ≫ n.hom.hom = i₁.hom.hom * i₀.hom.hom⁻¹ :=
  Classical.choose_spec (exists_difference n q hn i₀ i₁ hi)

theorem comp_difference_comp {T : Over S} (h : T ⟶ H.X) :
    (h ≫ difference n q hn i₀ i₁ hi) ≫ n.hom.hom =
      (h ≫ i₁.hom.hom) * (h ≫ i₀.hom.hom)⁻¹ := by
  rw [Category.assoc, difference_comp, MonObj.comp_mul, GrpObj.comp_inv]

variable [Mono n.hom.hom]

/-- Conjugation on the kernel along the first homomorphism. -/
def action : AutomorphicAction H N :=
  AutomorphicAction.ofNormalizedConjugation n i₀ (normalized n q hn i₀)

theorem action_act_comp {T : Over S} (h : T ⟶ H.X) (v : T ⟶ N.X) :
    (action n q hn i₀).act h v ≫ n.hom.hom =
      (h ≫ i₀.hom.hom) * (v ≫ n.hom.hom) * (h ≫ i₀.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp n i₀ (normalized n q hn i₀) h v

/-- Equal quotient maps produce an actual normalized cocycle for kernel conjugation. -/
def cocycle : (action n q hn i₀).Cocycle (Over.mk (𝟙 S)) where
  hom := snd (Over.mk (𝟙 S)) H.X ≫ difference n q hn i₀ i₁ hi
  one b := by
    apply (cancel_mono n.hom.hom).1
    rw [← Category.assoc, lift_snd, comp_difference_comp, MonObj.one_comp,
      MonObj.one_comp, MonObj.one_comp]
    simp
  mul b h h' := by
    apply (cancel_mono n.hom.hom).1
    simp only [← Category.assoc, lift_snd, comp_difference_comp, MonObj.mul_comp,
      action_act_comp]
    group

@[simp]
theorem cocycle_eval {T : Over S} (b : T ⟶ Over.mk (𝟙 S)) (h : T ⟶ H.X) :
    (cocycle n q hn i₀ i₁ hi).eval b h = h ≫ difference n q hn i₀ i₁ hi := by
  simp only [AutomorphicAction.Cocycle.eval, cocycle, lift_snd_assoc]

private theorem difference_eq_iff {A : Type*} [Group A] (a b v : A) :
    b * a⁻¹ = v * (a * v⁻¹ * a⁻¹) ↔ v * a * v⁻¹ = b := by
  constructor
  · intro e
    calc
      v * a * v⁻¹ = (v * (a * v⁻¹ * a⁻¹)) * a := by group
      _ = (b * a⁻¹) * a := by rw [← e]
      _ = b := by group
  · intro e
    rw [← e]
    group

set_option maxHeartbeats 800000 in
/-- The difference is the coboundary of a supplied kernel point exactly when
that point conjugates the first homomorphism to the second. -/
theorem cocycle_eq_coboundary_iff (v : Over.mk (𝟙 S) ⟶ N.X) :
    cocycle n q hn i₀ i₁ hi = (action n q hn i₀).coboundary v ↔
      i₀ ≫ (G.innerIso (v ≫ n.hom.hom)).hom = i₁ := by
  constructor
  · intro hc
    apply hom_ext_points
    intro T h
    have e := congrArg (fun c : (action n q hn i₀).Cocycle (Over.mk (𝟙 S)) =>
      c.eval (Over.homMk T.hom (by simp)) h ≫ n.hom.hom) hc
    rw [cocycle_eval, comp_difference_comp,
      AutomorphicAction.eval_coboundary, MonObj.mul_comp, action_act_comp,
      GrpObj.inv_comp] at e
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    dsimp only [GroupScheme.constantPoint]
    simp only [Category.assoc] at e
    exact (difference_eq_iff _ _ _).1 e
  · intro hc
    apply AutomorphicAction.Cocycle.eval_ext
    intro T b h
    apply (cancel_mono n.hom.hom).1
    rw [cocycle_eval, comp_difference_comp,
      AutomorphicAction.eval_coboundary, MonObj.mul_comp, action_act_comp,
      GrpObj.inv_comp]
    have e := congrArg (fun f : H ⟶ G => h ≫ f.hom.hom) hc
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at e
    have hb : b = Over.homMk T.hom (by simp) := by
      apply Over.OverMorphism.ext
      simpa using b.w
    rw [hb]
    dsimp only [GroupScheme.constantPoint] at e
    simp only [Category.assoc]
    exact (difference_eq_iff _ _ _).2 e

/-- A coboundary witness gives rational conjugacy with the identity source isomorphism. -/
theorem subgroupConjugate_of_coboundary
    (v : Over.mk (𝟙 S) ⟶ N.X)
    (hv : cocycle n q hn i₀ i₁ hi = (action n q hn i₀).coboundary v) :
    SubgroupConjugate i₀ i₁ := by
  refine ⟨v ≫ n.hom.hom, Iso.refl H, ?_⟩
  simpa only [Iso.refl_hom, Category.id_comp] using
    (cocycle_eq_coboundary_iff n q hn i₀ i₁ hi v).1 hv

end Langlands.GroupScheme.QuotientHomCocycle
