import Langlands.GroupScheme.Adjoint.CenterQuotientStatement
import Langlands.GroupScheme.Adjoint.QuotientDescent
import Langlands.GroupScheme.Adjoint.SecondCenter

/-! # Trivial centre of a full-centre quotient from the second-centre property -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CenterQuotientCenter

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G Q : GroupScheme S}

/-- A point of the target is central exactly when its lifts have central commutators:
if `g ≫ q = z` with `z` central, every commutator of a restriction of `g` is killed by
`q`, hence lies in the centre of `G`. -/
theorem comm_mem_center_of_comp_mem_center (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = center G) {T : Over S} (g : T ⟶ G.X)
    (hg : g ≫ q.hom.hom ∈ (center Q).carrier T) (T' : Over S) (a : T' ⟶ T)
    (h : T' ⟶ G.X) : (a ≫ g) * h * (a ≫ g)⁻¹ * h⁻¹ ∈ (center G).carrier T' := by
  apply CenterQuotientDescent.mem_center_of_comp_eq_one q hker
  have hc : Commute (a ≫ g ≫ q.hom.hom) (h ≫ q.hom.hom) := hg T' a (h ≫ q.hom.hom)
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  rw [hc.eq, mul_inv_cancel_right, mul_inv_cancel]

/-- A central point of `G` is killed by a homomorphism whose kernel is the centre. -/
theorem comp_eq_one_of_mem_center (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) = center G) {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (center G).carrier T) : g ≫ q.hom.hom = 1 := by
  rw [← hker] at hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  exact (kernelPointsEquiv q T y).property

/-- **Formal reduction.** Let `q : G ⟶ Q` be an fppf homomorphism whose actual kernel is
the full centre of `G`. If `G` has trivial second centre, then the centre of `Q` is trivial
on every test. -/
theorem center_eq_bot_of_secondCenterTrivial (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (center G) q) (hG : SecondCenterTrivial G) :
    center Q = ⊥ := by
  obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
  refine SubgroupFunctor.ext fun T => (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  -- The fppf cover `T' = T ×_Q G` of `T` on which `z` lifts to a point `g` of `G`.
  let p₀ := pullback.fst z.left q.hom.hom.left
  have hflat' : Flat p₀ := MorphismProperty.pullback_fst (P := @Flat) _ _ hflat
  have hsurj' : Surjective p₀ := MorphismProperty.pullback_fst (P := @Surjective) _ _ hsurj
  have hlfp' : LocallyOfFinitePresentation p₀ :=
    MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation) _ _ hlfp
  let T' : Over S := Over.mk (p₀ ≫ T.hom)
  let p : T' ⟶ T := Over.homMk p₀ rfl
  let g : T' ⟶ G.X := Over.homMk (pullback.snd z.left q.hom.hom.left) (by
    change pullback.snd z.left q.hom.hom.left ≫ G.X.hom = p₀ ≫ T.hom
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition, Category.assoc,
      Over.w z])
  have hgz : g ≫ q.hom.hom = p ≫ z := Over.OverMorphism.ext pullback.condition.symm
  have hgc : g ∈ (center G).carrier T' := by
    apply hG T' g
    apply comm_mem_center_of_comp_mem_center q hker g
    rw [hgz]
    exact (center Q).comp_mem p hz
  have hpz : p ≫ z = p ≫ 1 := by
    rw [← hgz, comp_eq_one_of_mem_center q hker hgc, MonObj.comp_one]
  have : Epi p.left := show Epi p₀ from inferInstance
  have : Epi p := Over.epi_of_epi_left _
  exact (cancel_epi p).1 hpz

/-- The target statement follows once every connected reductive group over a field has
trivial second centre. -/
theorem centerQuotientCenterTrivial_of_secondCenterTrivial
    (h : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → SecondCenterTrivial G) :
    CenterQuotientCenterTrivialStatement.{u} :=
  fun k _ G _ q hG _ _ hq => center_eq_bot_of_secondCenterTrivial q hq (h k G hG)

end CenterQuotientCenter

end Langlands.GroupScheme
