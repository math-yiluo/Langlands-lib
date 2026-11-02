import Langlands.GroupScheme.Dynamic.Basic
import Langlands.Group.LeftQuotient

/-! # Improper dynamic parabolics and their actual quotient spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The cocharacter with constant identity value on every test scheme. -/
def trivialCocharacter : (Gm S).toGrp ⟶ G :=
  homOfPoints (fun _ => 1) (by
    intro T T' a x
    exact (MonObj.comp_one a).symm)

@[simp] theorem comp_trivialCocharacter {T : Over S} (x : T ⟶ (Gm S).X) :
    x ≫ (trivialCocharacter G).hom.hom = 1 := by
  unfold trivialCocharacter
  exact comp_homOfPoints (fun _ => 1) (by
    intro T T' a x
    exact (MonObj.comp_one a).symm) T x

@[simp] theorem orbit_trivialCocharacter {T : Over S} (g : T ⟶ G.X) :
    orbit (trivialCocharacter G) g = fst T (Gm S).X ≫ g := by
  simp [orbit]

/-- The trivial cocharacter centralizes every point on every test scheme. -/
@[simp] theorem centralizer_trivialCocharacter :
    centralizer (trivialCocharacter G) = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp [mem_centralizer]

variable {G} (χ : (Gm S).toGrp ⟶ G)

/-- A full centralizer on a test scheme makes the dynamic parabolic full there. -/
theorem parabolic_carrier_eq_top_of_centralizer
    (T : Over S) (hχ : (centralizer χ).carrier T = ⊤) :
    (parabolic χ).carrier T = ⊤ := by
  apply top_unique
  intro g _
  apply centralizer_le_parabolic χ T
  change g ∈ (centralizer χ).carrier T
  rw [hχ]
  exact Subgroup.mem_top g

/-- If the cocharacter centralizes the group functor, its dynamic parabolic is the whole group. -/
theorem parabolic_eq_top_of_centralizer (hχ : centralizer χ = ⊤) :
    parabolic χ = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply parabolic_carrier_eq_top_of_centralizer χ T
  simp [hχ]

@[simp] theorem parabolic_trivialCocharacter :
    parabolic (trivialCocharacter G) = ⊤ :=
  parabolic_eq_top_of_centralizer _ (centralizer_trivialCocharacter G)

/-- Every point of a commutative group scheme centralizes every cocharacter. -/
theorem centralizer_eq_top_of_commutative (C : CommGroupScheme S)
    (χ : (Gm S).toGrp ⟶ C.toGrp) : centralizer χ = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true, mem_centralizer]
  dsimp [orbit]
  rw [mul_comm (snd T (Gm S).X ≫ χ.hom.hom), mul_inv_cancel_right]

/-- All dynamic parabolics of a commutative group scheme are improper. -/
theorem parabolic_eq_top_of_commutative (C : CommGroupScheme S)
    (χ : (Gm S).toGrp ⟶ C.toGrp) : parabolic χ = ⊤ :=
  parabolic_eq_top_of_centralizer χ (centralizer_eq_top_of_commutative C χ)

/-- Both actual quotient conventions of an improper dynamic parabolic are singletons. -/
theorem subsingleton_quotients_of_parabolic_eq_top (T : Over S)
    (hP : (parabolic χ).carrier T = ⊤) :
    Subsingleton ((T ⟶ G.X) ⧸ (parabolic χ).carrier T) ∧
      Subsingleton (Langlands.Induction.LeftQuotient ((parabolic χ).carrier T)) := by
  rw [hP]
  constructor
  · constructor
    intro x y
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        apply Quotient.sound
        change QuotientGroup.leftRel (⊤ : Subgroup (T ⟶ G.X)) a b
        rw [QuotientGroup.leftRel_apply]
        exact Subgroup.mem_top _
  · constructor
    intro x y
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        apply Quotient.sound
        change QuotientGroup.rightRel (⊤ : Subgroup (T ⟶ G.X)) a b
        rw [QuotientGroup.rightRel_apply]
        exact Subgroup.mem_top _

/-- Both actual quotients of an improper dynamic parabolic are compact for any point topology. -/
theorem compact_quotients_of_parabolic_eq_top (T : Over S)
    [TopologicalSpace (T ⟶ G.X)] (hP : (parabolic χ).carrier T = ⊤) :
    CompactSpace ((T ⟶ G.X) ⧸ (parabolic χ).carrier T) ∧
      CompactSpace (Langlands.Induction.LeftQuotient ((parabolic χ).carrier T)) := by
  have h := subsingleton_quotients_of_parabolic_eq_top χ T hP
  let := h.1
  let := h.2
  exact ⟨inferInstance, inferInstance⟩

/-- In particular the trivial cocharacter gives compact quotients for every point topology. -/
theorem compact_quotients_trivialCocharacter (T : Over S)
    [TopologicalSpace (T ⟶ G.X)] :
    CompactSpace ((T ⟶ G.X) ⧸ (parabolic (trivialCocharacter G)).carrier T) ∧
      CompactSpace (Langlands.Induction.LeftQuotient
        ((parabolic (trivialCocharacter G)).carrier T)) := by
  apply compact_quotients_of_parabolic_eq_top
  simp

end Langlands.GroupScheme.Dynamic
