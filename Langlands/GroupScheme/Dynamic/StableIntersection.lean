import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.SubgroupFunctorProduct

/-! # Dynamic decompositions inside closed invariant subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G)
    {F : SubgroupFunctor G} {j : H ⟶ G}

/-- A limit of a point of a closed invariant subgroup remains in that subgroup,
including for nonreduced test schemes. -/
theorem HasLimit.mem_of_isClosedSubgroup_of_isStable
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F)
    {T : Over S} {g l : T ⟶ G.X} (hg : g ∈ F.carrier T)
    (hl : HasLimit χ g l) : l ∈ F.carrier T := by
  obtain ⟨e, he, rfl⟩ := hl
  have ho : orbit χ g ∈ F.carrier (T ⊗ (Gm S).X) := by
    have h := hF _ (snd T (Gm S).X) (fst T (Gm S).X ≫ g)
      (F.comp_mem (fst T (Gm S).X) hg)
    simpa only [AutomorphicAction.conjugation_act, orbit] using h
  rw [← hj.2] at ho ⊢
  obtain ⟨o, ho⟩ := SubgroupFunctor.mem_range.mp ho
  have : IsClosedImmersion j.hom.hom.left := hjc
  obtain ⟨e', he'⟩ := AffineLine.exists_lift_of_unitInclusion j.hom.hom e o
    (ho.trans he.symm)
  exact SubgroupFunctor.mem_range.mpr ⟨evalZero e', by rw [← evalZero_comp, he']⟩

variable [IsSeparated G.X.hom]

/-- The limit homomorphism restricted to a closed invariant subgroup, with
values in the corresponding centralizer intersection. -/
def infParabolicLimitHom
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F) (T : Over S) :
    (F ⊓ parabolic χ).carrier T →* (F ⊓ centralizer χ).carrier T where
  toFun g := by
    let gP : (parabolic χ).carrier T := ⟨g, g.2.2⟩
    have hl : HasLimit χ (g : T ⟶ G.X) (limit χ gP) := hasLimit_limit χ gP
    have hlF := hl.mem_of_isClosedSubgroup_of_isStable χ hj hjc hF g.2.1
    exact ⟨limit χ gP, hlF, limit_mem_centralizer χ gP⟩
  map_one' := Subtype.ext (congrArg (fun z : (centralizer χ).carrier T =>
    (z : T ⟶ G.X)) (map_one (limitHom χ T)))
  map_mul' g h := Subtype.ext (congrArg (fun z : (centralizer χ).carrier T =>
    (z : T ⟶ G.X)) (map_mul (limitHom χ T) ⟨g, g.2.2⟩ ⟨h, h.2.2⟩))

/-- The restricted limit homomorphism commutes with every change of test scheme. -/
theorem infParabolicLimitHom_comp
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F)
    {T T' : Over S} (a : T' ⟶ T) (g : (F ⊓ parabolic χ).carrier T) :
    (infParabolicLimitHom χ hj hjc hF T'
      ⟨a ≫ g, (F ⊓ parabolic χ).comp_mem a g.2⟩ : T' ⟶ G.X) =
      a ≫ (infParabolicLimitHom χ hj hjc hF T g : T ⟶ G.X) :=
  limitHom_comp χ a ⟨g, g.2.2⟩

/-- The dynamic decomposition restricts to any closed subgroup invariant under
the cocharacter action, with both factors defined over the original test scheme. -/
theorem inf_parabolic_isPointwiseProduct_of_isStable
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F) :
    (F ⊓ parabolic χ).IsPointwiseProduct (F ⊓ centralizer χ) (F ⊓ unipotent χ) := by
  intro T g
  constructor
  · rintro ⟨hgF, hgP⟩
    obtain ⟨l, hl⟩ := exists_hasLimit χ hgP
    have hlF := hl.mem_of_isClosedSubgroup_of_isStable χ hj hjc hF hgF
    have hlZ := hl.mem_centralizer χ
    have hu : l⁻¹ * g ∈ (unipotent χ).carrier T := by
      apply (mem_unipotent χ).mpr
      have h := (hasLimit_of_mem_centralizer χ hlZ).inv.mul χ hl
      simpa only [inv_mul_cancel] using h
    exact ⟨l, ⟨hlF, hlZ⟩, l⁻¹ * g,
      ⟨(F.carrier T).mul_mem ((F.carrier T).inv_mem hlF) hgF, hu⟩,
      mul_inv_cancel_left l g⟩
  · rintro ⟨l, ⟨hlF, hlZ⟩, n, ⟨hnF, hnU⟩, rfl⟩
    exact ⟨mul_mem hlF hnF,
      mul_mem (centralizer_le_parabolic χ T hlZ) (unipotent_le_parabolic χ T hnU)⟩

/-- The ordered product as a literal equality of subsets on each test scheme. -/
theorem inf_parabolic_eq_mul_of_isStable
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F) (T : Over S) :
    (↑((F ⊓ parabolic χ).carrier T) : Set (T ⟶ G.X)) =
      (↑((F ⊓ centralizer χ).carrier T) : Set (T ⟶ G.X)) *
        (↑((F ⊓ unipotent χ).carrier T) : Set (T ⟶ G.X)) := by
  ext g
  exact inf_parabolic_isPointwiseProduct_of_isStable χ hj hjc hF T g

end Langlands.GroupScheme.Dynamic
