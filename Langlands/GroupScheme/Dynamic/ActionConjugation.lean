import Langlands.GroupScheme.Dynamic.Action

/-! # Restriction of conjugation and cocharacter dynamic comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H K G : GroupScheme S}

namespace AutomorphicAction

/-- The action morphism is determined by all its point actions. -/
theorem ext_act {a b : AutomorphicAction H G}
    (h : ∀ {T : Over S} (x : T ⟶ H.X) (g : T ⟶ G.X), a.act x g = b.act x g) :
    a = b := by
  have hh : a.hom = b.hom := by
    simpa only [act, lift_fst_snd, Category.id_comp] using
      h (fst H.X G.X) (snd H.X G.X)
  cases a
  cases b
  cases hh
  rfl

/-- Restricting conjugation agrees with conjugation along the composite homomorphism. -/
theorem restrict_conjugation (i : H ⟶ G) (f : K ⟶ H) :
    (conjugation i).restrict f = conjugation (f ≫ i) := by
  apply ext_act
  intro T h g
  simp only [restrict_act, conjugation_act, Grp.comp_hom_hom, Category.assoc]

variable (χ : (Gm S).toGrp ⟶ G)

/-- The automorphic action obtained by restricting ambient conjugation along a cocharacter. -/
def cocharacterAction : AutomorphicAction (Gm S).toGrp G :=
  (conjugation (𝟙 G)).restrict χ

/-- The restricted ambient action is conjugation along the cocharacter itself. -/
theorem cocharacterAction_eq_conjugation : cocharacterAction χ = conjugation χ := by
  simpa only [cocharacterAction, Category.comp_id] using restrict_conjugation (𝟙 G) χ

/-- On every test scheme, the restricted action is the usual conjugation formula. -/
@[simp] theorem cocharacterAction_act {T : Over S}
    (t : T ⟶ (Gm S).X) (g : T ⟶ G.X) :
    (cocharacterAction χ).act t g =
      (t ≫ χ.hom.hom) * g * (t ≫ χ.hom.hom)⁻¹ := by
  rw [cocharacterAction_eq_conjugation, conjugation_act]

/-- Equality of the actual abstract-action orbit morphism with the published orbit. -/
theorem cocharacterAction_orbit {T : Over S} (g : T ⟶ G.X) :
    (cocharacterAction χ).orbit g = Dynamic.orbit χ g := by
  change (cocharacterAction χ).act (snd T (Gm S).X)
    (fst T (Gm S).X ≫ g) = _
  rw [cocharacterAction_act]
  rfl

/-- The two extension predicates use the same morphism from the affine line. -/
theorem cocharacterAction_isOrbitExtension {T : Over S} (g : T ⟶ G.X)
    (e : T ⊗ AffineLine.scheme S ⟶ G.X) :
    (cocharacterAction χ).IsOrbitExtension g e ↔ Dynamic.IsOrbitExtension χ g e := by
  change (T ◁ AffineLine.unitInclusion S ≫ e = (cocharacterAction χ).orbit g) ↔
    (T ◁ AffineLine.unitInclusion S ≫ e = Dynamic.orbit χ g)
  rw [cocharacterAction_orbit]

/-- The abstract and cocharacter limit predicates agree, using the same zero evaluation. -/
theorem cocharacterAction_hasLimit {T : Over S} (g l : T ⟶ G.X) :
    (cocharacterAction χ).HasLimit g l ↔ Dynamic.HasLimit χ g l := by
  change (∃ e, (cocharacterAction χ).IsOrbitExtension g e ∧ Dynamic.evalZero e = l) ↔
    (∃ e, Dynamic.IsOrbitExtension χ g e ∧ Dynamic.evalZero e = l)
  simp only [cocharacterAction_isOrbitExtension]

/-- The abstract dynamic parabolic equals the published cocharacter subgroup functor. -/
theorem cocharacterAction_parabolic :
    (cocharacterAction χ).parabolic = Dynamic.parabolic χ := by
  apply SubgroupFunctor.ext
  intro T
  ext g
  rw [mem_parabolic, Dynamic.mem_parabolic]
  simp only [cocharacterAction_isOrbitExtension]

/-- The invariant functor equals the published cocharacter centralizer on every test. -/
theorem cocharacterAction_centralizer :
    (cocharacterAction χ).centralizer = Dynamic.centralizer χ := by
  change (cocharacterAction χ).fixedSubgroup = Dynamic.centralizer χ
  rw [cocharacterAction_eq_conjugation, conjugation_fixedSubgroup_eq_torusCentralizer,
    torusCentralizer_gm_eq_dynamicCentralizer]

/-- The abstract identity-limit subgroup equals the published cocharacter subgroup functor. -/
theorem cocharacterAction_unipotent :
    (cocharacterAction χ).unipotent = Dynamic.unipotent χ := by
  apply SubgroupFunctor.ext
  intro T
  ext g
  rw [mem_unipotent, Dynamic.mem_unipotent, cocharacterAction_hasLimit]

end AutomorphicAction

end Langlands.GroupScheme
