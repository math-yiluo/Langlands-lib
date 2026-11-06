import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Noncommuting points of nontrivial semisimple field groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A nontrivial semisimple group over any field is noncommutative on its
full functor of points. -/
theorem IsSemisimple.noncommutative_of_nontrivial
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    ¬ ∀ (U : Over (Spec (CommRingCat.of k))) (x y : U ⟶ G.X), Commute x y := by
  intro hcomm
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  let f : G ⟶ Z := hz.isRepresentedBy.factorHom (𝟙 G) (by
    intro U x _ V a y
    exact hcomm V (a ≫ x) y)
  have hf : f ≫ z = 𝟙 G := hz.isRepresentedBy.factorHom_comp _ _
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp hz.1 (by
    rw [hf]
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance)
  let : IsClosedImmersion f.hom.hom.left := hfc
  let : IsFinite Z.X.hom := hfin
  let : IsFinite G.X.hom := by
    rw [← f.hom.hom.w]
    infer_instance
  let q : G ⟶ Grp.trivial (Over (Spec (CommRingCat.of k))) :=
    default
  let b : G ⟶ G := Grp.homMk (toUnit G.X ≫ η[G.X])
  have hqunit : q.hom.hom = toUnit G.X := toUnit_unique _ _
  have : IsFinite q.hom.hom.left := by
    rw [hqunit]
    exact inferInstanceAs (IsFinite G.X.hom)
  have hq : (𝟙 G) ≫ q = b ≫ q := by
    apply Grp.hom_ext
    exact toUnit_unique _ _
  have hid : (𝟙 G.X : G.X ⟶ G.X) = 1 := by
    have h := congrArg (fun a => a.hom.hom) (finiteHom_cancel q hq)
    exact h
  apply hnt
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    change x = 1
    calc
      x = x ≫ (𝟙 G.X) := (Category.comp_id _).symm
      _ = 1 := by rw [hid, MonObj.comp_one]
  · intro _
    refine ⟨x, ?_⟩
    change x ≫ (𝟙 G.X) = x
    exact Category.comp_id _

/-- Choose an actual test scheme and two of its points that do not commute.
Nontriviality concerns the whole represented functor, not only rational points. -/
def IsSemisimple.noncommutingPoints
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    Σ U : Over (Spec (CommRingCat.of k)),
      {xy : (U ⟶ G.X) × (U ⟶ G.X) // ¬ Commute xy.1 xy.2} := by
  classical
  have hex : ∃ (U : Over (Spec (CommRingCat.of k))) (x y : U ⟶ G.X),
      ¬ Commute x y := by
    simpa only [not_forall] using hG.noncommutative_of_nontrivial hnt
  choose U x y hxy using hex
  exact ⟨U, (x, y), hxy⟩

end Langlands.GroupScheme
