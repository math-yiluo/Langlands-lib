import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Maximal central relative tori and the centre factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G C Z Z' : GroupScheme S}

/-- A closed central relative torus containing every closed central relative torus. -/
def IsMaximalCentralRelativeTorus (z : Z ⟶ G) : Prop :=
  IsClosedSubgroup z ∧ IsCentral z ∧ RelativeTorus.IsTorus Z ∧
    ∀ (Z' : GroupScheme S) (z' : Z' ⟶ G), IsClosedSubgroup z' → IsCentral z' →
      RelativeTorus.IsTorus Z' → SubgroupFunctor.range z' ≤ SubgroupFunctor.range z

/-- Two maximal central relative tori define the same subgroup functor. -/
theorem IsMaximalCentralRelativeTorus.range_eq {z : Z ⟶ G} {z' : Z' ⟶ G}
    (hz : IsMaximalCentralRelativeTorus z) (hz' : IsMaximalCentralRelativeTorus z') :
    SubgroupFunctor.range z = SubgroupFunctor.range z' :=
  le_antisymm
    (hz'.2.2.2 Z z hz.1 hz.2.1 hz.2.2.1)
    (hz.2.2.2 Z' z' hz'.1 hz'.2.1 hz'.2.2.1)

/-- A largest subtorus of the full centre is a maximal central relative torus. -/
theorem isMaximalCentralRelativeTorus_comp_center
    (c : C ⟶ G) (hc : IsSchemeTheoreticCenter c)
    (t : Z ⟶ C) (ht : IsClosedSubgroup t) (hZ : RelativeTorus.IsTorus Z)
    (hmax : ∀ (T : GroupScheme S) (t' : T ⟶ C),
      IsClosedSubgroup t' → RelativeTorus.IsTorus T → ∃ f : T ⟶ Z, f ≫ t = t') :
    IsMaximalCentralRelativeTorus (t ≫ c) := by
  refine ⟨ht.comp hc.1, hc.isCentral.comp t, hZ, ?_⟩
  intro T t' ht' htc hT
  let f : T ⟶ C :=
    hc.isRepresentedBy.factorHom t' ((isCentral_iff_range_le_center t').mp htc)
  have hf : f ≫ c = t' := hc.isRepresentedBy.factorHom_comp _ _
  have hfc : IsClosedSubgroup f := hc.1.of_comp (by rw [hf]; exact ht')
  obtain ⟨g, hg⟩ := hmax T f hfc hT
  have he : g ≫ (t ≫ c) = t' := by rw [← Category.assoc, hg, hf]
  rintro U x ⟨y, rfl⟩
  refine ⟨y ≫ g.hom.hom, ?_⟩
  change (y ≫ g.hom.hom) ≫ (t ≫ c).hom.hom = y ≫ t'.hom.hom
  calc
    (y ≫ g.hom.hom) ≫ (t ≫ c).hom.hom =
        y ≫ (g ≫ (t ≫ c)).hom.hom := by
      change (y ≫ g.hom.hom) ≫ (t ≫ c).hom.hom =
        y ≫ (g.hom.hom ≫ (t ≫ c).hom.hom)
      exact Category.assoc _ _ _
    _ = y ≫ t'.hom.hom :=
      congrArg (fun a : T ⟶ G => y ≫ a.hom.hom) he

/-- The existence part requires only a represented centre and a largest subtorus of it. -/
theorem exists_maximalCentralRelativeTorus_of_center
    (c : C ⟶ G) (hc : IsSchemeTheoreticCenter c)
    (h : ∃ (Z : GroupScheme S) (t : Z ⟶ C),
      IsClosedSubgroup t ∧ RelativeTorus.IsTorus Z ∧
        ∀ (T : GroupScheme S) (t' : T ⟶ C),
          IsClosedSubgroup t' → RelativeTorus.IsTorus T →
            ∃ f : T ⟶ Z, f ≫ t = t') :
    ∃ (Z : GroupScheme S) (z : Z ⟶ G), IsMaximalCentralRelativeTorus z := by
  obtain ⟨Z, t, ht, hZ, hmax⟩ := h
  exact ⟨Z, t ≫ c, isMaximalCentralRelativeTorus_comp_center c hc t ht hZ hmax⟩

end Langlands.GroupScheme
