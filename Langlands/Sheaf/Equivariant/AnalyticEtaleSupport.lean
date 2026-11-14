import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Langlands.Geometry.Analytic.EtaleOpenDomains.Statement

/-! # Underlying-point support of global analytic étale sections -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}

/-- Field-valued points lift to every étale neighborhood of their underlying
point. This is a property, rather than additional point data. -/
def EtalePointLifting : Prop :=
  ∀ (x : (localizedFieldPointFunctor L).obj X) (U : EtaleSite X),
    pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map U.hom) →
      Nonempty ((EtaleSite.pointFibre L x).obj U)

/-- The point axioms give lifting when the complement of the underlying
point is represented by an object of the étale site. -/
theorem pointFibre_nonempty_of_complement
    (x : (localizedFieldPointFunctor L).obj X) (hx : EtaleSite.PointAxioms L x)
    (U V : EtaleSite X)
    (hU : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map U.hom))
    (hV : Set.range (localizedSpaceFunctor.map V.hom) = {pointProjection L X x}ᶜ) :
    Nonempty ((EtaleSite.pointFibre L x).obj U) := by
  let fU : U ⟶ etaleSelf X := MorphismProperty.Over.homMk U.hom (Category.comp_id _)
  let fV : V ⟶ etaleSelf X := MorphismProperty.Over.homMk V.hom (Category.comp_id _)
  let S : Sieve (etaleSelf X) :=
    { arrows := fun W f => (∃ g : W ⟶ U, g ≫ fU = f) ∨
        (∃ g : W ⟶ V, g ≫ fV = f)
      downward_closed := by
        intro W W' f hf g
        rcases hf with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact Or.inl ⟨g ≫ a, Category.assoc _ _ _⟩
        · exact Or.inr ⟨g ≫ a, Category.assoc _ _ _⟩ }
  have hS : S ∈ etaleTopology X (etaleSelf X) := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    by_cases hy : y = pointProjection L X x
    · refine ⟨U, fU, Or.inl ⟨𝟙 U, Category.id_comp _⟩, ?_⟩
      exact hy ▸ hU
    · refine ⟨V, fV, Or.inr ⟨𝟙 V, Category.id_comp _⟩, ?_⟩
      change y ∈ Set.range (localizedSpaceFunctor.map V.hom)
      rw [hV]
      exact hy
  let p : (EtaleSite.pointFibre L x).obj (etaleSelf X) :=
    ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩
  obtain ⟨W, f, hf, q, hq⟩ := hx.2 S hS p
  rcases hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact ⟨(EtaleSite.pointFibre L x).map g q⟩
  · let r : {p : (localizedFieldPointFunctor L).obj V.left //
        (localizedFieldPointFunctor L).map V.hom p = x} :=
      (EtaleSite.pointFibre L x).map g q
    have hr : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map V.hom) := by
      refine ⟨pointProjection L V.left r.1, ?_⟩
      exact (pointProjection_map L V.hom r.1).symm.trans
        (congrArg (pointProjection L X) r.2)
    rw [hV] at hr
    exact False.elim (hr rfl)

/-- Étaleness of open-domain inclusions implies point lifting on a
Hausdorff analytic space, using only the given point axioms. -/
theorem etalePointLifting_of_openDomains [T2Space (localizedSpaceFunctor.obj X)]
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (hopen : EtaleOpenDomainStatement X) : EtalePointLifting L (X := X) := by
  intro x U hU
  let C : Set (localizedSpaceFunctor.obj X) := {pointProjection L X x}ᶜ
  have hC : IsOpen C := isClosed_singleton.isOpen_compl
  let D := (presentationOf X).openDomain C hC
  let V : EtaleSite X := MorphismProperty.Over.mk ⊤ (domainι X D) (hopen C hC)
  apply pointFibre_nonempty_of_complement L x (h x) U V hU
  change Set.range (localizedSpaceFunctor.map (domainι X D)) = C
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [domainι_apply]
    exact z.property
  · intro hy
    exact ⟨⟨y, hy⟩, domainι_apply D _⟩

end Langlands.Sheaf.Equivariant.Analytic
