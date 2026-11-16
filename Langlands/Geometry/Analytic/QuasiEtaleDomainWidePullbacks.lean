import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-! # Finite wide pullbacks of actual quasi-étale domain charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Membership in a finite meet of actual domains is membership in every factor. -/
theorem mem_finsetInf_domain
    {U : LocalizedCategory.{u, v, v} (K := K)} {I : Type*}
    (D : I → (presentationOf U).AnalyticDomain) (s : Finset I)
    (x : localizedSpaceFunctor.obj U) :
    x ∈ (s.inf D).carrier ↔ ∀ i ∈ s, x ∈ (D i).carrier := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro _ i hi
      exact (Finset.notMem_empty i hi).elim
    · intro _
      exact Set.mem_univ x
  | @insert i s _ ih =>
    rw [Finset.inf_insert]
    change (x ∈ (D i).carrier ∧ x ∈ (s.inf D).carrier) ↔ _
    rw [ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

namespace FiniteCompactDomainChartCover

variable {X : LocalizedCategory.{u, v, v} (K := K)}
  {U : QuasiEtaleSite X} (C : FiniteCompactDomainChartCover U)

@[reassoc (attr := simp)]
theorem domainIso_inv_arrow (i : C.Index) :
    (C.domainIso i).inv ≫ (C.arrow i).left = domainι U.left (C.domain i) := by
  rw [← C.domainIso_hom_inclusion, Iso.inv_hom_id_assoc]

theorem arrow_left_mono (i : C.Index) : Mono (C.arrow i).left := by
  rw [← C.domainIso_hom_inclusion]
  infer_instance

instance arrow_mono (i : C.Index) : Mono (C.arrow i) where
  right_cancellation f g h := by
    let : Mono (C.arrow i).left := C.arrow_left_mono i
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono (C.arrow i).left).1 (congrArg (fun k => k.left) h)

theorem arrow_image_mem (i : C.Index)
    (y : localizedSpaceFunctor.obj (C.obj i).left) :
    localizedSpaceFunctor.map (C.arrow i).left y ∈ (C.domain i).carrier := by
  rw [← C.domainIso_hom_inclusion, Functor.map_comp, TopCat.comp_app, domainι_apply]
  exact (localizedSpaceFunctor.map (C.domainIso i).hom y).property

variable {J : Type w} [Fintype J] (a : J → C.Index) (j₀ : J)

/-- The anchor ensures compactness and a retained étale envelope; the tail
contains every member of the finite tuple, with repetitions allowed. -/
def wideDomain : (presentationOf U.left).AnalyticDomain := by
  classical
  exact C.intersectionDomain (a j₀) (Finset.univ.image a)

theorem wideDomain_le (j : J) : C.wideDomain a j₀ ≤ C.domain (a j) := by
  classical
  exact inf_le_right.trans (Finset.inf_le (Finset.mem_image.mpr
    ⟨j, Finset.mem_univ j, rfl⟩))

theorem mem_wideDomain (x : localizedSpaceFunctor.obj U.left) :
    x ∈ (C.wideDomain a j₀).carrier ↔ ∀ j, x ∈ (C.domain (a j)).carrier := by
  classical
  change (x ∈ (C.domain (a j₀)).carrier ∧
    x ∈ ((Finset.univ.image a).inf C.domain).carrier) ↔ _
  rw [mem_finsetInf_domain]
  constructor
  · intro h j
    exact h.2 _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  · intro h
    refine ⟨h j₀, ?_⟩
    rintro _ hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact h j

theorem wideDomain_factorization :
    HasDomainEtaleFactorization (domainι U.left (C.wideDomain a j₀) ≫ U.hom) := by
  classical
  exact C.intersectionDomain_factorization (a j₀) (Finset.univ.image a)

/-- The actual quasi-étale object representing the finite domain intersection. -/
def wideObj : QuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (domainι U.left (C.wideDomain a j₀) ≫ U.hom)
    (C.wideDomain_factorization a j₀).quasiEtale

theorem isCompactSpace_wideObj [T2Space (localizedSpaceFunctor.obj U.left)] :
    IsCompactSpace (C.wideObj a j₀).left := by
  classical
  exact C.isCompactSpace_intersectionObj (a j₀) (Finset.univ.image a)

/-- The actual arrow from the intersection to the ambient site object. -/
def wideBase : C.wideObj a j₀ ⟶ U :=
  MorphismProperty.Over.homMk (domainι U.left (C.wideDomain a j₀)) rfl

/-- Each projection returns to the selected chart source through its stored
actual domain isomorphism. -/
def wideProjection (j : J) : C.wideObj a j₀ ⟶ C.obj (a j) :=
  MorphismProperty.Over.homMk
    (domainOrderMap (C.wideDomain_le a j₀ j) ≫ (C.domainIso (a j)).inv) (by
      change (domainOrderMap (C.wideDomain_le a j₀ j) ≫
        (C.domainIso (a j)).inv) ≫ (C.obj (a j)).hom =
          domainι U.left (C.wideDomain a j₀) ≫ U.hom
      rw [← MorphismProperty.Over.w (C.arrow (a j))]
      simp only [Category.assoc, C.domainIso_inv_arrow_assoc,
        domainOrderMap_comp_inclusion_assoc])

@[reassoc (attr := simp)]
theorem wideProjection_comp_arrow (j : J) :
    C.wideProjection a j₀ j ≫ C.arrow (a j) = C.wideBase a j₀ := by
  apply MorphismProperty.Over.Hom.ext
  change (domainOrderMap (C.wideDomain_le a j₀ j) ≫
    (C.domainIso (a j)).inv) ≫ (C.arrow (a j)).left =
      domainι U.left (C.wideDomain a j₀)
  rw [Category.assoc, C.domainIso_inv_arrow, domainOrderMap_comp_inclusion]

/-- The finite intersection is a cone over the actual domain-chart arrows. -/
def wideCone : WidePullbackCone (fun j => C.arrow (a j)) :=
  WidePullbackCone.mk (C.wideBase a j₀) (C.wideProjection a j₀)
    (C.wideProjection_comp_arrow a j₀)

/-- A cone's common ambient arrow has image in every selected domain. -/
theorem wideCone_image_mem (t : WidePullbackCone (fun j => C.arrow (a j)))
    (z : localizedSpaceFunctor.obj t.pt.left) :
    localizedSpaceFunctor.map t.base.left z ∈ (C.wideDomain a j₀).carrier := by
  apply (C.mem_wideDomain a j₀ _).2
  intro j
  have hz := congrArg (fun k => localizedSpaceFunctor.map k.left z) (t.condition j)
  change localizedSpaceFunctor.map ((t.π j).left ≫ (C.arrow (a j)).left) z =
    localizedSpaceFunctor.map t.base.left z at hz
  rw [← hz, Functor.map_comp, TopCat.comp_app]
  exact C.arrow_image_mem (a j) _

/-- The universal arrow is the unique analytic factorization of the common
ambient arrow through the actual intersection domain. -/
def wideLift (t : WidePullbackCone (fun j => C.arrow (a j))) :
    t.pt ⟶ C.wideObj a j₀ :=
  MorphismProperty.Over.homMk
    (domainLift (C.wideDomain a j₀) t.base.left (C.wideCone_image_mem a j₀ t)) (by
      change domainLift _ _ _ ≫ (domainι _ _ ≫ U.hom) = t.pt.hom
      rw [← Category.assoc, domainLift_comp]
      exact MorphismProperty.Over.w t.base)

@[reassoc (attr := simp)]
theorem wideLift_base (t : WidePullbackCone (fun j => C.arrow (a j))) :
    C.wideLift a j₀ t ≫ C.wideBase a j₀ = t.base := by
  apply MorphismProperty.Over.Hom.ext
  exact domainLift_comp (C.wideDomain a j₀) t.base.left (C.wideCone_image_mem a j₀ t)

@[reassoc (attr := simp)]
theorem wideLift_projection (t : WidePullbackCone (fun j => C.arrow (a j))) (j : J) :
    C.wideLift a j₀ t ≫ C.wideProjection a j₀ j = t.π j := by
  apply (cancel_mono (C.arrow (a j))).1
  rw [Category.assoc, C.wideProjection_comp_arrow, C.wideLift_base]
  exact (t.condition j).symm

/-- The wide pullback universal property holds against every quasi-étale site
object, without a compactness or chart hypothesis on the test object. -/
def wideIsLimit : IsLimit (C.wideCone a j₀) :=
  WidePullbackCone.IsLimit.mk (C.wideCone a j₀) (C.wideLift a j₀)
    (C.wideLift_base a j₀) (C.wideLift_projection a j₀)
    (fun t m hm _ => by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (domainι U.left (C.wideDomain a j₀))).1
      exact (congrArg (fun k => k.left) hm).trans
        (congrArg (fun k => k.left) (C.wideLift_base a j₀ t)).symm)

end FiniteCompactDomainChartCover

end Langlands.Analytic.SaturatedAtlasPresentation
