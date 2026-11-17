import Langlands.Geometry.Analytic.EtalePointFaithfulness.FibreIsolation
import Langlands.Geometry.Analytic.EtaleOpenDomains.Statement
import Langlands.Sheaf.Equivariant.AnalyticCompactSupport
import Langlands.Sheaf.Equivariant.AnalyticEtaleSupport

/-! # Lifting analytic field points over prescribed underlying points -/

noncomputable section

universe u v uL

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [NormedAlgebra K L]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- The point axioms lift a field point into an étale neighborhood when its
underlying point lies in the image and open domains of the base are étale. -/
theorem pointFibre_nonempty_of_openDomains [T2Space (localizedSpaceFunctor.obj X)]
    (x : (localizedFieldPointFunctor L).obj X) (hx : EtaleSite.PointAxioms L x)
    (hopen : EtaleOpenDomainStatement X) (U : EtaleSite X)
    (hU : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map U.hom)) :
    Nonempty ((EtaleSite.pointFibre L x).obj U) := by
  let C : Set (localizedSpaceFunctor.obj X) := {pointProjection L X x}ᶜ
  have hC : IsOpen C := isClosed_singleton.isOpen_compl
  let D := (presentationOf X).openDomain C hC
  let V : EtaleSite X := MorphismProperty.Over.mk ⊤ (domainι X D) (hopen C hC)
  apply pointFibre_nonempty_of_complement L x hx U V hU
  change Set.range (localizedSpaceFunctor.map (domainι X D)) = C
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [domainι_apply]
    exact z.property
  · intro hy
    exact ⟨⟨y, hy⟩, domainι_apply D _⟩

/-- Open-source restriction and fibre isolation lift a base field point over
any prescribed point of its underlying étale fibre. -/
theorem exists_pointFibre_with_projection [T2Space (localizedSpaceFunctor.obj X)]
    (hopen : EtaleOpenDomainStatement X)
    (hrestrict : ∀ (U : EtaleSite X) (V : Set (localizedSpaceFunctor.obj U.left))
      (hV : IsOpen V),
      etale (domainι U.left ((presentationOf U.left).openDomain V hV) ≫ U.hom))
    (x : (localizedFieldPointFunctor L).obj X) (hx : EtaleSite.PointAxioms L x)
    (U : EtaleSite X) (y : localizedSpaceFunctor.obj U.left)
    (hxy : localizedSpaceFunctor.map U.hom y = pointProjection L X x) :
    ∃ q : (EtaleSite.pointFibre L x).obj U, pointProjection L U.left q.1 = y := by
  obtain ⟨V, hV, hy, hiso⟩ := etale_exists_open_fibreIsolation U.hom U.prop y
  let D := (presentationOf U.left).openDomain V hV
  let W : EtaleSite X :=
    MorphismProperty.Over.mk ⊤ (domainι U.left D ≫ U.hom) (hrestrict U V hV)
  have hW : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map W.hom) := by
    let yd : localizedSpaceFunctor.obj (domainObj U.left D) := ⟨y, hy⟩
    refine ⟨yd, ?_⟩
    have hι : localizedSpaceFunctor.map (domainι U.left D) yd = y := domainι_apply D yd
    exact (ConcreteCategory.congr_hom
      (localizedSpaceFunctor.map_comp (domainι U.left D) U.hom) yd).trans
        ((congrArg (localizedSpaceFunctor.map U.hom) hι).trans hxy)
  obtain ⟨q⟩ := pointFibre_nonempty_of_openDomains L x hx hopen W hW
  let i : W ⟶ U := MorphismProperty.Over.homMk (domainι U.left D) rfl
  let r : (EtaleSite.pointFibre L x).obj U := (EtaleSite.pointFibre L x).map i q
  refine ⟨r, hiso _ ?_ ?_⟩
  · let qp : (localizedFieldPointFunctor L).obj (domainObj U.left D) := q.1
    have hp : pointProjection L U.left r.1 =
        (pointProjection L (domainObj U.left D) qp).val :=
      (pointProjection_map L (domainι U.left D) qp).trans (domainι_apply D _)
    exact hp.symm ▸ (pointProjection L (domainObj U.left D) qp).property
  · exact ((pointProjection_map L U.hom r.1).symm.trans
      (congrArg (pointProjection L X) r.2)).trans hxy.symm

/-- Under open-domain étaleness and open-source restriction, surjectivity of
the field-point projection on the base implies it on every étale object. -/
theorem pointProjection_surjective_on_etale_of_openSourceRestriction
    [T2Space (localizedSpaceFunctor.obj X)]
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (hX : Function.Surjective (pointProjection L X))
    (hopen : EtaleOpenDomainStatement X)
    (hrestrict : ∀ (U : EtaleSite X) (V : Set (localizedSpaceFunctor.obj U.left))
      (hV : IsOpen V),
      etale (domainι U.left ((presentationOf U.left).openDomain V hV) ≫ U.hom)) :
    ∀ U : EtaleSite X, Function.Surjective (pointProjection L U.left) := by
  intro U y
  obtain ⟨x, hx⟩ := hX (localizedSpaceFunctor.map U.hom y)
  obtain ⟨q, hq⟩ := exists_pointFibre_with_projection L hopen hrestrict x (h x) U y hx.symm
  exact ⟨q.1, hq⟩

end Langlands.Sheaf.Equivariant.Analytic
