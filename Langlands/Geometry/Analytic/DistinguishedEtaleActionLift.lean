import Langlands.Geometry.Analytic.ContinuousDomainEmbeddings
import Langlands.Geometry.Analytic.LocalActionLifts
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods

/-! # Restricting a compact quasi-étale lift to a distinguished étale object -/

noncomputable section

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory
open scoped Pointwise

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X U V : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}

variable [IsTopologicalGroup G] in
/-- A compact analytic domain is preserved by an open subgroup of a
continuous action. Finitely many ambient charts contained in the domain
cover it, and each has an open stabilizer. -/
theorem exists_openSubgroup_preserving_compact_domain (hρ : IsContinuousAction ρ)
    (D : (presentationOf X).AnalyticDomain) (hD : IsCompact D.carrier) :
    ∃ H : OpenSubgroup G, ∀ g ∈ H, ∀ x ∈ D.carrier,
      localizedSpaceFunctor.map (ρ g).asIso.hom x ∈ D.carrier := by
  classical
  let a := (presentationOf X).presentation.atlas
  obtain ⟨A, hA, hchart, hsub, hcov⟩ :=
    AtlasTopology.exists_finite_cover_of_restrictedFamily D.is_domain hD Set.Subset.rfl
  let I : Set a.Index := (fun i => Set.range (a.chart i)) ⁻¹' A
  have hI : I.Finite := hA.preimage a.chartDomain_injective.injOn
  let := hI.fintype
  let H := OpenSubgroup.iInfOfFinite (fun i : I => chartOpenStabilizer ρ hρ i.1)
  refine ⟨H, fun g hg x hx => ?_⟩
  obtain ⟨E, hE, hxE⟩ := hcov hx
  obtain ⟨i, rfl⟩ := hchart hE
  have hgi : g ∈ chartOpenStabilizer ρ hρ i :=
    (OpenSubgroup.iInfOfFinite_le (fun i : I => chartOpenStabilizer ρ hρ i.1) ⟨i, hE⟩) hg
  let : MulAction G (localizedSpaceFunctor.obj X) := localizedSpaceAction ρ
  change localizedSpaceFunctor.obj X at x
  have hS : g • (Set.range (a.chart i) : Set (localizedSpaceFunctor.obj X)) =
      Set.range (a.chart i) := hgi
  have hmem : g • x ∈ (Set.range (a.chart i) : Set (localizedSpaceFunctor.obj X)) :=
    Eq.mp (congrArg (fun T : Set (localizedSpaceFunctor.obj X) => g • x ∈ T) hS)
      (Set.smul_mem_smul_set hxE)
  exact hsub _ hE hmem

namespace ActionLift

variable {f : U ⟶ X}

/-- Restrict a lift to an invariant analytic domain of its source. -/
def restrictDomain (l : ActionLift ρ f) (D : (presentationOf U).AnalyticDomain)
    (hD : IsInvariantDomain (analyticActionOfAut l.action) D) :
    ActionLift ρ (domainι U D ≫ f) where
  subgroup := l.subgroup
  isOpen_subgroup := l.isOpen_subgroup
  action := (invariantDomainAction (analyticActionOfAut l.action) D hD).ρAut
  isContinuousAction := by
    have hc : IsContinuousAction (analyticActionOfAut l.action).ρAut := by
      rw [analyticActionOfAut_ρAut]
      exact l.isContinuousAction
    exact hc.invariantDomainAction D hD
  equivariant g := by
    have hg := (invariantDomainInclusion (analyticActionOfAut l.action) D hD).comm g
    change ((invariantDomainAction (analyticActionOfAut l.action) D hD).ρAut g).asIso.hom ≫
      domainι U D = domainι U D ≫ (l.action g).asIso.hom at hg
    have hrhs : (domainι U D ≫ (l.action g).asIso.hom) ≫ f =
        (domainι U D ≫ f) ≫ (ρ g).asIso.hom := by
      rw [Category.assoc, l.equivariant, Category.assoc]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun p : domainObj U D ⟶ U => p ≫ f) hg).trans hrhs)

/-- Transport a lift along an isomorphism of its source. -/
def precompIso (l : ActionLift ρ f) (e : V ≅ U) : ActionLift ρ (e.hom ≫ f) where
  subgroup := l.subgroup
  isOpen_subgroup := l.isOpen_subgroup
  action := e.symm.conjAut.toMonoidHom.comp l.action
  isContinuousAction := l.isContinuousAction.conjAut e.symm
  equivariant g := by
    change (e.symm.conjAut (l.action g)).asIso.hom ≫ e.hom ≫ f = _
    rw [Iso.conjAut_apply]
    change (e.hom ≫ (l.action g).asIso.hom ≫ e.inv) ≫ e.hom ≫ f =
      (e.hom ≫ f) ≫ (ρ g).asIso.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc, l.equivariant]

end ActionLift

variable [IsTopologicalGroup G] in
/-- Existence of lifts on compact quasi-étale sources suffices for existence
of lifts on distinguished étale sources. Preserve the compact analytic
complement of the open domain, then restrict the lift to the open domain. -/
theorem nonempty_actionLift_of_isDistinguishedEtale
    (hLift : ∀ (U : LocalizedCategory.{u, v, v} (K := K)) (f : U ⟶ X),
      quasiEtale f → IsCompactSpace U → Nonempty (ActionLift ρ f))
    {f : V ⟶ X} (hf : IsDistinguishedEtale f) : Nonempty (ActionLift ρ f) := by
  obtain ⟨-, U, φ, hφ, hU, O, D, hO, hD, e, rfl⟩ := hf
  obtain ⟨l⟩ := hLift U φ hφ hU
  let : CompactSpace (presentationOf U).presentation.space := hU.1
  have hDc : IsCompact D.carrier := by
    rw [hD]
    exact hO.isClosed_compl.isCompact
  obtain ⟨H, hH⟩ := exists_openSubgroup_preserving_compact_domain l.isContinuousAction D hDc
  let H' : Subgroup G := H.toSubgroup.map l.subgroup.subtype
  have hH' : H' ≤ l.subgroup := by
    rintro _ ⟨g, -, rfl⟩
    exact g.property
  have hHopen : IsOpen (H' : Set G) :=
    l.isOpen_subgroup.isOpenMap_subtype_val _ H.isOpen
  let l' := l.restrict H' hHopen hH'
  let : MulAction l'.subgroup (localizedSpaceFunctor.obj U) := localizedSpaceAction l'.action
  have hD' (g : l'.subgroup) (x : localizedSpaceFunctor.obj U) (hx : x ∈ D.carrier) :
      g • x ∈ D.carrier := by
    obtain ⟨k, hk, he⟩ := g.property
    have he' : Subgroup.inclusion hH' g = k := Subtype.ext he.symm
    change localizedSpaceFunctor.map (l.action (Subgroup.inclusion hH' g)).asIso.hom x ∈ D.carrier
    rw [he']
    exact hH k hk x hx
  have hO' : IsInvariantDomain (analyticActionOfAut l'.action) O := by
    intro g x hx
    change localizedSpaceFunctor.obj U at x
    change g • x ∈ O.carrier
    by_contra h
    have hy : g • x ∈ D.carrier := hD ▸ h
    have hBack := hD' g⁻¹ (g • x) hy
    rw [inv_smul_smul, hD] at hBack
    exact hBack hx
  exact ⟨(l'.restrictDomain O hO').precompIso e⟩

end Langlands.Analytic.SaturatedAtlasPresentation
