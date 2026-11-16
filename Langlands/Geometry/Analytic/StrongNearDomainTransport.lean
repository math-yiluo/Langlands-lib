import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.SaturatedSourceRefinementEquality

/-! # Berkovich test relations and actual domain inclusions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

namespace TestTriple

/-- A chart of an actual domain is the retained ambient chart, with the same
function and bound. -/
def ambient {D : B.AnalyticDomain} (τ : TestTriple (B.domain D)) : TestTriple B where
  domain := τ.domain.val
  function := τ.function
  bound := τ.bound
  bound_pos := τ.bound_pos

theorem ambient_locus_subset {D : B.AnalyticDomain} (τ : TestTriple (B.domain D)) :
    τ.ambient.locus ⊆ D.carrier :=
  τ.domain.property

theorem locus_eq_preimage_ambient {D : B.AnalyticDomain}
    (τ : TestTriple (B.domain D)) :
    τ.locus = Subtype.val ⁻¹' τ.ambient.locus := by
  change Set.range (B.presentation.atlas.subspaceChart D.carrier τ.domain) = _
  exact B.presentation.atlas.range_subspaceChart D.carrier τ.domain

end TestTriple

section Codomain

variable {D : B.AnalyticDomain} (τ : TestTriple (B.domain D))
  (a b : A ⟶ B.domain D)

/-- Corestriction to a domain does not change whether a source chart maps
into a retained test chart. -/
theorem isTestPiece_comp_domainInclusion_iff (i : A.presentation.atlas.Index) :
    IsTestPiece τ.ambient (a ≫ B.domainInclusion D) (b ≫ B.domainInclusion D) i ↔
      IsTestPiece τ a b i := by
  rw [IsTestPiece, IsTestPiece, τ.locus_eq_preimage_ambient]
  constructor <;> rintro ⟨ha, hb⟩
  · constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact ha ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hb ⟨x, hx, rfl⟩
  · constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact ha ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hb ⟨x, hx, rfl⟩

/-- Complete bounded pullbacks along the inclusion recover those of the
corestricted map. -/
theorem comp_domainInclusion_pullback (i : A.presentation.atlas.Index)
    (h : a.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆ τ.locus)
    (h' : (a ≫ B.domainInclusion D).baseMap ''
      Set.range (A.presentation.atlas.chart i) ⊆ τ.ambient.locus) :
    (a ≫ B.domainInclusion D).pullback i τ.ambient.domain h' =
      a.pullback i τ.domain h := by
  exact originalDomainInclusion_comp_pullback D a i τ.domain h h'

/-- The test relation for maps into an actual domain is exactly the
ambient test relation after the full analytic inclusion. -/
theorem strongNear_comp_domainInclusion_iff :
    StrongNear τ.ambient (a ≫ B.domainInclusion D) (b ≫ B.domainInclusion D) ↔
      StrongNear τ a b := by
  have ha : (a ≫ B.domainInclusion D).baseMap ⁻¹' τ.ambient.locus =
      a.baseMap ⁻¹' τ.locus := by
    rw [τ.locus_eq_preimage_ambient]
    rfl
  have hb : (b ≫ B.domainInclusion D).baseMap ⁻¹' τ.ambient.locus =
      b.baseMap ⁻¹' τ.locus := by
    rw [τ.locus_eq_preimage_ambient]
    rfl
  constructor
  · rintro ⟨hpre, hcov, hbound⟩
    refine ⟨ha.symm.trans (hpre.trans hb), ?_, ?_⟩
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := hcov y (ha.symm ▸ hy)
      exact ⟨i, (isTestPiece_comp_domainInclusion_iff τ a b i).mp hi, hyi⟩
    · intro i hi p
      have hi' := (isTestPiece_comp_domainInclusion_iff τ a b i).mpr hi
      have hp := hbound i hi' p
      rw [comp_domainInclusion_pullback τ a i hi.1 hi'.1,
        comp_domainInclusion_pullback τ b i hi.2 hi'.2] at hp
      exact hp
  · rintro ⟨hpre, hcov, hbound⟩
    refine ⟨ha.trans (hpre.trans hb.symm), ?_, ?_⟩
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := hcov y (ha ▸ hy)
      exact ⟨i, (isTestPiece_comp_domainInclusion_iff τ a b i).mpr hi, hyi⟩
    · intro i hi p
      have hi' := (isTestPiece_comp_domainInclusion_iff τ a b i).mp hi
      rw [comp_domainInclusion_pullback τ a i hi'.1 hi.1,
        comp_domainInclusion_pullback τ b i hi'.2 hi.2]
      exact hbound i hi' p

end Codomain

section Source

variable (τ : TestTriple B) (a b : A ⟶ B)

/-- Restricting the source to a domain keeps the full bounded pullback at
each retained original source chart. -/
theorem domainInclusion_comp_pullback (E : A.AnalyticDomain)
    (i : (A.domain E).presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : a.baseMap '' Set.range (A.presentation.atlas.chart i.val) ⊆
      Set.range (B.presentation.atlas.chart j))
    (h' : (A.domainInclusion E ≫ a).baseMap ''
      Set.range ((A.domain E).presentation.atlas.chart i) ⊆
        Set.range (B.presentation.atlas.chart j)) :
    (A.domainInclusion E ≫ a).pullback i j h' = a.pullback i.val j h := by
  have hinc : (A.domainInclusion E).baseMap ''
      Set.range ((A.domain E).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  refine (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
    (A.domainInclusion E) a (A.domain E).hasAllLocalDomains
    A.hasAllLocalDomains i i.val j hinc h h').trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (a.pullback i.val j h) = _
  rw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

theorem isTestPiece_precomp_domainInclusion_iff (E : A.AnalyticDomain)
    (i : (A.domain E).presentation.atlas.Index) :
    IsTestPiece τ (A.domainInclusion E ≫ a) (A.domainInclusion E ≫ b) i ↔
      IsTestPiece τ a b i.val := by
  constructor <;> rintro ⟨ha, hb⟩
  · constructor
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ha ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hb ⟨_, ⟨x, rfl⟩, rfl⟩
  · constructor
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ha ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hb ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Restricting the source preserves the test relation if the whole
inverse image of the test locus lies in the chosen source domain. -/
theorem StrongNear.precomp_domainInclusion (hnear : StrongNear τ a b)
    (E : A.AnalyticDomain) (hE : a.baseMap ⁻¹' τ.locus ⊆ E.carrier) :
    StrongNear τ (A.domainInclusion E ≫ a) (A.domainInclusion E ≫ b) := by
  refine ⟨congrArg (Subtype.val ⁻¹' ·) hnear.1, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := hnear.2.1 y.val hy
    have hiE : Set.range (A.presentation.atlas.chart i) ⊆ E.carrier := by
      intro x hx
      exact hE (hi.1 ⟨x, hx, rfl⟩)
    let i' : (A.domain E).presentation.atlas.Index := ⟨i, hiE⟩
    refine ⟨i', (isTestPiece_precomp_domainInclusion_iff τ a b E i').mpr hi, ?_⟩
    obtain ⟨x, hx⟩ := hyi
    exact ⟨x, Subtype.ext hx⟩
  · intro i hi p
    have hi' := (isTestPiece_precomp_domainInclusion_iff τ a b E i).mp hi
    rw [domainInclusion_comp_pullback a E i τ.domain hi'.1 hi.1,
      domainInclusion_comp_pullback b E i τ.domain hi'.2 hi.2]
    exact hnear.2.2 i.val hi' p

/-- A same-space source refinement keeps the original bounded pullback. -/
theorem refiningSubatlasInclusion_comp_pullback
    (P : A.presentation.atlas.RefiningSelection)
    (i : (A.refiningSubpresentation P).presentation.atlas.Index)
    (j : B.presentation.atlas.Index)
    (h : a.baseMap '' Set.range (A.presentation.atlas.chart i.val) ⊆
      Set.range (B.presentation.atlas.chart j))
    (h' : (A.refiningSubatlasInclusion P ≫ a).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (B.presentation.atlas.chart j)) :
    (A.refiningSubatlasInclusion P ≫ a).pullback i j h' = a.pullback i.val j h := by
  have hinc : (A.refiningSubatlasInclusion P).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
    (A.refiningSubatlasInclusion P) a (A.refiningSubpresentation P).hasAllLocalDomains
    A.hasAllLocalDomains i i.val j hinc h h').trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (a.pullback i.val j h) = _
  rw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- Any downward-closed locally refining source subatlas preserves the
strong test relation. No original test piece has to be retained whole. -/
theorem StrongNear.precomp_refiningSubatlasInclusion (hnear : StrongNear τ a b)
    (P : A.presentation.atlas.RefiningSelection) :
    StrongNear τ (A.refiningSubatlasInclusion P ≫ a)
      (A.refiningSubatlasInclusion P ≫ b) := by
  refine ⟨hnear.1, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := hnear.2.1 y hy
    obtain ⟨σ, _, hs, hm, hn⟩ :=
      P.locally_refining _ (Set.mem_range_self i) y hyi
    obtain ⟨V, hV, hyV⟩ := mem_of_mem_nhdsWithin hyi hn
    obtain ⟨k, hk⟩ := hs hV
    change Set.range (A.presentation.atlas.chart k.val) = V at hk
    have hki : Set.range (A.presentation.atlas.chart k.val) ⊆
        Set.range (A.presentation.atlas.chart i) := by
      rw [hk]
      exact (hm V hV).1
    refine ⟨k, ⟨(Set.image_mono hki).trans hi.1,
      (Set.image_mono hki).trans hi.2⟩, ?_⟩
    change y ∈ Set.range (A.presentation.atlas.chart k.val)
    exact hk.symm ▸ hyV
  · intro i hi p
    change IsTestPiece τ a b i.val at hi
    rw [refiningSubatlasInclusion_comp_pullback a P i τ.domain hi.1 hi.1,
      refiningSubatlasInclusion_comp_pullback b P i τ.domain hi.2 hi.2]
    exact hnear.2.2 i.val hi p

end Source

end Langlands.Analytic.SaturatedAtlasPresentation
