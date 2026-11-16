import Langlands.Geometry.Analytic.StrongQuasiIsoDomainRestriction

/-! # Restricting near-identity fractions to actual analytic domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B S T : SaturatedAtlasPresentation.{u, v, w} K}

/-- One locally refining original-chart source selection on which both maps
corestrict to the same actual analytic domain. -/
def commonDomainSourceSelection (a b : A ⟶ B) (D : B.AnalyticDomain)
    (ha : ∀ x, a.baseMap x ∈ D.carrier) (hb : ∀ x, b.baseMap x ∈ D.carrier) :
    A.presentation.atlas.RefiningSelection :=
  domainSourceSelection a D ha ⊓ domainSourceSelection b D hb

/-- Two strong maps into an actual domain admit simultaneous corestriction
on one common original-chart source refinement, preserving the test relation. -/
theorem StrongNear.exists_domainFactors {D : B.AnalyticDomain}
    (τ : TestTriple (B.domain D)) {a b : A ⟶ B}
    (hnear : StrongNear τ.ambient a b)
    (ha : ∀ x, a.baseMap x ∈ D.carrier) (hb : ∀ x, b.baseMap x ∈ D.carrier) :
    ∃ (P : A.presentation.atlas.RefiningSelection)
      (a' b' : A.refiningSubpresentation P ⟶ B.domain D),
      a' ≫ B.domainInclusion D = A.refiningSubatlasInclusion P ≫ a ∧
      b' ≫ B.domainInclusion D = A.refiningSubatlasInclusion P ≫ b ∧
      StrongNear τ a' b' := by
  let P := commonDomainSourceSelection a b D ha hb
  let a' : A.refiningSubpresentation P ⟶ B.domain D :=
    A.refiningSubatlasMap (show P ≤ domainSourceSelection a D ha from inf_le_left) ≫
      domainFactor a D ha
  let b' : A.refiningSubpresentation P ⟶ B.domain D :=
    A.refiningSubatlasMap (show P ≤ domainSourceSelection b D hb from inf_le_right) ≫
      domainFactor b D hb
  have ha' : a' ≫ B.domainInclusion D = A.refiningSubatlasInclusion P ≫ a := by
    change (A.refiningSubatlasMap _ ≫ domainFactor a D ha) ≫ B.originalDomainInclusion D = _
    rw [Category.assoc, domainFactor_comp_inclusion, ← Category.assoc,
      refiningSubatlasMap_inclusion]
  have hb' : b' ≫ B.domainInclusion D = A.refiningSubatlasInclusion P ≫ b := by
    change (A.refiningSubatlasMap _ ≫ domainFactor b D hb) ≫ B.originalDomainInclusion D = _
    rw [Category.assoc, domainFactor_comp_inclusion, ← Category.assoc,
      refiningSubatlasMap_inclusion]
  refine ⟨P, a', b', ha', hb', ?_⟩
  apply (strongNear_comp_domainInclusion_iff τ a' b').mp
  rw [ha', hb']
  exact hnear.precomp_refiningSubatlasInclusion τ.ambient a b P

/-- A denominator equation also computes the numerator on every actual point. -/
theorem numerator_point_eq_of_fraction_equation (s : T ⟶ A) (a : T ⟶ B)
    (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (hφ : localizationFunctor.map s ≫ φ = localizationFunctor.map a)
    (x : T.presentation.space) :
    localizedSpaceFunctor.map φ (s.baseMap x) = a.baseMap x := by
  have hx := congrArg (fun f : localizationFunctor.obj T ⟶ localizationFunctor.obj B =>
    localizedSpaceFunctor.map f x) hφ
  rw [Functor.map_comp, localizedSpaceFunctor_map, localizedSpaceFunctor_map] at hx
  exact hx

/-- Full inclusion squares determine the fraction of a restricted analytic arrow. -/
theorem eq_domainFraction_of_squares
    (E : A.AnalyticDomain) (D : B.AnalyticDomain)
    (s : T ⟶ A) (a : T ⟶ B)
    (φ : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (hφ : localizationFunctor.map s ≫ φ = localizationFunctor.map a)
    (r : S ⟶ T) (t : S ⟶ A.domain E) (ht : t.IsQuasiIso)
    (c : S ⟶ B.domain D)
    (hts : t ≫ A.domainInclusion E = r ≫ s)
    (hca : c ≫ B.domainInclusion D = r ≫ a)
    (ψ : localizationFunctor.obj (A.domain E) ⟶ localizationFunctor.obj (B.domain D))
    (hψ : ψ ≫ B.localizedDomainInclusion D = A.localizedDomainInclusion E ≫ φ) :
    ψ = (localizedQuasiIso t ht).inv ≫ localizationFunctor.map c := by
  apply (cancel_epi (localizedQuasiIso t ht).hom).1
  change localizationFunctor.map t ≫ ψ = localizationFunctor.map t ≫
    ((localizedQuasiIso t ht).inv ≫ localizationFunctor.map c)
  rw [← Category.assoc, localizedQuasiIso_hom_inv_id, Category.id_comp]
  apply (cancel_mono (B.localizedDomainInclusion D)).1
  calc
    (localizationFunctor.map t ≫ ψ) ≫ B.localizedDomainInclusion D =
        localizationFunctor.map t ≫ (ψ ≫ B.localizedDomainInclusion D) :=
      Category.assoc _ _ _
    _ = localizationFunctor.map t ≫ (A.localizedDomainInclusion E ≫ φ) := by rw [hψ]
    _ = localizationFunctor.map (t ≫ A.domainInclusion E) ≫ φ := by
      rw [Functor.map_comp, Category.assoc]
      rfl
    _ = localizationFunctor.map (r ≫ s) ≫ φ := by rw [hts]
    _ = localizationFunctor.map r ≫ (localizationFunctor.map s ≫ φ) := by
      rw [Functor.map_comp, Category.assoc]
    _ = localizationFunctor.map (r ≫ a) := by rw [hφ, Functor.map_comp]
    _ = localizationFunctor.map c ≫ B.localizedDomainInclusion D := by
      rw [← hca, Functor.map_comp]
      rfl

/-- Restricting an analytic endomorphism preserving a domain preserves
Berkovich's near-identity relation for every test triple of that domain. -/
theorem IsNear.domainRestrict_id
    {X : LocalizedCategory.{u, v, w} (K := K)}
    (D : (presentationOf X).AnalyticDomain)
    (τ : TestTriple ((presentationOf X).domain D)) (φ : X ⟶ X)
    (hφD : ∀ x ∈ D.carrier, localizedSpaceFunctor.map φ x ∈ D.carrier)
    (hnear : IsNear τ.ambient φ (𝟙 X)) :
    IsNear τ (domainRestrict D D φ hφD) (𝟙 (domainObj X D)) := by
  obtain ⟨T, s, hs, a, b, hφ, hid, hab⟩ := hnear
  have hsa : localizationFunctor.map s ≫ φ = localizationFunctor.map a := by
    rw [hφ]
    exact localizationFunctor_map_s_comp_localizedRightFraction
      (MorphismProperty.RightFraction.mk s hs a)
  have hsb : localizationFunctor.map s ≫ (𝟙 X) = localizationFunctor.map b := by
    rw [hid]
    exact localizationFunctor_map_s_comp_localizedRightFraction
      (MorphismProperty.RightFraction.mk s hs b)
  have hpa := numerator_point_eq_of_fraction_equation s a φ hsa
  have hpb : ∀ x, s.baseMap x = b.baseMap x := by
    intro x
    have hx := numerator_point_eq_of_fraction_equation s b (𝟙 X) hsb x
    erw [localizedSpaceFunctor.map_id X] at hx
    exact hx
  let E := QuasiIsoDomainRestriction.preimageDomain s D
  let q := QuasiIsoDomainRestriction.map s hs D
  let e := T.domainInclusion E
  have haD : ∀ x, (e ≫ a).baseMap x ∈ D.carrier := by
    intro x
    change a.baseMap x.val ∈ D.carrier
    rw [← hpa x.val]
    exact hφD _ x.property
  have hbD : ∀ x, (e ≫ b).baseMap x ∈ D.carrier := by
    intro x
    change b.baseMap x.val ∈ D.carrier
    rw [← hpb x.val]
    exact x.property
  have hE : a.baseMap ⁻¹' τ.ambient.locus ⊆ E.carrier := by
    intro x hx
    have hbx : b.baseMap x ∈ τ.ambient.locus := by
      change x ∈ b.baseMap ⁻¹' τ.ambient.locus
      rw [← hab.1]
      exact hx
    change s.baseMap x ∈ D.carrier
    rw [hpb x]
    exact τ.ambient_locus_subset hbx
  have habE := hab.precomp_domainInclusion τ.ambient a b E hE
  obtain ⟨P, a', b', ha', hb', hab'⟩ := habE.exists_domainFactors τ haD hbD
  let p := (T.domain E).refiningSubatlasInclusion P
  let t := p ≫ q
  have ht : t.IsQuasiIso :=
    (quasiIsomorphisms (K := K)).comp_mem _ _
      (isQuasiIso_refiningSubatlasInclusion P) (QuasiIsoDomainRestriction.isQuasiIso s hs D)
  have hts : t ≫ (presentationOf X).domainInclusion D = (p ≫ e) ≫ s := by
    change (p ≫ q) ≫ (presentationOf X).domainInclusion D = (p ≫ e) ≫ s
    have hq := QuasiIsoDomainRestriction.map_comp_domainInclusion s hs D
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => p ≫ f) hq).trans (Category.assoc _ _ _).symm)
  have ha'sq : a' ≫ (presentationOf X).domainInclusion D = (p ≫ e) ≫ a :=
    ha'.trans (Category.assoc _ _ _).symm
  have hb'sq : b' ≫ (presentationOf X).domainInclusion D = (p ≫ e) ≫ b :=
    hb'.trans (Category.assoc _ _ _).symm
  refine ⟨(T.domain E).refiningSubpresentation P, t, ht, a', b', ?_, ?_, hab'⟩
  · exact eq_domainFraction_of_squares D D s a φ hsa (p ≫ e) t ht a'
      hts ha'sq (domainRestrict D D φ hφD) (domainRestrict_comp D D φ hφD)
  · exact eq_domainFraction_of_squares D D s b (𝟙 X) hsb (p ≫ e) t ht b'
      hts hb'sq (𝟙 (domainObj X D))
      ((Category.id_comp _).trans (Category.comp_id _).symm)

end Langlands.Analytic.SaturatedAtlasPresentation
