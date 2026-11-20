import Langlands.AlgebraicGeometry.AffineSectionNeighbourhood
import Langlands.AlgebraicGeometry.LocallyClosedLocusFromOpenCharts
import Langlands.GroupScheme.IdentityJetSmoothUnitAffineChart
import Langlands.RingTheory.Smooth.SectionJetConormalChart

/-! # The fixed-rank smoothness locus along a group unit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

open Algebra.SectionJet Langlands.AlgebraicGeometry

private theorem hasClosedOpenChart_of_openImmersion {S U Z : Scheme.{u}}
    (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop) (a : U ⟶ S) [IsOpenImmersion a]
    (j : Z ⟶ U) [IsClosedImmersion j]
    (h : ∀ (T : Scheme.{u}) (g : T ⟶ U), (∃ k : T ⟶ Z, k ≫ j = g) ↔ P (g ≫ a)) :
    HasClosedOpenChart P a.opensRange := by
  let e := a.isoOpensRange
  have he : e.hom ≫ a.opensRange.ι = a := Scheme.Hom.isoOpensRange_hom_ι a
  have he' : e.inv ≫ a = a.opensRange.ι := calc
    e.inv ≫ a = e.inv ≫ e.hom ≫ a.opensRange.ι := congrArg (e.inv ≫ ·) he.symm
    _ = _ := e.inv_hom_id_assoc _
  refine ⟨Z, j ≫ e.hom, inferInstance, fun T g => ?_⟩
  rw [← he', ← Category.assoc, ← h T]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have heq := congrArg (fun m : T ⟶ a.opensRange.toScheme => m ≫ e.inv) hk
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using heq
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← Category.assoc, hk, Category.assoc, e.inv_hom_id, Category.comp_id]⟩

private theorem range_smoothUnitBasicMap {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f : T ⟶ S) (t : T) (a : Γ(S, ⊤))
    (ha : f.appTop.hom a ∉ (T.isoSpec.hom t).asIdeal) :
    f t ∈ Set.range (smoothUnitBasicMap a) := by
  let R := Γ(S, ⊤)
  let X := Spec (CommRingCat.of (Localization.Away a))
  let p : X ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))
  have hp : S.isoSpec.hom (f t) = (T.isoSpec.hom t).comap f.appTop.hom :=
    (congrArg (fun g : T ⟶ Spec R => g t) (Scheme.isoSpec_hom_naturality f)).symm
  have hq : S.isoSpec.hom (f t) ∈ p.opensRange := by
    rw [show p.opensRange = PrimeSpectrum.basicOpen a from Scheme.Hom.opensRange_localizationAway a,
      hp, PrimeSpectrum.mem_basicOpen]
    exact ha
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, ?_⟩
  change (p ≫ S.isoSpec.inv) x = f t
  rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

private theorem exists_closed_chart_at_test_point {S T : Scheme.{u}} [IsLocallyNoetherian S]
    (G : GroupScheme S) [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (r : ℕ) (g : T ⟶ S) (hg : SmoothUnitRankTest G r g) (t : T) :
    ∃ U : S.Opens, g t ∈ U ∧ HasClosedOpenChart (fun {_} g' => SmoothUnitRankTest G r g') U := by
  let N := affineSectionNeighbourhood G.X.hom G.identitySection G.identitySection_comp (g t)
  let K := (GroupScheme.baseChange N.baseι).obj G
  let v : N.total ⟶ K.X.left := pullback.lift N.totalι N.hom N.comm
  have : IsLocallyNoetherian N.base := isLocallyNoetherian_of_isOpenImmersion N.baseι
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom N.baseι))
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom N.baseι))
  have : IsOpenImmersion v := by
    have : IsOpenImmersion (pullback.fst G.X.hom N.baseι) := inferInstance
    have : IsOpenImmersion (v ≫ pullback.fst G.X.hom N.baseι) := by
      dsimp [v]
      rw [pullback.lift_fst]
      infer_instance
    exact IsOpenImmersion.of_comp v (pullback.fst G.X.hom N.baseι)
  have he : N.sectionMap ≫ v = K.identitySection := by
    apply pullback.hom_ext
    · rw [Category.assoc, show v ≫ pullback.fst G.X.hom N.baseι = N.totalι from pullback.lift_fst _ _ _,
        N.section_comp, identitySection_baseChange_fst]
    · rw [Category.assoc, show v ≫ pullback.snd G.X.hom N.baseι = N.hom from pullback.lift_snd _ _ _]
      exact N.section_hom.trans K.identitySection_comp.symm
  have ht : t ∈ g ⁻¹ᵁ N.baseι.opensRange := N.mem_base
  obtain ⟨U, hU, htU, hUV⟩ := exists_isAffineOpen_mem_and_subset ht
  have : IsAffine U.toScheme := hU
  let f : U.toScheme ⟶ N.base := IsOpenImmersion.lift N.baseι (U.ι ≫ g) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hUV x.property)
  have hf : f ≫ N.baseι = U.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hK : SmoothUnitRankTest K r f := by
    apply (smoothUnitRankTest_comp_iff G r N.baseι f).mpr
    rw [hf]
    exact SmoothUnitRankTest.comp G hg U.ι
  let t' : U.toScheme := ⟨t, htU⟩
  let R := Γ(N.base, ⊤)
  let A := Γ(N.total, ⊤)
  let B := Γ(U.toScheme, ⊤)
  let : Algebra R A := neighborhoodAlgebra K v
  let : Algebra R B := f.appTop.hom.toAlgebra
  let ε := neighborhoodAugmentation K v N.sectionMap he
  have : LocallyOfFinitePresentation (v ≫ K.X.hom) := inferInstance
  have : Algebra.FinitePresentation R A := HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation)
    (v ≫ K.X.hom) inferInstance
  have hs := (smoothAlongUnitOfRank_baseChange_iff_affine K v N.sectionMap he f r).mp hK
  let q := U.toScheme.isoSpec.hom t'
  obtain ⟨a, ha, z, hspan⟩ := sectionJetConormalChart R A B ε q r (hs.2 q)
  obtain ⟨Z, j, hj, hchart⟩ := exists_closed_smoothUnitBasicChart K v N.sectionMap he r a z hspan
  let b := smoothUnitBasicMap a
  let b' := b ≫ N.baseι
  have : IsOpenImmersion b := inferInstanceAs (IsOpenImmersion (Spec.map _ ≫ N.base.isoSpec.inv))
  have : IsOpenImmersion b' := inferInstanceAs (IsOpenImmersion (b ≫ N.baseι))
  refine ⟨b'.opensRange, ?_,
    hasClosedOpenChart_of_openImmersion (fun {_} g' => SmoothUnitRankTest G r g') b' j ?_⟩
  · obtain ⟨x, hx⟩ := range_smoothUnitBasicMap f t' a ha
    refine ⟨x, ?_⟩
    change (b ≫ N.baseι) x = g t
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hf]
    rfl
  · intro T' k
    exact (hchart T' k).trans ((smoothUnitRankTest_comp_iff G r N.baseι (k ≫ b)).trans (by
      rw [Category.assoc]))

/-- Over a locally noetherian base the fixed-rank smoothness condition along
the actual unit is represented by a closed subscheme of an open of the base. -/
def IdentityJetSmoothUnitLocusStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S) [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (r : ℕ),
    ∃ (U : S.Opens) (Z : Scheme.{u}) (j : Z ⟶ U.toScheme), IsClosedImmersion j ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ S),
        (∃! k : T ⟶ Z, k ≫ j ≫ U.ι = g) ↔ SmoothUnitRankTest G r g

theorem identityJetSmoothUnitLocus : IdentityJetSmoothUnitLocusStatement.{u} := by
  intro S _ G _ _ r
  obtain ⟨U, Z, j, hj, h⟩ := locallyClosedLocus_of_openCharts S
    (fun {_} g => SmoothUnitRankTest G r g)
    (fun {_ _} b _ hh => SmoothUnitRankTest.comp G hh b)
    (fun {_} g 𝒰 hh => smoothUnitRankTest_of_openCover G g 𝒰 hh)
    (fun {_} g hg t => exists_closed_chart_at_test_point G r g hg t)
  refine ⟨U, Z, j, hj, fun T g => ⟨fun hg => (h T g).mp hg.exists, ?_⟩⟩
  intro hg
  obtain ⟨k, hk⟩ := (h T g).mpr hg
  refine ⟨k, hk, fun k' hk' => ?_⟩
  exact (cancel_mono (j ≫ U.ι)).mp (hk'.trans hk.symm)

end Langlands.GroupScheme.IdentityJet
