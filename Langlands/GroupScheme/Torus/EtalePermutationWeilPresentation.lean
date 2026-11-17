import Langlands.GroupScheme.Torus.EtalePermutationWeilCompatibility
import Langlands.GroupScheme.Torus.MatchingPermutationCharts

/-! # Actual Weil presentation of a group with an étale permutation atlas -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open EtalePermutationAtlas FiniteAffinePermutationCoefficients

/-- The actual global comparison with the invariant-coefficient Weil group
for a finite affine étale permutation atlas. -/
def finiteAffineWeilIso
    {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) [Finite 𝒰.I₀]
    [∀ a, IsAffine (𝒰.X a)] [∀ a, Flat (𝒰.f a)] [Surjective (Sigma.desc 𝒰.f)]
    (I : 𝒰.I₀ → Type u) [∀ a, Finite (I a)]
    (e : ∀ a, (baseChange (𝒰.f a)).obj D ≅ splitTorus (𝒰.X a) (I a))
    (H : ∀ a b, LocallyPermutes (𝒰.f a) (𝒰.f b) (e a) (e b)) :
    D ≅ weilGroup 𝒰.X 𝒰.f I e H := by
  apply matchingChartsIso 𝒰 I e (coordinateWeilChart 𝒰.X 𝒰.f I e H)
  intro a b z
  obtain ⟨O, hz, σ, Hσ⟩ := H a b z
  exact ⟨O, hz, σ, Hσ, weil_agreeBy_of_original 𝒰.X 𝒰.f I e H a b O σ Hσ⟩

/-- Every group with an étale permutation atlas over an affine scheme is the
actual pulled-back Weil group of a finite projective étale section algebra. -/
theorem HasEtalePermutationAtlas.exists_weilGroup
    {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S} (hD : HasEtalePermutationAtlas D) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra Γ(S, ⊤) E)
      (_ : Module.Finite Γ(S, ⊤) E) (_ : Module.Projective Γ(S, ⊤) E),
      Algebra.Etale Γ(S, ⊤) E ∧
        Nonempty (D ≅ (baseChange S.isoSpec.hom).obj (WeilGm.groupScheme Γ(S, ⊤) E)) := by
  obtain ⟨𝒰, hfin, I, hI, e, H⟩ := hD.exists_finiteAffine
  letI : Finite 𝒰.I₀ := hfin
  letI : Finite 𝒰.cover.I₀ := hfin
  letI : ∀ a, Finite (I a) := hI
  haveI (a : 𝒰.I₀) : Etale (𝒰.f a) := 𝒰.map_prop a
  haveI (a : 𝒰.I₀) : Flat (𝒰.f a) := inferInstance
  haveI : Surjective (Sigma.desc 𝒰.cover.f) := ⟨fun x => by
    obtain ⟨a, y, rfl⟩ := 𝒰.cover.exists_eq x
    exact ⟨Sigma.ι 𝒰.cover.X a y, by simp [← Scheme.Hom.comp_apply]⟩⟩
  let E := (coaction 𝒰.cover.X 𝒰.cover.f I e H).invariants
  have hfinE : Module.Finite Γ(S, ⊤) E := invariantFinite 𝒰.cover.X 𝒰.cover.f I e H
  have hprojE : Module.Projective Γ(S, ⊤) E := invariantProjective 𝒰.cover.X 𝒰.cover.f I e H
  have hetE : Algebra.Etale Γ(S, ⊤) E := invariantEtale 𝒰.cover.X 𝒰.cover.f I e H
  refine ⟨E, inferInstance, inferInstance, hfinE, hprojE, hetE, ?_⟩
  exact ⟨finiteAffineWeilIso 𝒰.cover I e H⟩

/-- The complete arbitrary-ring Weil presentation derived from an actual
étale permutation atlas. -/
theorem permutationAtlasWeilPresentation : PermutationAtlasWeilPresentationStatement.{u} := by
  intro R _ D hD
  obtain ⟨E, hE, aE, hfin, hproj, het, ⟨e⟩⟩ := hD.exists_weilGroup
  letI : CommRing E := hE
  letI : Algebra Γ(Spec (CommRingCat.of R), ⊤) E := aE
  letI : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) E := hfin
  letI : Module.Projective Γ(Spec (CommRingCat.of R), ⊤) E := hproj
  letI : Algebra.Etale Γ(Spec (CommRingCat.of R), ⊤) E := het
  let φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom
  letI : Algebra Γ(Spec (CommRingCat.of R), ⊤) R := φ.hom.toAlgebra
  let E' := R ⊗[Γ(Spec (CommRingCat.of R), ⊤)] E
  refine ⟨E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hφ : Spec.map φ = (Spec (CommRingCat.of R)).isoSpec.hom :=
    SpecMap_ΓSpecIso_hom (CommRingCat.of R)
  have e' : (baseChange (Spec.map φ)).obj
      (WeilGm.groupScheme Γ(Spec (CommRingCat.of R), ⊤) E) ≅
      WeilGm.groupScheme (CommRingCat.of R) E' := WeilGm.baseChangeIso φ E
  rw [hφ] at e'
  exact ⟨e ≪≫ e'⟩

end Langlands.GroupScheme
