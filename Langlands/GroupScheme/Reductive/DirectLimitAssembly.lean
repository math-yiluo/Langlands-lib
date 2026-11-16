import Langlands.GroupScheme.Reductive.DirectLimitGeometry
import Langlands.GroupScheme.Reductive.FibreLocusComparisons
import Langlands.GroupScheme.Reductive.DirectLimitReductiveStatement
import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleLocusStatement

/-! # Assembly of the direct-limit equivalences -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A dependent predicate holds at every sufficiently large index above `i₀`. -/
def directedEventually {ι : Type u} [Preorder ι] (i₀ : ι)
    (P : ∀ i : ι, i₀ ≤ i → Prop) : Prop :=
  ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i → P i h

theorem directedEventually_congr {ι : Type u} [Preorder ι] {i₀ : ι}
    {P Q : ∀ i : ι, i₀ ≤ i → Prop}
    (hPQ : ∀ i h, P i h ↔ Q i h) :
    directedEventually i₀ P ↔ directedEventually i₀ Q := by
  constructor
  · rintro ⟨i₁, h₁, hP⟩
    exact ⟨i₁, h₁, fun i h hi => (hPQ i h).mp (hP i h hi)⟩
  · rintro ⟨i₁, h₁, hQ⟩
    exact ⟨i₁, h₁, fun i h hi => (hPQ i h).mpr (hQ i h hi)⟩

/-- Directedness permits a common stage for two eventual conditions. -/
theorem directedEventually_and {ι : Type u} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {i₀ : ι} {P Q : ∀ i : ι, i₀ ≤ i → Prop} :
    directedEventually i₀ (fun i h => P i h ∧ Q i h) ↔
      directedEventually i₀ P ∧ directedEventually i₀ Q := by
  constructor
  · rintro ⟨i₁, h₁, hPQ⟩
    exact ⟨⟨i₁, h₁, fun i h hi => (hPQ i h hi).1⟩,
      ⟨i₁, h₁, fun i h hi => (hPQ i h hi).2⟩⟩
  · rintro ⟨⟨i₁, h₁, hP⟩, ⟨i₂, _, hQ⟩⟩
    obtain ⟨j, hj₁, hj₂⟩ := directed_of (· ≤ ·) i₁ i₂
    exact ⟨j, h₁.trans hj₁, fun i h hi =>
      ⟨hP i h (hj₁.trans hi), hQ i h (hj₂.trans hi)⟩⟩

local instance directLimitAssembly_smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom b))

local instance directLimitAssembly_affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A : ι ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : ι) (G₀ : GroupScheme (Spec (A.obj i₀)))
    [Smooth G₀.X.hom] [IsAffineHom G₀.X.hom]

include hc

/-- Whole-group reductivity descends along a directed ring colimit. -/
theorem isReductive_baseChange_iff_eventually :
    IsReductive ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) ↔
      directedEventually i₀ (fun i h => IsReductive (directedSystemBaseChange A i₀ G₀ i h)) := by
  calc
    _ ↔ GeometricallyConnected ((baseChange (Spec.map (c.ι.app i₀))).obj G₀).X.hom ∧
        identityComponentReductiveLocus ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) =
          Set.univ :=
      isReductive_iff_geometricallyConnected_and_locus_eq_univ _
    _ ↔ directedEventually i₀
          (fun i h => GeometricallyConnected (directedSystemBaseChange A i₀ G₀ i h).X.hom) ∧
        directedEventually i₀
          (fun i h => identityComponentReductiveLocus
            (directedSystemBaseChange A i₀ G₀ i h) = Set.univ) :=
      and_congr (geometricallyConnected_baseChange_iff_eventually A c hc i₀ G₀)
        (identityComponentReductiveLocus_eq_univ_iff_eventually A c hc i₀ G₀)
    _ ↔ directedEventually i₀ (fun i h =>
          GeometricallyConnected (directedSystemBaseChange A i₀ G₀ i h).X.hom ∧
          identityComponentReductiveLocus (directedSystemBaseChange A i₀ G₀ i h) = Set.univ) :=
      directedEventually_and.symm
    _ ↔ _ := directedEventually_congr fun i h =>
      (isReductive_iff_geometricallyConnected_and_locus_eq_univ
        (directedSystemBaseChange A i₀ G₀ i h)).symm

/-- Openness of the initial semisimple locus suffices for its direct-limit descent. -/
theorem identityComponentSemisimpleLocus_eq_univ_iff_eventually_of_isOpen
    (hs : IsOpen (identityComponentSemisimpleLocus G₀)) :
    identityComponentSemisimpleLocus ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) = Set.univ ↔
      directedEventually i₀ (fun i h =>
        identityComponentSemisimpleLocus (directedSystemBaseChange A i₀ G₀ i h) = Set.univ) := by
  simpa only [directedEventually, directedSystemBaseChange,
    identityComponentSemisimpleLocus_baseChange] using
    Langlands.AlgebraicGeometry.spec_preimage_eq_univ_iff_eventually_of_isOpen A c hc i₀
      (identityComponentSemisimpleLocus G₀) hs

/-- Relative semisimplicity descends once the initial semisimple locus is open. -/
theorem isReductive_and_semisimple_baseChange_iff_eventually_of_isOpen
    (hs : IsOpen (identityComponentSemisimpleLocus G₀)) :
    (IsReductive ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) ∧
      ∀ s, IsSemisimple (geometricFiber ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) s)) ↔
      directedEventually i₀ (fun i h =>
        IsReductive (directedSystemBaseChange A i₀ G₀ i h) ∧
          ∀ s, IsSemisimple (geometricFiber (directedSystemBaseChange A i₀ G₀ i h) s)) := by
  calc
    _ ↔ GeometricallyConnected ((baseChange (Spec.map (c.ι.app i₀))).obj G₀).X.hom ∧
        identityComponentSemisimpleLocus ((baseChange (Spec.map (c.ι.app i₀))).obj G₀) =
          Set.univ :=
      isReductive_and_semisimple_geometricFibres_iff_locus _
    _ ↔ directedEventually i₀
          (fun i h => GeometricallyConnected (directedSystemBaseChange A i₀ G₀ i h).X.hom) ∧
        directedEventually i₀
          (fun i h => identityComponentSemisimpleLocus
            (directedSystemBaseChange A i₀ G₀ i h) = Set.univ) :=
      and_congr (geometricallyConnected_baseChange_iff_eventually A c hc i₀ G₀)
        (identityComponentSemisimpleLocus_eq_univ_iff_eventually_of_isOpen A c hc i₀ G₀ hs)
    _ ↔ directedEventually i₀ (fun i h =>
          GeometricallyConnected (directedSystemBaseChange A i₀ G₀ i h).X.hom ∧
          identityComponentSemisimpleLocus (directedSystemBaseChange A i₀ G₀ i h) = Set.univ) :=
      directedEventually_and.symm
    _ ↔ _ := directedEventually_congr fun i h =>
      (isReductive_and_semisimple_geometricFibres_iff_locus
        (directedSystemBaseChange A i₀ G₀ i h)).symm

omit hc

/-- The four direct-limit clauses reduce to the separate semisimple-openness statement. -/
theorem directLimitReductive_of_semisimpleLocusOpen
    (hOpen : IdentityComponentSemisimpleLocusOpenStatement.{u}) :
    DirectLimitReductiveStatement.{u} := by
  intro ι _ _ A c hc i₀ G₀ _ _
  dsimp only
  refine ⟨identityComponentReductiveLocus_eq_univ_iff_eventually A c hc i₀ G₀,
    isReductive_baseChange_iff_eventually A c hc i₀ G₀, ?_, ?_⟩
  · simpa only [directedEventually, directedSystemBaseChange,
      identityComponentSemisimpleLocus_eq_univ_iff, Functor.const] using
      identityComponentSemisimpleLocus_eq_univ_iff_eventually_of_isOpen A c hc i₀ G₀
        (hOpen _ G₀)
  · exact isReductive_and_semisimple_baseChange_iff_eventually_of_isOpen A c hc i₀ G₀
      (hOpen _ G₀)

end Langlands.GroupScheme
