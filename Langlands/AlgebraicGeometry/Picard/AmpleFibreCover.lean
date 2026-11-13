import Langlands.AlgebraicGeometry.Picard.FibreAmplenessBaseChange
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleIsoSubalgebraDescentProof
import Langlands.AbelianScheme.SubalgebraDescentProof
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Topology.Spectral.ConstructibleTopology

/-! # Finite covers of a base by fibre-ample loci of abelian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

/-- `f : X → S` has an ample-fibre cover of `V ⊆ S` if finitely many affine schemes
`T i → S` with image in `V`, each with a pullback square for `f` and a line bundle on it,
have fibre-ample loci whose images cover `V`. -/
def HasAmpleFibreCover {X S : Scheme.{u}} (f : X ⟶ S) (V : Set S) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (T W : ι → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (a : ∀ i, W i ⟶ X) (q : ∀ i, W i ⟶ T i) (L : ∀ i, LineBundle (W i)),
    (∀ i, IsPullback (a i) (q i) f (g i)) ∧ (∀ i, IsAffine (T i)) ∧
    (∀ i, Set.range (g i) ⊆ V) ∧
    ∀ s ∈ V, ∃ i, ∃ t : T i, g i t = s ∧ t ∈ ampleFibreLocus (q i) (L i)

/-- Composing with the bottom map of a pullback square transports an ample-fibre cover. -/
theorem HasAmpleFibreCover.of_isPullback {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} {α : X ⟶ X'} {h : S ⟶ S'} (hp : IsPullback α f f' h) {V : Set S}
    (hc : HasAmpleFibreCover f V) : HasAmpleFibreCover f' (h '' V) := by
  obtain ⟨ι, hι, T, W, g, a, q, L, hpb, haff, hrange, hcov⟩ := hc
  refine ⟨ι, hι, T, W, fun i ↦ g i ≫ h, fun i ↦ a i ≫ α, q, L,
    fun i ↦ (hpb i).paste_horiz hp, haff, ?_, ?_⟩
  · rintro i _ ⟨t, rfl⟩
    exact ⟨g i t, hrange i ⟨t, rfl⟩, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨i, t, rfl, ht⟩ := hcov s hs
    exact ⟨i, t, rfl, ht⟩

/-- An ample-fibre cover of the whole base survives base change between affine bases. -/
theorem HasAmpleFibreCover.baseChange {X₀ S₀ X₁ S₁ : Scheme.{u}} {f₀ : X₀ ⟶ S₀}
    {f₁ : X₁ ⟶ S₁} {α : X₁ ⟶ X₀} {φ : S₁ ⟶ S₀} (hp : IsPullback α f₁ f₀ φ)
    [IsAffine S₀] [IsAffine S₁] (hc : HasAmpleFibreCover f₀ Set.univ) :
    HasAmpleFibreCover f₁ Set.univ := by
  obtain ⟨ι, hι, T, W, g, a, q, L, hpb, haff, -, hcov⟩ := hc
  let T' : ι → Scheme.{u} := fun i ↦ pullback (g i) φ
  let g' : ∀ i, T' i ⟶ S₁ := fun i ↦ pullback.snd (g i) φ
  let r : ∀ i, T' i ⟶ T i := fun i ↦ pullback.fst (g i) φ
  let W' : ι → Scheme.{u} := fun i ↦ pullback (q i) (r i)
  let q' : ∀ i, W' i ⟶ T' i := fun i ↦ pullback.snd (q i) (r i)
  have hw : ∀ i, (pullback.fst (q i) (r i) ≫ a i) ≫ f₀ = (q' i ≫ g' i) ≫ φ := by
    intro i
    simp only [Category.assoc, q', g', r]
    rw [(hpb i).w, pullback.condition_assoc, pullback.condition]
  let a' : ∀ i, W' i ⟶ X₁ := fun i ↦ hp.lift _ _ (hw i)
  have hcomp : ∀ i, IsPullback (a' i ≫ α) (q' i) f₀ (g' i ≫ φ) := by
    intro i
    have h1 : a' i ≫ α = pullback.fst (q i) (r i) ≫ a i := hp.lift_fst _ _ _
    have h2 : g' i ≫ φ = r i ≫ g i := pullback.condition.symm
    rw [h1, h2]
    exact (IsPullback.of_hasPullback (q i) (r i)).paste_horiz (hpb i)
  have hpb' : ∀ i, IsPullback (a' i) (q' i) f₁ (g' i) := fun i ↦
    IsPullback.of_right (hcomp i) (hp.lift_snd _ _ _) hp
  refine ⟨ι, hι, T', W', g', a', q',
    fun i ↦ (LineBundle.pullback (pullback.fst (q i) (r i))).obj (L i), hpb', ?_,
    fun _ ↦ Set.subset_univ _, ?_⟩
  · intro i
    have := haff i
    infer_instance
  · intro s _
    obtain ⟨i, t, ht, htL⟩ := hcov (φ s) (Set.mem_univ _)
    obtain ⟨t', ht'1, ht'2⟩ := Scheme.Pullback.exists_preimage_pullback t s ht
    refine ⟨i, t', ht'2, ?_⟩
    rw [mem_ampleFibreLocus_iff_of_isPullback (IsPullback.of_hasPullback (q i) (r i))]
    rw [show r i t' = t from ht'1]
    exact htL

end Langlands.AlgebraicGeometry.Picard
