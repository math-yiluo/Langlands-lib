import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Finite affine fppf splitting covers of groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}}

/-- A finite affine fppf cover on which an actual group becomes diagonalizable. -/
structure AffineSplittingCover (H : GroupScheme S) where
  count : ℕ
  ring : Fin count → CommRingCat.{u}
  map : ∀ k, Spec (ring k) ⟶ S
  flat : ∀ k, Flat (map k)
  locallyOfFinitePresentation : ∀ k, LocallyOfFinitePresentation (map k)
  covers : ∀ s : S, ∃ k, s ∈ Set.range (map k)
  diagonalizable : ∀ k, IsDiagonalizable ((GroupScheme.baseChange (map k)).obj H)

/-- A multiplicative-type group over a quasi-compact base has a finite affine
fppf splitting cover. -/
theorem nonempty_affineSplittingCover [CompactSpace S] (H : GroupScheme S)
    (hH : IsMultiplicativeType H) : Nonempty (AffineSplittingCover H) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hH
  let j : S → 𝒰.I₀ := fun s => 𝒰.idx s
  let y : ∀ s, 𝒰.X (j s) := fun s => (𝒰.covers s).choose
  let a : ∀ s, (𝒰.X (j s)).affineOpenCover.I₀ :=
    fun s => (𝒰.X (j s)).affineOpenCover.idx (y s)
  let A : S → CommRingCat.{u} := fun s => (𝒰.X (j s)).affineOpenCover.X (a s)
  let g : ∀ s, Spec (A s) ⟶ S :=
    fun s => (𝒰.X (j s)).affineOpenCover.f (a s) ≫ 𝒰.f (j s)
  have hg : ∀ s, Flat (g s) ∧ LocallyOfFinitePresentation (g s) := by
    intro s
    have : Flat (𝒰.f (j s)) := (𝒰.map_prop (j s)).1
    have : LocallyOfFinitePresentation (𝒰.f (j s)) := (𝒰.map_prop (j s)).2
    exact ⟨inferInstance, inferInstance⟩
  have hgt : ∀ s, s ∈ Set.range (g s) := by
    intro s
    obtain ⟨z, hz⟩ := (𝒰.X (j s)).affineOpenCover.covers (y s)
    refine ⟨z, ?_⟩
    change 𝒰.f (j s) ((𝒰.X (j s)).affineOpenCover.f (a s) z) = s
    rw [hz]
    exact (𝒰.covers s).choose_spec
  have hsplit : ∀ s, IsDiagonalizable ((GroupScheme.baseChange (g s)).obj H) := by
    intro s
    exact IsDiagonalizable.of_iso (baseChangeCompIso (𝒰.f (j s)) _ H)
      ((h𝒰 (j s)).baseChange _)
  have hopen : ∀ s, IsOpen (Set.range (g s)) := by
    intro s
    have : Flat (g s) := (hg s).1
    have : LocallyOfFinitePresentation (g s) := (hg s).2
    exact (g s).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => Set.range (g s))
    hopen (fun s _ => Set.mem_iUnion.mpr ⟨s, hgt s⟩)
  let ε := t.equivFin
  let s₀ : Fin t.card → S := fun k => (ε.symm k).1
  refine ⟨{
    count := t.card
    ring := fun k => A (s₀ k)
    map := fun k => g (s₀ k)
    flat := fun k => (hg (s₀ k)).1
    locallyOfFinitePresentation := fun k => (hg (s₀ k)).2
    covers := ?_
    diagonalizable := fun k => hsplit (s₀ k) }⟩
  intro s
  obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
  refine ⟨ε ⟨x, hx⟩, ?_⟩
  rw [show s₀ (ε ⟨x, hx⟩) = x by simp [s₀]]
  exact hsx

/-- Choose a finite affine fppf splitting cover over a quasi-compact base. -/
def affineSplittingCover [CompactSpace S] (H : GroupScheme S)
    (hH : IsMultiplicativeType H) : AffineSplittingCover H :=
  Classical.choice (nonempty_affineSplittingCover H hH)

end Langlands.GroupScheme.RelativeMultiplicativeType
