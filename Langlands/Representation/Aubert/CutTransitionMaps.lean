import Langlands.Representation.Aubert.TransitionMaps
import Langlands.Representation.Geometric.BlockWeylCutProof
import Langlands.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.Geometric.StandardIntersectionsProof

/-! The actual Aubert diagram indexed by inclusion of interior cuts. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric

universe uF uV

section ShapeOrder

variable {n : ℕ} {B C : BlockShape n} {R : Type*} [CommRing R]

/-- Finer-block equality implies coarser-block equality. -/
theorem blockIndex_eq_of_cuts_subset (h : B.cuts ⊆ C.cuts) {a b : Fin n}
    (hab : blockIndex C a = blockIndex C b) : blockIndex B a = blockIndex B b := by
  apply (blockIndex_eq_iff_cut_sides B a b).mpr
  intro i hi
  exact (blockIndex_eq_iff_cut_sides C a b).mp hab i (h hi)

/-- A strict separation by coarse blocks remains strict after adding cuts. -/
theorem blockIndex_lt_of_cuts_subset (h : B.cuts ⊆ C.cuts) {a b : Fin n}
    (hab : blockIndex B a < blockIndex B b) : blockIndex C a < blockIndex C b := by
  have hab' : a < b := by
    by_contra hn
    exact (not_le_of_gt hab) (blockIndex_monotone B (le_of_not_gt hn))
  apply lt_of_le_of_ne (blockIndex_monotone C hab'.le)
  intro heq
  exact hab.ne (blockIndex_eq_of_cuts_subset h heq)

/-- Ambient-coordinate criterion for an actual upper unipotent radical. -/
theorem mem_unipotentSubgroup_iff_blockIndex (B : BlockShape n)
    (g : GeneralLinear n R) :
    g ∈ B.unipotentSubgroup R ↔
      ∀ a b, blockIndex B b ≤ blockIndex B a →
        g a b = if a = b then 1 else 0 := by
  rw [B.mem_unipotentSubgroup_iff, Geometric.mem_parabolic_iff_blockIndex R]
  constructor
  · rintro ⟨hp, hd⟩ a b hab
    rcases lt_or_eq_of_le hab with hlt | heq
    · have hne : a ≠ b := by intro h; subst b; exact lt_irrefl _ hlt
      simp only [hne, ↓reduceIte]
      exact hp a b hlt
    · obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
      obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
      change blockIndex B (B.index j y) = blockIndex B (B.index i x) at heq
      simp only [blockIndex_index] at heq
      subst j
      change g (B.index i x) (B.index i y) =
        if B.index i x = B.index i y then 1 else 0
      simpa only [EmbeddingLike.apply_eq_iff_eq] using hd i x y
  · intro hg
    constructor
    · intro a b hab
      have hne : a ≠ b := by intro h; subst b; exact lt_irrefl _ hab
      simpa only [hne, ↓reduceIte] using hg a b hab.le
    · intro i x y
      simpa only [EmbeddingLike.apply_eq_iff_eq] using
        hg (B.index i x) (B.index i y) (by simpa only [blockIndex_index] using le_rfl)

/-- Adding interior cuts makes the actual standard parabolic smaller. -/
theorem parabolic_le_of_cuts_subset (h : B.cuts ⊆ C.cuts) :
    C.parabolic R ≤ B.parabolic R := by
  intro g hg
  apply (Geometric.mem_parabolic_iff_blockIndex R B g).mpr
  intro a b hab
  exact (Geometric.mem_parabolic_iff_blockIndex R C g).mp hg a b
    (blockIndex_lt_of_cuts_subset h hab)

/-- Adding interior cuts makes the actual upper unipotent radical larger. -/
theorem unipotentSubgroup_le_of_cuts_subset (h : B.cuts ⊆ C.cuts) :
    B.unipotentSubgroup R ≤ C.unipotentSubgroup R := by
  intro g hg
  apply (mem_unipotentSubgroup_iff_blockIndex C g).mpr
  intro a b hab
  apply (mem_unipotentSubgroup_iff_blockIndex B g).mp hg a b
  by_contra hn
  exact (not_lt_of_ge hab) (blockIndex_lt_of_cuts_subset h (lt_of_not_ge hn))

end ShapeOrder

namespace Transition

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} {B C D : BlockShape n}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual transition attached to inclusion of cut sets. -/
def cutMap (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (h : B.cuts ⊆ C.cuts) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (term T B ρ).IntertwiningMap (term T C ρ) :=
  map T ρ (parabolic_le_of_cuts_subset h) (unipotentSubgroup_le_of_cuts_subset h)

@[simp]
theorem cutMap_refl (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    cutMap T (B := B) ρ Finset.Subset.rfl =
      Representation.IntertwiningMap.id (term T B ρ) :=
  map_refl T B ρ

theorem cutMap_comp (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hBC : B.cuts ⊆ C.cuts) (hCD : C.cuts ⊆ D.cuts) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (cutMap T ρ hCD).comp (cutMap T ρ hBC) = cutMap T ρ (hBC.trans hCD) :=
  map_comp T ρ _ _ _ _

end Transition

end Langlands.Aubert
