import Langlands.Representation.Aubert.TwoSidedSupport
import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.Geometric.BruhatMatrixExistenceProof
import Langlands.Representation.Geometric.BruhatWeylReflectionProof
import Langlands.Representation.Geometric.BruhatDescent

/-! The corrected Weyl core as an actual parabolic-invariant matrix support. -/

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe u

variable {n : ℕ}

private theorem blockIndex_singletons (i : Fin n) :
    blockIndex (BlockShape.singletons n) i = i := by
  have h := blockIndex_index (BlockShape.singletons n) i (0 : Fin 1)
  simpa only [BlockShape.singletons_index (n := n) i (0 : Fin 1)] using h

private theorem blockWeyl_singletons_eq_one (w : Equiv.Perm (Fin n))
    (hw : w ∈ blockWeyl (BlockShape.singletons n)) : w = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h := congrArg Fin.val (hw i)
  simpa only [blockIndex_singletons, Equiv.Perm.one_apply] using h

private theorem mem_doubleCoset_iff_mk_eq {G : Type*} [Group G]
    (H K : Subgroup G) (a b : G) :
    b ∈ DoubleCoset.doubleCoset a H K ↔ DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [DoubleCoset.mem_doubleCoset, DoubleCoset.eq]
  rfl

variable (R : Type u) [CommRing R]

/-- A Borel double coset with the Library's inverse-permutation convention. -/
def borelCell (w : Equiv.Perm (Fin n)) : Set (GeneralLinear n R) :=
  DoubleCoset.doubleCoset (permutation n R w)⁻¹
    (upperTriangularSubgroup n R) (upperTriangularSubgroup n R)

/-- The actual matrix support indexed by a set of Weyl elements. -/
def bruhatSupport (θ : Set (Equiv.Perm (Fin n))) : Set (GeneralLinear n R) :=
  {g | ∃ w ∈ θ, g ∈ borelCell R w}

theorem bruhatSupport_mono {θ η : Set (Equiv.Perm (Fin n))} (h : θ ⊆ η) :
    bruhatSupport R θ ⊆ bruhatSupport R η := by
  rintro g ⟨w, hw, hg⟩
  exact ⟨w, h hw, hg⟩

@[simp] theorem bruhatSupport_empty : bruhatSupport R (∅ : Set (Equiv.Perm (Fin n))) = ∅ := by
  ext g
  simp [bruhatSupport]

theorem borelCell_subset_parabolicCell (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    borelCell R w ⊆ DoubleCoset.doubleCoset (permutation n R w)⁻¹
      (B.parabolic R) (C.parabolic R) := by
  intro g hg
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp hg
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨a, B.upperTriangularSubgroup_le_parabolic R ha,
      b, C.upperTriangularSubgroup_le_parabolic R hb, h⟩

variable [Nontrivial R]

/-- Actual Borel double cosets of inverse permutation matrices are distinct. -/
theorem inverse_permutation_borelCell_injective {v w : Equiv.Perm (Fin n)}
    (h : DoubleCoset.mk (upperTriangularSubgroup n R) (upperTriangularSubgroup n R)
        (permutation n R v)⁻¹ =
      DoubleCoset.mk (upperTriangularSubgroup n R) (upperTriangularSubgroup n R)
        (permutation n R w)⁻¹) : v = w := by
  have hc : DoubleCoset.mk ((BlockShape.singletons n).parabolic R)
        ((BlockShape.singletons n).parabolic R) (permutation n R v)⁻¹ =
      DoubleCoset.mk ((BlockShape.singletons n).parabolic R)
        ((BlockShape.singletons n).parabolic R) (permutation n R w)⁻¹ := by
    apply (mem_doubleCoset_iff_mk_eq _ _ _ _).mp
    exact borelCell_subset_parabolicCell R (BlockShape.singletons n) (BlockShape.singletons n) v
      ((mem_doubleCoset_iff_mk_eq _ _ _ _).mpr h)
  have hW := weyl_doubleCoset_eq_of_inverse_permutation_eq
    (BlockShape.singletons n) (BlockShape.singletons n) hc
  obtain ⟨a, ha, b, hb, hw⟩ := DoubleCoset.eq.mp hW
  rw [blockWeyl_singletons_eq_one a ha, blockWeyl_singletons_eq_one b hb,
    one_mul, mul_one] at hw
  exact hw.symm

@[simp] theorem inverse_permutation_mem_bruhatSupport_iff
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n)) :
    (permutation n R w)⁻¹ ∈ bruhatSupport R θ ↔ w ∈ θ := by
  constructor
  · rintro ⟨v, hv, hcell⟩
    have heq : v = w := inverse_permutation_borelCell_injective R
      ((mem_doubleCoset_iff_mk_eq _ _ _ _).mp hcell)
    exact heq ▸ hv
  · intro hw
    exact ⟨w, hw, DoubleCoset.mem_doubleCoset_self _ _ _⟩

section Field

variable (F : Type u) [Field F]

theorem exists_borelCell (g : GeneralLinear n F) :
    ∃ w : Equiv.Perm (Fin n), g ∈ borelCell F w := by
  obtain ⟨a, b, w, ha, hb, hg⟩ := fieldUpperBruhatFactorizationTheorem F n g
  refine ⟨w⁻¹, DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b, hb, ?_⟩⟩
  simpa only [permutation_inv, inv_inv] using hg

@[simp] theorem bruhatSupport_univ :
    bruhatSupport F (Set.univ : Set (Equiv.Perm (Fin n))) = Set.univ := by
  ext g
  obtain ⟨w, hw⟩ := exists_borelCell F g
  exact iff_of_true ⟨w, trivial, hw⟩ trivial

/-- Taking the greatest actual parabolic-invariant matrix support agrees exactly
with taking the corrected two-sided Weyl core. -/
theorem twoSidedCore_bruhatSupport (B C : BlockShape n)
    (θ : Set (Equiv.Perm (Fin n))) :
    twoSidedCore (B.parabolic F) (C.parabolic F) (bruhatSupport F θ) =
      bruhatSupport F (weylSupport B C θ) := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, hwg⟩ := exists_borelCell F g
    refine ⟨w, ?_, hwg⟩
    intro v hv
    apply (inverse_permutation_mem_bruhatSupport_iff F θ v).mp
    apply hg
    apply (mem_doubleCoset_iff_mk_eq _ _ _ _).mpr
    have hvg : DoubleCoset.mk (B.parabolic F) (C.parabolic F)
        (permutation n F v)⁻¹ =
        DoubleCoset.mk (B.parabolic F) (C.parabolic F) (permutation n F w)⁻¹ :=
      inverse_permutation_doubleCoset_eq_of_weyl_eq F B C
        (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hv))
    have hwg' := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp
      (borelCell_subset_parabolicCell F B C w hwg)
    exact (hvg.trans hwg').symm
  · rintro ⟨w, hw, hwg⟩ x hx
    obtain ⟨v, hvx⟩ := exists_borelCell F x
    refine ⟨v, ?_, hvx⟩
    apply hw
    apply (mem_doubleCoset_iff_mk_eq _ _ _ _).mpr
    have hvg := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp
      (borelCell_subset_parabolicCell F B C v hvx)
    have hwg' := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp
      (borelCell_subset_parabolicCell F B C w hwg)
    have hgx := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp hx
    exact (weyl_doubleCoset_eq_of_inverse_permutation_eq B C
      (hvg.trans (hwg'.trans hgx).symm)).symm

theorem corrected_bruhatSupport_invariant (B C : BlockShape n)
    (θ : Set (Equiv.Perm (Fin n))) :
    IsTwoSidedInvariant (B.parabolic F) (C.parabolic F)
      (bruhatSupport F (weylSupport B C θ)) := by
  rw [← twoSidedCore_bruhatSupport]
  exact twoSidedCore_invariant _ _ _

end Field
end Langlands.Aubert.Support
