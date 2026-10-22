import Langlands.Representation.CuspidalSupport.BlockMap
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof

/-! Quasicuspidality of whole-Levi transport along a minimal conjugating permutation. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

section Geometry

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {w : Equiv.Perm (Fin n)}

/-- A transposition preserves blocks exactly when it swaps two coordinates of
one block. -/
theorem swap_mem_blockWeyl_iff (B : BlockShape n) (a b : Fin n) :
    Equiv.swap a b ∈ blockWeyl B ↔ blockIndex B a = blockIndex B b := by
  constructor
  · intro h
    have h' := h a
    rw [Equiv.swap_apply_left] at h'
    exact h'.symm
  · intro h x
    rcases eq_or_ne x a with rfl | hxa
    · rw [Equiv.swap_apply_left]
      exact h.symm
    rcases eq_or_ne x b with rfl | hxb
    · rw [Equiv.swap_apply_right]
      exact h
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- A permutation conjugating the actual Levis matches their block partitions. -/
theorem blockIndex_eq_iff_of_conjugatesLevi
    (hw : ConjugatesLevi (F := F) B C w) (a b : Fin n) :
    blockIndex C (w a) = blockIndex C (w b) ↔ blockIndex B a = blockIndex B b := by
  constructor
  · intro h
    have hs := conjugatesLevi_weyl_mem (conjugatesLevi_inv hw)
      ((swap_mem_blockWeyl_iff C _ _).mpr h)
    rw [← Equiv.swap_apply_apply, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hs
    exact (swap_mem_blockWeyl_iff B a b).mp hs
  · intro h
    have hs := conjugatesLevi_weyl_mem hw ((swap_mem_blockWeyl_iff B _ _).mpr h)
    rw [← Equiv.swap_apply_apply] at hs
    exact (swap_mem_blockWeyl_iff C _ _).mp hs

/-- Every source coordinate is sent into the target block of its source block. -/
theorem blockIndex_apply_eq_blockMap (hw : ConjugatesLevi (F := F) B C w)
    (a : Fin n) : blockIndex C (w a) = blockMap B C w (blockIndex B a) :=
  (blockIndex_eq_iff_of_conjugatesLevi hw _ _).mpr (blockIndex_index B _ _).symm

theorem blockMap_bijective (hw : ConjugatesLevi (F := F) B C w) :
    Function.Bijective (blockMap B C w) := by
  constructor
  · intro i j h
    have h' := (blockIndex_eq_iff_of_conjugatesLevi hw _ _).mp h
    simpa only [blockIndex_index] using h'
  · intro j
    refine ⟨blockIndex B (w⁻¹ (C.index j ⟨0, C.positive j⟩)), ?_⟩
    rw [← blockIndex_apply_eq_blockMap hw, Equiv.Perm.coe_inv, Equiv.apply_symm_apply,
      blockIndex_index]

/-- The block bijection determined by a conjugating permutation. -/
noncomputable def blockEquiv (hw : ConjugatesLevi (F := F) B C w) :
    Fin B.length ≃ Fin C.length :=
  Equiv.ofBijective _ (blockMap_bijective hw)

theorem exists_index_eq_apply_index (hw : ConjugatesLevi (F := F) B C w)
    (i : Fin B.length) (a : Fin (B.size i)) :
    ∃ b : Fin (C.size (blockMap B C w i)),
      C.index (blockMap B C w i) b = w (B.index i a) :=
  exists_index_of_blockIndex_eq C
    (by rw [blockIndex_apply_eq_blockMap hw, blockIndex_index])

/-- The position of an image coordinate inside its target block. -/
noncomputable def innerMap (hw : ConjugatesLevi (F := F) B C w)
    (i : Fin B.length) (a : Fin (B.size i)) : Fin (C.size (blockMap B C w i)) :=
  (exists_index_eq_apply_index hw i a).choose

theorem index_innerMap (hw : ConjugatesLevi (F := F) B C w)
    (i : Fin B.length) (a : Fin (B.size i)) :
    C.index (blockMap B C w i) (innerMap hw i a) = w (B.index i a) :=
  (exists_index_eq_apply_index hw i a).choose_spec

theorem innerMap_bijective (hw : ConjugatesLevi (F := F) B C w)
    (i : Fin B.length) : Function.Bijective (innerMap hw i) := by
  constructor
  · intro a b h
    have h' := congrArg (C.index (blockMap B C w i)) h
    rw [index_innerMap, index_innerMap] at h'
    exact (B.index i).injective (w.injective h')
  · intro b
    have hblock : blockIndex B (w⁻¹ (C.index (blockMap B C w i) b)) = i := by
      apply (blockMap_bijective hw).1
      rw [← blockIndex_apply_eq_blockMap hw, Equiv.Perm.coe_inv, Equiv.apply_symm_apply,
        blockIndex_index]
    obtain ⟨a, ha⟩ := exists_index_of_blockIndex_eq B hblock
    refine ⟨a, (C.index (blockMap B C w i)).injective ?_⟩
    rw [index_innerMap, ha, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

/-- Corresponding source and target blocks have the same size. -/
theorem size_blockMap (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    B.size i = C.size (blockMap B C w i) :=
  Fin.equiv_iff_eq.mp ⟨Equiv.ofBijective _ (innerMap_bijective hw i)⟩

/-- For a minimal representative, each source block is carried in increasing
order onto its target block. -/
theorem apply_index_eq (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) (a : Fin (B.size i)) :
    w (B.index i a) =
      C.index (blockMap B C w i) (Fin.cast (size_blockMap hw i) a) := by
  have hmono : StrictMono (innerMap hw i) := by
    intro a b hab
    have h := hmin.1 i hab
    simp only at h
    rw [← index_innerMap hw i a, ← index_innerMap hw i b] at h
    exact (index_strictMono C _).lt_iff_lt.mp h
  have hrange : Set.range (innerMap hw i) =
      Set.range (Fin.cast (size_blockMap hw i)) := by
    rw [(innerMap_bijective hw i).2.range_eq]
    refine (Set.range_eq_univ.mpr fun b => ⟨Fin.cast (size_blockMap hw i).symm b,
      Fin.ext rfl⟩).symm
  have heq := (hmono.range_inj_of_wellFoundedLT (Fin.cast_strictMono _)).mp hrange
  rw [← index_innerMap hw i a, heq]

/-- Entries of inverse whole-Levi conjugation, in corresponding blocks. -/
theorem leviConjugation_symm_block_entry (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    (leviConjugation B C w hw).symm m i a b =
      m (blockMap B C w i) (Fin.cast (size_blockMap hw i) a)
        (Fin.cast (size_blockMap hw i) b) := by
  rw [← B.leviEmbedding_apply_same F, leviConjugation_symm_embedding,
    mul_permutation_entry, permutation_inv, permutation_mul_entry, inv_inv,
    apply_index_eq hmin hw, apply_index_eq hmin hw, C.leviEmbedding_apply_same]

end Geometry

section Cast

variable {F : Type uF} [Field F]

/-- The same block sizes, regarded as a block shape of an equal rank. -/
def castShape {k l : ℕ} (h : k = l) (D : BlockShape k) : BlockShape l :=
  ⟨D.length, D.size, D.positive, D.sum_eq.trans h⟩

theorem mem_castShape_parabolic_iff {k l : ℕ} (h : k = l) (D : BlockShape k)
    (g : GeneralLinear k F) (g' : GeneralLinear l F)
    (hg : ∀ a b, g' a b = g (Fin.cast h.symm a) (Fin.cast h.symm b)) :
    g' ∈ (castShape h D).parabolic F ↔ g ∈ D.parabolic F := by
  subst h
  have hgg : g' = g := Units.ext (Matrix.ext fun a b => hg a b)
  subst hgg
  exact Iff.rfl

theorem mem_castShape_unipotentSubgroup_iff {k l : ℕ} (h : k = l)
    (D : BlockShape k) (g : GeneralLinear k F) (g' : GeneralLinear l F)
    (hg : ∀ a b, g' a b = g (Fin.cast h.symm a) (Fin.cast h.symm b)) :
    g' ∈ (castShape h D).unipotentSubgroup F ↔ g ∈ D.unipotentSubgroup F := by
  subst h
  have hgg : g' = g := Units.ext (Matrix.ext fun a b => hg a b)
  subst hgg
  exact Iff.rfl

end Cast

section Refinement

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {w : Equiv.Perm (Fin n)}

/-- The source refinement corresponding to a target refinement. -/
def pullbackRefinement (hw : ConjugatesLevi (F := F) B C w)
    (R : BlockRefinement C) : BlockRefinement B :=
  fun i => castShape (size_blockMap hw i).symm (R (blockMap B C w i))

theorem mem_refinedParabolic_pullback_iff (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (R : BlockRefinement C) (m : C.Levi F) :
    (leviConjugation B C w hw).symm m ∈
        refinedParabolic F B (pullbackRefinement hw R) ↔
      m ∈ refinedParabolic F C R := by
  rw [mem_refinedParabolic, mem_refinedParabolic,
    ← (blockEquiv hw).forall_congr_right]
  apply forall_congr'
  intro i
  exact mem_castShape_parabolic_iff _ _ _ _
    (leviConjugation_symm_block_entry hmin hw m i)

theorem mem_refinedUnipotent_pullback_iff (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (R : BlockRefinement C) (m : C.Levi F) :
    (leviConjugation B C w hw).symm m ∈
        refinedUnipotent F B (pullbackRefinement hw R) ↔
      m ∈ refinedUnipotent F C R := by
  rw [mem_refinedUnipotent, mem_refinedUnipotent,
    ← (blockEquiv hw).forall_congr_right]
  apply forall_congr'
  intro i
  exact mem_castShape_unipotentSubgroup_iff _ _ _ _
    (leviConjugation_symm_block_entry hmin hw m i)

/-- Inverse whole-Levi conjugation carries each target refined radical onto
the corresponding source refined radical. -/
theorem refinedUnipotent_map_leviConjugation_symm
    (hmin : IsMinimalRepresentative B C w) (hw : ConjugatesLevi (F := F) B C w)
    (R : BlockRefinement C) :
    (refinedUnipotent F C R).map (leviConjugation B C w hw).symm.toMonoidHom =
      refinedUnipotent F B (pullbackRefinement hw R) := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    ← mem_refinedUnipotent_pullback_iff hmin hw R, MulEquiv.symm_apply_apply]

/-- A proper target refinement has a proper corresponding source refinement. -/
theorem refinedParabolic_pullback_ne_top (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (R : BlockRefinement C)
    (hR : refinedParabolic F C R ≠ ⊤) :
    refinedParabolic F B (pullbackRefinement hw R) ≠ ⊤ := by
  intro htop
  apply hR
  rw [eq_top_iff]
  intro m _
  rw [← mem_refinedParabolic_pullback_iff hmin hw R, htop]
  exact Subgroup.mem_top _

end Refinement

variable {F : Type uF} [Field F] {n : ℕ}

/-- The quotient step of Weyl transport, once actual radical images and
properness of their source refinements have been proved. -/
theorem isLeviQuasicuspidal_transport_of_refinement_images
    (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w)
    (hgeometry : ∀ R : BlockRefinement C, refinedParabolic F C R ≠ ⊤ →
      ∃ S : BlockRefinement B, refinedParabolic F B S ≠ ⊤ ∧
        (refinedUnipotent F C R).map (leviConjugation B C w hw).symm.toMonoidHom =
          refinedUnipotent F B S)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) (hρ : IsLeviQuasicuspidal B ρ) :
    IsLeviQuasicuspidal C (transport B C w hw ρ) := by
  intro R hR
  obtain ⟨S, hS, hU⟩ := hgeometry R hR
  have hzero : Subsingleton (Jacquet.Coinvariants ρ
      ((refinedUnipotent F C R).map (leviConjugation B C w hw).symm.toMonoidHom)) := by
    rw [hU]
    exact hρ S hS
  let := hzero
  exact (Jacquet.coinvariantsMapEquiv ρ
    (leviConjugation B C w hw).symm.toMonoidHom
    (refinedUnipotent F C R)).injective.subsingleton

/-- Whole-Levi transport along a minimal conjugating permutation preserves
quasicuspidality, over any field and in any carrier universe. -/
theorem isLeviQuasicuspidal_transport (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) (hρ : IsLeviQuasicuspidal B ρ) :
    IsLeviQuasicuspidal C (transport B C w hw ρ) :=
  isLeviQuasicuspidal_transport_of_refinement_images B C w hw
    (fun R hR => ⟨pullbackRefinement hw R,
      refinedParabolic_pullback_ne_top hmin hw R hR,
      refinedUnipotent_map_leviConjugation_symm hmin hw R⟩) ρ hρ

/-- The published transport-quasicuspidality component, for every rank
including zero. -/
theorem minimalWeylTransportQuasicuspidal {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ w hw
  exact isLeviQuasicuspidal_transport B C w.val w.property hw ρ.representation hρ

/-- Check the complete unapplied telescope, including both independent universes. -/
example : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n :=
  @minimalWeylTransportQuasicuspidal.{uF, uV}

end Langlands.CuspidalSupport
