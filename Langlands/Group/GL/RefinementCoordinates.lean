import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! Reindexing a nested refinement into its original ordered blocks. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Geometric

universe u
variable {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
    (R : Type u) [CommRing R]

/-- Reindex the original Levi product into outer and inner blocks, using the
specified equality of each block's size. -/
def nestedLeviEquiv : B.Levi R ≃* ∀ i, (S i).Levi R where
  toEquiv := ((Equiv.piCongrLeft (fun i => GeneralLinear (B.size i) R) e).symm.trans
    (Equiv.piCongrRight fun a => (reindex (R := R) (finCongr (hs a).symm)).toEquiv)).trans
      (Equiv.piCurry fun i k => GeneralLinear ((S i).size k) R)
  map_mul' m m' := by
    funext i k
    exact (reindex (R := R) (finCongr (hs ⟨i, k⟩).symm)).map_mul _ _

@[simp] theorem nestedLeviEquiv_apply (m : B.Levi R)
    (i : Fin D.length) (k : Fin (S i).length) :
    nestedLeviEquiv B D S e hs R m i k =
      reindex (R := R) (finCongr (hs ⟨i, k⟩).symm) (m (e ⟨i, k⟩)) := rfl

@[simp] theorem nestedLeviEquiv_entry (m : B.Levi R)
    (i : Fin D.length) (k : Fin (S i).length)
    (x y : Fin ((S i).size k)) :
    nestedLeviEquiv B D S e hs R m i k x y =
      m (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) (Fin.cast (hs ⟨i, k⟩) y) := rfl

theorem nestedLeviEquiv_symm_apply (m : ∀ i, (S i).Levi R)
    (i : Fin D.length) (k : Fin (S i).length) :
    (nestedLeviEquiv B D S e hs R).symm m (e ⟨i, k⟩) =
      reindex (R := R) (finCongr (hs ⟨i, k⟩)) (m i k) := by
  have h := congrArg (fun q => q i k)
    ((nestedLeviEquiv B D S e hs R).apply_symm_apply m)
  change reindex (R := R) (finCongr (hs ⟨i, k⟩).symm)
    ((nestedLeviEquiv B D S e hs R).symm m (e ⟨i, k⟩)) = m i k at h
  exact (reindex (R := R) (finCongr (hs ⟨i, k⟩).symm)).injective
    (h.trans ((reindex (R := R) (finCongr (hs ⟨i, k⟩).symm)).apply_symm_apply
      (m i k)).symm)

/-- The nested product is identified with the existing actual refined Levi. -/
def leviRefinementEquiv : B.Levi R ≃* refinedLevi R D S :=
  (nestedLeviEquiv B D S e hs R).trans (refinedLeviEquiv R D S)

@[simp] theorem leviRefinementEquiv_val (m : B.Levi R) (i : Fin D.length) :
    (leviRefinementEquiv B D S e hs R m).val i =
      (S i).leviEmbedding R (nestedLeviEquiv B D S e hs R m i) := rfl

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The product reindexing respects the actual matrix topologies. -/
def nestedLeviEquivContinuous : B.Levi R ≃ₜ* ∀ i, (S i).Levi R where
  toMulEquiv := nestedLeviEquiv B D S e hs R
  continuous_toFun := continuous_pi fun i => continuous_pi fun k =>
    (reindexContinuous (R := R) (finCongr (hs ⟨i, k⟩).symm)).continuous.comp
      (continuous_apply (e ⟨i, k⟩))
  continuous_invFun := by
    apply continuous_pi
    intro b
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective b
    change Continuous (fun m : ∀ i, (S i).Levi R =>
      (nestedLeviEquiv B D S e hs R).symm m (e ⟨i, k⟩))
    simp_rw [nestedLeviEquiv_symm_apply]
    exact (reindexContinuous (R := R) (finCongr (hs ⟨i, k⟩))).continuous.comp
      ((continuous_apply k).comp (continuous_apply i))

/-- The actual subgroup-valued Levi equivalence is continuous in both directions. -/
def leviRefinementEquivContinuous : B.Levi R ≃ₜ* refinedLevi R D S :=
  (nestedLeviEquivContinuous B D S e hs R).trans (refinedLeviEquivContinuous R D S)

end Topology

variable (hc : ∀ (i : Fin D.length) (k : Fin (S i).length) (x : Fin ((S i).size k)),
    D.index i ((S i).index k x) = B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x))

include hc in
/-- An exact standard-coordinate identity makes the two ambient Levi embeddings equal. -/
theorem leviEmbedding_leviRefinementEquiv (m : B.Levi R) :
    D.leviEmbedding R (leviRefinementEquiv B D S e hs R m).val =
      B.leviEmbedding R m := by
  apply Units.ext
  ext a b
  obtain ⟨⟨i, x⟩, rfl⟩ := D.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := D.indexEquiv.surjective b
  obtain ⟨⟨k, x⟩, rfl⟩ := (S i).indexEquiv.surjective x
  obtain ⟨⟨l, y⟩, rfl⟩ := (S j).indexEquiv.surjective y
  change D.leviEmbedding R _ (D.index i ((S i).index k x))
    (D.index j ((S j).index l y)) =
      B.leviEmbedding R m (D.index i ((S i).index k x))
        (D.index j ((S j).index l y))
  by_cases hij : i = j
  · subst j
    rw [D.leviEmbedding_apply_same, leviRefinementEquiv_val]
    by_cases hkl : k = l
    · subst l
      rw [(S i).leviEmbedding_apply_same, nestedLeviEquiv_entry, hc, hc,
        B.leviEmbedding_apply_same]
    · rw [(S i).leviEmbedding_apply_ne R _ _ _ hkl, hc, hc,
        B.leviEmbedding_apply_ne]
      exact fun he => hkl (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective he)).2)
  · rw [D.leviEmbedding_apply_ne R _ _ _ hij, hc, hc, B.leviEmbedding_apply_ne]
    exact fun he => hij (congrArg Sigma.fst (e.injective he))

include hc in
/-- Exact consecutive coordinates force earlier outer blocks to contain earlier
original blocks. -/
theorem refinementBlock_lt_of_outer_lt {i j : Fin D.length}
    (k : Fin (S i).length) (l : Fin (S j).length) (hij : i < j) :
    e ⟨i, k⟩ < e ⟨j, l⟩ := by
  let x : Fin ((S i).size k) := ⟨0, (S i).positive k⟩
  let y : Fin ((S j).size l) := ⟨0, (S j).positive l⟩
  have hxy := D.index_lt_index_of_block_lt hij ((S i).index k x) ((S j).index l y)
  rw [hc, hc] at hxy
  have hle := blockIndex_monotone B hxy.le
  rw [blockIndex_index, blockIndex_index] at hle
  exact lt_of_le_of_ne hle (fun he => (ne_of_lt hij) (congrArg Sigma.fst (e.injective he)))

include hc in
/-- Within a common outer block, the nested labels have their original order. -/
theorem refinementBlock_strictMono (i : Fin D.length) :
    StrictMono (fun k : Fin (S i).length => e ⟨i, k⟩) := by
  intro k l hkl
  let x : Fin ((S i).size k) := ⟨0, (S i).positive k⟩
  let y : Fin ((S i).size l) := ⟨0, (S i).positive l⟩
  have hxy := index_strictMono D i ((S i).index_lt_index_of_block_lt hkl x y)
  rw [hc, hc] at hxy
  have hle := blockIndex_monotone B hxy.le
  rw [blockIndex_index, blockIndex_index] at hle
  exact lt_of_le_of_ne hle (fun he => (ne_of_lt hkl)
    (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective he)).2))

include hc in
/-- Pulling back the inner parabolic through the outer projection recovers the
original actual standard parabolic. -/
theorem composedParabolic_eq_of_coordinates :
    Parabolic.composedParabolic R D S = B.parabolic R := by
  ext g
  change g ∈ Parabolic.leviPreimage R D (refinedParabolic R D S) ↔ _
  rw [Parabolic.mem_leviPreimage_iff]
  constructor
  · rintro ⟨hD, hS⟩
    rw [B.mem_parabolic_iff]
    intro a b x y hba
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨j, l⟩, rfl⟩ := e.surjective b
    let x' := Fin.cast (hs ⟨i, k⟩).symm x
    let y' := Fin.cast (hs ⟨j, l⟩).symm y
    have hx : D.index i ((S i).index k x') = B.index (e ⟨i, k⟩) x := by
      simpa [x'] using hc i k x'
    have hy : D.index j ((S j).index l y') = B.index (e ⟨j, l⟩) y := by
      simpa [y'] using hc j l y'
    rw [← hx, ← hy]
    rcases lt_trichotomy j i with hji | hji | hij
    · exact (D.mem_parabolic_iff R g).mp hD i j _ _ hji
    · subst j
      have hkl := (refinementBlock_strictMono B D S e hs hc i).lt_iff_lt.mp hba
      exact ((S i).mem_parabolic_iff R _).mp
        ((mem_refinedParabolic R D S _).mp hS i) k l x' y' hkl
    · exact False.elim ((not_lt_of_gt hba)
        (refinementBlock_lt_of_outer_lt B D S e hs hc k l hij))
  · intro hB
    have hD : g ∈ D.parabolic R := by
      rw [D.mem_parabolic_iff]
      intro i j x y hji
      obtain ⟨⟨k, x⟩, rfl⟩ := (S i).indexEquiv.surjective x
      obtain ⟨⟨l, y⟩, rfl⟩ := (S j).indexEquiv.surjective y
      change g (D.index i ((S i).index k x)) (D.index j ((S j).index l y)) = 0
      rw [hc, hc]
      exact (B.mem_parabolic_iff R g).mp hB _ _ _ _
        (refinementBlock_lt_of_outer_lt B D S e hs hc l k hji)
    refine ⟨hD, ?_⟩
    rw [mem_refinedParabolic]
    intro i
    rw [(S i).mem_parabolic_iff]
    intro k l x y hlk
    change g (D.index i ((S i).index k x)) (D.index i ((S i).index l y)) = 0
    rw [hc, hc]
    exact (B.mem_parabolic_iff R g).mp hB _ _ _ _
      (refinementBlock_strictMono B D S e hs hc i hlk)

/-- The parabolic comparison changes only the subtype membership proof. -/
def parabolicRefinementEquiv : B.parabolic R ≃* Parabolic.composedParabolic R D S where
  toFun g := ⟨g.val, by
    rw [composedParabolic_eq_of_coordinates B D S e hs R hc]
    exact g.property⟩
  invFun g := ⟨g.val, by
    rw [← composedParabolic_eq_of_coordinates B D S e hs R hc]
    exact g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem parabolicRefinementEquiv_val (g : B.parabolic R) :
    (parabolicRefinementEquiv B D S e hs R hc g).val = g.val := rfl

/-- The same identification is continuous for the actual subgroup topologies. -/
def parabolicRefinementEquivContinuous [TopologicalSpace R] [IsTopologicalRing R] :
    B.parabolic R ≃ₜ* Parabolic.composedParabolic R D S where
  toMulEquiv := parabolicRefinementEquiv B D S e hs R hc
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

include hc in
/-- Extracting the nested diagonal blocks agrees with extracting the original
blocks, under the actual Levi and parabolic identifications. -/
theorem composedLeviProjection_parabolicRefinementEquiv (g : B.parabolic R) :
    Parabolic.composedLeviProjection R D S
      (parabolicRefinementEquiv B D S e hs R hc g) =
        leviRefinementEquiv B D S e hs R (B.leviProjection R g) := by
  apply (refinedLeviEquiv R D S).symm.injective
  change (refinedLeviEquiv R D S).symm
    (refinedLeviEquiv R D S
      (fun i => (S i).leviProjection R (refinedParabolicEval R D S i
        (Parabolic.preimageProjection R D (refinedParabolic R D S)
          (parabolicRefinementEquiv B D S e hs R hc g))))) =
    (refinedLeviEquiv R D S).symm
      (refinedLeviEquiv R D S (nestedLeviEquiv B D S e hs R (B.leviProjection R g)))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  funext i k
  apply Units.ext
  ext x y
  change g.val (D.index i ((S i).index k x)) (D.index i ((S i).index k y)) =
    nestedLeviEquiv B D S e hs R (B.leviProjection R g) i k x y
  rw [nestedLeviEquiv_entry, B.leviProjection_apply, hc, hc]

end Langlands.GeneralLinear.BlockShape
