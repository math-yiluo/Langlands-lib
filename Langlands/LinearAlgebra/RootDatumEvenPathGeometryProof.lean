import Langlands.LinearAlgebra.RootDatumEvenPathGeometryStatement
import Langlands.LinearAlgebra.RootDatumPairedPaths

/-! # Proof of the stable even-path geometry statement -/

noncomputable section

universe u v w z

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumEvenPathGeometryProof

open RootDatumOrbitPairs RootDatumReversedPath RootDatumPathWeights RootDatumPairedPaths
  RootDatumEvenPathGeometry
open Langlands.GroupScheme.SplitPinning (middleDistance)

variable {I : Type u} [Finite I] {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  {P : RootDatum I M N} {b : P.Base} {Γ : Type z} [Group Γ] {ρ : Γ →* Equiv.Perm b.support}
  (hρ : IsPairingCompatible b ρ)

/-! ### The even path family of the pairs -/

/-- The paths of the pairs of non-orthogonal simple roots in one orbit, one path for each
pair, with the pair in the middle. -/
def pairFamily : EvenPathFamily b (PairIndex ρ) where
  half := half hρ
  path := path hρ
  isPathComponent := isPathComponent_path hρ
  disjoint := path_disjoint hρ

theorem pairFamily_middleLeft (c : PairIndex ρ) : (pairFamily hρ).middleLeft c = c.1 :=
  path_left hρ c

theorem pairFamily_middleRight (c : PairIndex ρ) :
    (pairFamily hρ).middleRight c = partner ρ c.1 :=
  path_right hρ c

/-- A simple root avoids all middle pairs exactly when it is not paired. -/
theorem mem_rest_iff (a : b.support) :
    (∀ c, a ≠ (pairFamily hρ).middleLeft c ∧ a ≠ (pairFamily hρ).middleRight c) ↔
      ¬ IsPaired ρ a := by
  rw [isPaired_iff_exists hρ a]
  simp only [pairFamily_middleLeft, pairFamily_middleRight, not_exists, not_or]

theorem not_isPaired_rest (a : (pairFamily hρ).Rest) : ¬ IsPaired ρ a.val :=
  (mem_rest_iff hρ a.val).1 a.2

/-! ### The action on the paths -/

/-- The action of the group on the pairs, as a homomorphism to permutations. -/
def pairPerm : Γ →* Equiv.Perm (PairIndex ρ) :=
  @MulAction.toPermHom Γ (PairIndex ρ) _ (pairAction hρ)

theorem pairPerm_apply (γ : Γ) (c : PairIndex ρ) : pairPerm hρ γ c = pairSMul hρ γ c :=
  rfl

theorem isPathComponent_apply (σ : Γ) (c : PairIndex ρ) :
    IsPathComponent (fun j => ρ σ (path hρ c j)) :=
  (isPathComponent_path hρ c).comp_perm (ρ σ) (fun u v => hρ.pairing_apply σ u v)

/-- The image path shares a vertex with the path of the image pair. -/
theorem exists_shared (σ : Γ) (c : PairIndex ρ) :
    ∃ i' : Fin (2 * half hρ (pairSMul hρ σ c)),
      path hρ (pairSMul hρ σ c) i' =
        (fun j => ρ σ (path hρ c j)) ⟨0, by have := half_pos hρ c; omega⟩ := by
  obtain ⟨i', hi', -⟩ := exists_path_smul hρ σ c ⟨0, by have := half_pos hρ c; omega⟩
  exact ⟨i', hi'⟩

theorem half_pairSMul (σ : Γ) (c : PairIndex ρ) :
    half hρ (pairSMul hρ σ c) = half hρ c := by
  obtain ⟨i', hi'⟩ := exists_shared hρ σ c
  have := (isPathComponent_path hρ (pairSMul hρ σ c)).length_eq
    (isPathComponent_apply hρ σ c) hi'
  omega

/-- A group element maps each path in order or in reverse order onto the path of the image
pair. -/
theorem path_pairSMul (σ : Γ) (c : PairIndex ρ) :
    ∃ reverse : Bool, ∀ i : Fin (2 * half hρ c),
      ρ σ (path hρ c i) = path hρ (pairSMul hρ σ c)
        (Fin.cast (congrArg (fun m => 2 * m) (half_pairSMul hρ σ c)).symm
          (if reverse then i.rev else i)) := by
  obtain ⟨i', hi'⟩ := exists_shared hρ σ c
  obtain ⟨-, hrel | hrel⟩ :=
    (isPathComponent_path hρ (pairSMul hρ σ c)).eq_or_eq_rev (isPathComponent_apply hρ σ c) hi'
  · refine ⟨false, fun i => (hrel i).trans ?_⟩
    rfl
  · refine ⟨true, fun i => (hrel i).trans ?_⟩
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_cast, ↓reduceIte]
    have := half_pairSMul hρ σ c
    omega

/-- The compatible action on the pair paths. -/
def compatibleAction : (pairFamily hρ).CompatibleAction ρ where
  action := pairPerm hρ
  half_eq := half_pairSMul hρ
  path_eq := path_pairSMul hρ

/-! ### Orbits of the remaining roots -/

/-- The action on remaining roots. -/
def restSMul (γ : Γ) (a : (pairFamily hρ).Rest) : (pairFamily hρ).Rest :=
  ⟨ρ γ a.val, (mem_rest_iff hρ _).2 fun h =>
    not_isPaired_rest hρ a ((isPaired_apply_iff hρ γ).1 h)⟩

@[simp] theorem restSMul_val (γ : Γ) (a : (pairFamily hρ).Rest) :
    (restSMul hρ γ a).val = ρ γ a.val :=
  rfl

open Classical in
/-- The orbit of a remaining root, as a finite set of remaining roots. -/
def restOrbit (a : (pairFamily hρ).Rest) : Finset (pairFamily hρ).Rest :=
  Finset.univ.filter fun a' => ∃ γ : Γ, ρ γ a.val = a'.val

theorem mem_restOrbit {a a' : (pairFamily hρ).Rest} :
    a' ∈ restOrbit hρ a ↔ ∃ γ : Γ, ρ γ a.val = a'.val := by
  classical
  simp [restOrbit]

theorem self_mem_restOrbit (a : (pairFamily hρ).Rest) : a ∈ restOrbit hρ a :=
  (mem_restOrbit hρ).2 ⟨1, by simp⟩

theorem restSMul_mem_restOrbit {a a' : (pairFamily hρ).Rest} (h : a' ∈ restOrbit hρ a)
    (γ : Γ) : restSMul hρ γ a' ∈ restOrbit hρ a := by
  obtain ⟨δ, hδ⟩ := (mem_restOrbit hρ).1 h
  refine (mem_restOrbit hρ).2 ⟨γ * δ, ?_⟩
  rw [restSMul_val, ← hδ, map_mul, Equiv.Perm.mul_apply]

theorem exists_apply_of_mem_restOrbit {a a₁ a₂ : (pairFamily hρ).Rest}
    (h₁ : a₁ ∈ restOrbit hρ a) (h₂ : a₂ ∈ restOrbit hρ a) :
    ∃ γ : Γ, ρ γ a₁.val = a₂.val := by
  obtain ⟨γ, hγ⟩ := (mem_restOrbit hρ).1 h₁
  obtain ⟨δ, hδ⟩ := (mem_restOrbit hρ).1 h₂
  refine ⟨δ * γ⁻¹, ?_⟩
  rw [← hγ, ← hδ]
  rw [map_mul, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply (ρ γ⁻¹), ← map_mul,
    inv_mul_cancel, map_one, Equiv.Perm.one_apply]

theorem restOrbit_eq_of_mem {a a' : (pairFamily hρ).Rest} (h : a' ∈ restOrbit hρ a) :
    restOrbit hρ a' = restOrbit hρ a := by
  ext x
  constructor
  · intro hx
    obtain ⟨γ, hγ⟩ := (mem_restOrbit hρ).1 hx
    have := restSMul_mem_restOrbit hρ h γ
    have hx' : restSMul hρ γ a' = x := Subtype.ext hγ
    rwa [hx'] at this
  · intro hx
    exact (mem_restOrbit hρ).2 (exists_apply_of_mem_restOrbit hρ h hx)

theorem level_eq_of_mem_restOrbit {a a' : (pairFamily hρ).Rest} (h : a' ∈ restOrbit hρ a) :
    level hρ a'.val = level hρ a.val := by
  obtain ⟨γ, hγ⟩ := (mem_restOrbit hρ).1 h
  rw [← hγ, level_apply]

/-- Distinct remaining roots in one orbit are orthogonal. -/
theorem isOrthogonal_of_mem_restOrbit {a a₁ a₂ : (pairFamily hρ).Rest}
    (h₁ : a₁ ∈ restOrbit hρ a) (h₂ : a₂ ∈ restOrbit hρ a) (hne : a₁ ≠ a₂) :
    P.IsOrthogonal (a₁.val : I) (a₂.val : I) := by
  obtain ⟨γ, hγ⟩ := exists_apply_of_mem_restOrbit hρ h₁ h₂
  have hγ' : ρ γ a₁.val ≠ a₁.val := by
    rw [hγ]
    exact fun h => hne (Subtype.ext h).symm
  have := not_isOrthogonal_of_not_isPaired (not_isPaired_rest hρ a₁) γ hγ'
  rwa [hγ] at this

/-! ### The ordered orbit blocks -/

open Classical in
/-- The orbits of the remaining roots. -/
def restOrbits : Finset (Finset (pairFamily hρ).Rest) :=
  Finset.univ.image (restOrbit hρ)

/-- The level of an orbit: the common distance of its members from their middle pairs. -/
def orbitLevel (O : Finset (pairFamily hρ).Rest) : ℕ :=
  O.sup fun a => level hρ a.val

theorem orbitLevel_restOrbit (a : (pairFamily hρ).Rest) :
    orbitLevel hρ (restOrbit hρ a) = level hρ a.val :=
  le_antisymm (Finset.sup_le fun _ ha' => (level_eq_of_mem_restOrbit hρ ha').le)
    (Finset.le_sup (f := fun a => level hρ a.val) (self_mem_restOrbit hρ a))

theorem exists_eq_restOrbit {O : Finset (pairFamily hρ).Rest} (hO : O ∈ restOrbits hρ) :
    ∃ a, restOrbit hρ a = O := by
  classical
  simpa [restOrbits] using hO

theorem level_eq_orbitLevel {O : Finset (pairFamily hρ).Rest} (hO : O ∈ restOrbits hρ)
    {a : (pairFamily hρ).Rest} (ha : a ∈ O) : level hρ a.val = orbitLevel hρ O := by
  obtain ⟨x, rfl⟩ := exists_eq_restOrbit hρ hO
  rw [orbitLevel_restOrbit, level_eq_of_mem_restOrbit hρ ha]

/-- The orbits, sorted by increasing level. -/
def sortedOrbits : List (Finset (pairFamily hρ).Rest) :=
  (restOrbits hρ).toList.mergeSort fun O O' => decide (orbitLevel hρ O ≤ orbitLevel hρ O')

theorem mem_sortedOrbits {O : Finset (pairFamily hρ).Rest} :
    O ∈ sortedOrbits hρ ↔ O ∈ restOrbits hρ := by
  rw [sortedOrbits, (List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]

theorem nodup_sortedOrbits : (sortedOrbits hρ).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem pairwise_sortedOrbits :
    (sortedOrbits hρ).Pairwise fun O O' => orbitLevel hρ O ≤ orbitLevel hρ O' := by
  have h := List.pairwise_mergeSort
    (le := fun O O' => decide (orbitLevel hρ O ≤ orbitLevel hρ O'))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (restOrbits hρ).toList
  exact h.imp fun h' => by simpa using h'

/-- The orbit blocks, in order of increasing level. -/
def orbitBlocks : List (List (pairFamily hρ).Rest) :=
  (sortedOrbits hρ).map Finset.toList

theorem exists_of_mem_orbitBlocks {l : List (pairFamily hρ).Rest} (hl : l ∈ orbitBlocks hρ) :
    ∃ a, l = (restOrbit hρ a).toList := by
  obtain ⟨O, hO, rfl⟩ := List.mem_map.1 hl
  obtain ⟨a, rfl⟩ := exists_eq_restOrbit hρ ((mem_sortedOrbits hρ).1 hO)
  exact ⟨a, rfl⟩

/-- The enumeration of the remaining roots block by block. -/
def flatOrbits : List (pairFamily hρ).Rest := (orbitBlocks hρ).flatten

theorem nodup_flatOrbits : (flatOrbits hρ).Nodup := by
  rw [flatOrbits, List.nodup_flatten]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨O, -, rfl⟩ := List.mem_map.1 hl
    exact Finset.nodup_toList O
  · rw [orbitBlocks, List.pairwise_map]
    refine (nodup_sortedOrbits hρ).pairwise_of_forall_ne fun O hO O' hO' hne x hx hx' => ?_
    obtain ⟨a, rfl⟩ := exists_eq_restOrbit hρ ((mem_sortedOrbits hρ).1 hO)
    obtain ⟨a', rfl⟩ := exists_eq_restOrbit hρ ((mem_sortedOrbits hρ).1 hO')
    rw [Finset.mem_toList] at hx hx'
    exact hne ((restOrbit_eq_of_mem hρ hx).symm.trans (restOrbit_eq_of_mem hρ hx'))

theorem mem_flatOrbits (a : (pairFamily hρ).Rest) : a ∈ flatOrbits hρ := by
  classical
  rw [flatOrbits, List.mem_flatten]
  refine ⟨(restOrbit hρ a).toList, List.mem_map.2 ⟨restOrbit hρ a, ?_, rfl⟩, ?_⟩
  · rw [mem_sortedOrbits, restOrbits]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  · rw [Finset.mem_toList]
    exact self_mem_restOrbit hρ a

theorem pairwise_level_flatOrbits :
    (flatOrbits hρ).Pairwise fun a a' => level hρ a.val ≤ level hρ a'.val := by
  rw [flatOrbits, List.pairwise_flatten]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := exists_of_mem_orbitBlocks hρ hl
    refine (Finset.nodup_toList _).pairwise_of_forall_ne fun a ha a' ha' _ => ?_
    rw [Finset.mem_toList] at ha ha'
    rw [level_eq_of_mem_restOrbit hρ ha, level_eq_of_mem_restOrbit hρ ha']
  · rw [orbitBlocks, List.pairwise_map]
    refine (pairwise_sortedOrbits hρ).imp_of_mem fun hO hO' hle x hx y hy => ?_
    rw [Finset.mem_toList] at hx hy
    rw [level_eq_orbitLevel hρ ((mem_sortedOrbits hρ).1 hO) hx,
      level_eq_orbitLevel hρ ((mem_sortedOrbits hρ).1 hO') hy]
    exact hle

theorem level_get_le {j j' : Fin (flatOrbits hρ).length} (h : j' ≤ j) :
    level hρ ((flatOrbits hρ).get j').val ≤ level hρ ((flatOrbits hρ).get j).val := by
  rcases h.lt_or_eq with h | h
  · exact List.pairwise_iff_getElem.1 (pairwise_level_flatOrbits hρ) j' j j'.2 j.2 h
  · rw [h]

open Classical in
/-- The enumeration of the remaining roots. -/
def restOrder : Fin (flatOrbits hρ).length ≃ (pairFamily hρ).Rest :=
  List.Nodup.getEquivOfForallMemList (flatOrbits hρ) (nodup_flatOrbits hρ) (mem_flatOrbits hρ)

theorem restOrder_apply (j : Fin (flatOrbits hρ).length) :
    restOrder hρ j = (flatOrbits hρ).get j :=
  rfl

theorem isMiddleOut_restOrder : (pairFamily hρ).IsMiddleOut (restOrder hρ) := by
  intro c i i' j j' hj hj' hlt
  by_contra hjj
  have hle := level_get_le hρ (not_lt.1 hjj)
  rw [← restOrder_apply, ← restOrder_apply, hj, hj'] at hle
  have e1 : level hρ ((pairFamily hρ).path c i) = middleDistance ((pairFamily hρ).half c) i :=
    level_path hρ c i
  have e2 : level hρ ((pairFamily hρ).path c i') =
      middleDistance ((pairFamily hρ).half c) i' :=
    level_path hρ c i'
  omega

theorem invariant_orbitBlocks (γ : Γ) (l : List (pairFamily hρ).Rest)
    (hl : l ∈ orbitBlocks hρ) :
    (l.map fun a => ρ γ a.val).Perm (l.map Subtype.val) := by
  obtain ⟨x, rfl⟩ := exists_of_mem_orbitBlocks hρ hl
  have hinj : Injective fun a : (pairFamily hρ).Rest => ρ γ a.val :=
    (ρ γ).injective.comp Subtype.val_injective
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map hinj)
    ((Finset.nodup_toList _).map Subtype.val_injective)]
  intro y
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨restSMul hρ γ a, restSMul_mem_restOrbit hρ ha γ, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨restSMul hρ γ⁻¹ a, restSMul_mem_restOrbit hρ ha γ⁻¹, ?_⟩
    rw [restSMul_val, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]

/-- The middle-out ordering of the remaining roots in orbit blocks. -/
def orbitOrdering : (pairFamily hρ).OrbitOrdering ρ where
  length := (flatOrbits hρ).length
  order := restOrder hρ
  middleOut := isMiddleOut_restOrder hρ
  blocks := orbitBlocks hρ
  flatten_eq := (List.ofFn_get (flatOrbits hρ)).symm
  invariant := invariant_orbitBlocks hρ
  same_orbit := fun l hl a a' ha ha' => by
    obtain ⟨x, rfl⟩ := exists_of_mem_orbitBlocks hρ hl
    rw [Finset.mem_toList] at ha ha'
    exact exists_apply_of_mem_restOrbit hρ ha ha'
  pairwise := fun l hl => by
    obtain ⟨x, rfl⟩ := exists_of_mem_orbitBlocks hρ hl
    refine (Finset.nodup_toList _).pairwise_of_forall_ne fun a ha a' ha' hne => ⟨hne, ?_⟩
    rw [Finset.mem_toList] at ha ha'
    exact isOrthogonal_of_mem_restOrbit hρ ha ha' hne

end Langlands.LinearAlgebra.RootDatumEvenPathGeometryProof

namespace Langlands.LinearAlgebra

open RootDatumEvenPathGeometryProof

/-- **Stable even-path geometry.** A pairing-compatible simple-root action admits disjoint
even path components preserved up to reversal and a middle-out orthogonal orbit-block
ordering of the remaining simple roots. -/
theorem evenPathOrbitGeometry : EvenPathOrbitGeometryStatement.{u, v, w, z} := by
  intro I _ M N _ _ P b Γ _ ρ hρ
  exact ⟨RootDatumPairedPaths.PairIndex ρ, Fintype.ofFinite _, pairFamily hρ,
    ⟨compatibleAction hρ⟩, ⟨orbitOrdering hρ⟩⟩

end Langlands.LinearAlgebra
