import Langlands.GroupScheme.Rational.PathMergedRootScalars
import Langlands.GroupScheme.Rational.PathRootDeterminants

/-! # Supplied merged reflections on normalized path lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}

/-- A supplied representative for any root transports the actual representation weights. -/
theorem ReflectionRepresentative.rationalMatrix_mem_representationWeightSpace
    {r : p.rootIndex} (n : p.ReflectionRepresentative r)
    (ρ : MatrixRepresentation G d) (lam : characterLattice p.torus)
    {v : d → k} (hv : v ∈ p.representationWeightSpace ρ lam) :
    (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ v ∈
      p.representationWeightSpace ρ (p.rootDatum.reflection r lam) := by
  let := p.isSplitTorus.isAffineHom
  have h := ρ.rationalMatrix_mem_characterSpace p.inclusion n.normalizes lam hv
  change (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ v ∈
    (ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm (p.rootDatum.reflection r lam))
  simpa only [n.characterAut_eq] using h

variable {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- A reflection matrix interchanging two endpoint lines with supplied scalars. -/
def pathEndpointReflectionMatrix (i l : Fin (L + 1)) (a b : k) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  fun s t => if t = i then a * (if s = l then 1 else 0)
    else if t = l then b * (if s = i then 1 else 0)
    else if s = t then 1 else 0

/-- The determinant of a scaled endpoint transposition is minus the scalar product. -/
theorem det_pathEndpointReflectionMatrix (i l : Fin (L + 1)) (hil : i ≠ l)
    (a b : k) :
    (pathEndpointReflectionMatrix i l a b).det = -(a * b) := by
  have he : pathEndpointReflectionMatrix i l a b =
      (Matrix.diagonal (fun j => (if j = i then a else 1) *
        (if j = l then b else 1))).submatrix (Equiv.swap i l) id := by
    ext s t
    by_cases hs : s = i
    · subst s
      by_cases ht : t = i <;> by_cases ht' : t = l <;>
        simp_all [pathEndpointReflectionMatrix, eq_comm]
    · by_cases hs' : s = l
      · subst s
        by_cases ht : t = i <;> by_cases ht' : t = l <;>
          simp_all [pathEndpointReflectionMatrix, Matrix.diagonal_apply, eq_comm]
      · rw [Matrix.submatrix_apply, Equiv.swap_apply_of_ne_of_ne hs hs']
        by_cases ht : t = i <;> by_cases ht' : t = l <;>
          simp_all [pathEndpointReflectionMatrix, Matrix.diagonal_apply, eq_comm]
  rw [he, Matrix.det_permute, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp [Equiv.Perm.sign_swap hil]

include hβ in
/-- The merged root is the reflection of the second adjacent root in the first. -/
theorem adjacentRoot_eq_reflectionPerm {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    r = p.rootDatum.reflectionPerm (β ⟨i, by omega⟩ : p.rootIndex)
      (β ⟨i + 1, by omega⟩ : p.rootIndex) := by
  apply p.rootDatum.root.injective
  rw [hr, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    pairing_path_succ hβ hi, neg_one_smul, sub_neg_eq_add, add_comm]

include hβ hlam in
/-- The reflection in an adjacent merged root sends its first endpoint weight to the last. -/
theorem reflection_adjacentRoot_pathWeight_left {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    p.rootDatum.reflection r (pathWeight β lam i) = pathWeight β lam (i + 2) := by
  rw [adjacentRoot_eq_reflectionPerm hβ hi hr, RootPairing.reflection_reflectionPerm,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    reflection_pathWeight_self hβ hlam (by omega : i < L)]
  rw [reflection_pathWeight_self hβ hlam (by omega : i + 1 < L)]
  rw [reflection_apply_eq, pairing_pathWeight hβ hlam hi]
  simp

include hβ hlam in
/-- The same reflection sends its last endpoint weight to the first. -/
theorem reflection_adjacentRoot_pathWeight_right {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    p.rootDatum.reflection r (pathWeight β lam (i + 2)) = pathWeight β lam i := by
  rw [← reflection_adjacentRoot_pathWeight_left hβ hlam hi hr,
    RootPairing.reflection_same]

include hv₀ in
/-- The endpoint columns of any supplied adjacent merged reflection are scalar multiples
of the opposite normalized endpoint vectors. -/
theorem exists_adjacentReflection_endpoint_scalars {i : ℕ} (hi : i + 2 ≤ L)
    {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex))
    (n : p.ReflectionRepresentative r) :
    ∃ a b : k,
      (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ
          (normalizedPathVector hρ hβ hlam x v₀ i : d → k) =
        a • (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) ∧
      (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ
          (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
        b • (normalizedPathVector hρ hβ hlam x v₀ i : d → k) := by
  have hleft := n.rationalMatrix_mem_representationWeightSpace ρ (pathWeight β lam i)
    (normalizedPathVector hρ hβ hlam x v₀ i).2
  rw [reflection_adjacentRoot_pathWeight_left hβ hlam hi hr] at hleft
  have hright := n.rationalMatrix_mem_representationWeightSpace ρ
    (pathWeight β lam (i + 2)) (normalizedPathVector hρ hβ hlam x v₀ (i + 2)).2
  rw [reflection_adjacentRoot_pathWeight_right hβ hlam hi hr] at hright
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (finrank_pathWeightSpace hρ hβ hlam hi)
    (x := normalizedPathVector hρ hβ hlam x v₀ (i + 2))
    (fun he => normalizedPathVector_ne_zero hρ hβ hlam x v₀ hv₀ hi
      (congrArg Subtype.val he)) ⟨_, hleft⟩
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_pathWeightSpace hρ hβ hlam (by omega : i ≤ L))
    (x := normalizedPathVector hρ hβ hlam x v₀ i)
    (fun he => normalizedPathVector_ne_zero hρ hβ hlam x v₀ hv₀ (by omega : i ≤ L)
      (congrArg Subtype.val he)) ⟨_, hright⟩
  exact ⟨a, b, (congrArg Subtype.val ha).symm, (congrArg Subtype.val hb).symm⟩

/-- For a representative generated by the two root groups, every other column is fixed. -/
theorem normalizedPathMatrix_adjacentReflection_of_endpoint_scalars
    {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex))
    (n : p.ReflectionRepresentative r)
    (hn : n.point ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _)))
    (a b : k)
    (ha : (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ i : d → k) =
      a • (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k))
    (hb : (ρ.rationalMatrix n.point : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
      b • (normalizedPathVector hρ hβ hlam x v₀ i : d → k)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ n.point =
      pathEndpointReflectionMatrix ⟨i, by omega⟩ ⟨i + 2, by omega⟩ a b := by
  ext s t
  rw [normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀]
  by_cases ht : t = ⟨i, by omega⟩
  · subst t
    rw [ha, ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ ⟨i + 2, by omega⟩]
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
    simp [pathEndpointReflectionMatrix, eq_comm]
  · by_cases ht' : t = ⟨i + 2, by omega⟩
    · subst t
      rw [hb, ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ ⟨i, by omega⟩]
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
      simp [pathEndpointReflectionMatrix, ht, eq_comm]
    · rw [rootSup_pathRoot_fixes hρ hβ hlam r (by omega : i < i + 2) hi
        (adjacentRoot_eq_pathWeight_sub hi hr) (by omega : (t : ℕ) ≤ L)
        (fun h => ht (Fin.ext h)) (fun h => ht' (Fin.ext h))
        (normalizedPathVector hρ hβ hlam x v₀ t).2 hn,
        ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ t,
        Module.Basis.repr_self_apply]
      simp [pathEndpointReflectionMatrix, ht, ht', eq_comm]

/-- A supplied generated merged reflection has endpoint scalar product minus one. -/
theorem exists_normalizedPathMatrix_adjacentReflection
    {i : ℕ} (hi : i + 2 ≤ L) {r : p.rootIndex}
    (hr : p.rootDatum.root r = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex))
    (n : p.ReflectionRepresentative r)
    (hn : n.point ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _))) :
    ∃ a b : k, a * b = -1 ∧
      normalizedPathMatrix hρ hβ hlam x v₀ hv₀ n.point =
        pathEndpointReflectionMatrix ⟨i, by omega⟩ ⟨i + 2, by omega⟩ a b := by
  obtain ⟨a, b, ha, hb⟩ :=
    exists_adjacentReflection_endpoint_scalars hρ hβ hlam x v₀ hv₀ hi hr n
  have hm := normalizedPathMatrix_adjacentReflection_of_endpoint_scalars
    hρ hβ hlam x v₀ hv₀ hi hr n hn a b ha hb
  have hd := normalizedPathMatrix_det_eq_one_of_mem_rootSup hρ hβ hlam x v₀ hv₀
    r ⟨i, by omega⟩ ⟨i + 2, by omega⟩ (by change i < i + 2; omega)
    (adjacentRoot_eq_pathWeight_sub hi hr) hn
  rw [hm, det_pathEndpointReflectionMatrix _ _
    (by intro h; have := congrArg Fin.val h; dsimp at this; omega)] at hd
  exact ⟨a, b, (neg_eq_iff_eq_neg.mp hd), hm⟩

end Langlands.GroupScheme.SplitPinning
