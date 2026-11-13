import Langlands.GroupScheme.Rational.PathCorootMatrices
import Langlands.GroupScheme.Rational.EvenChainLocality
import Langlands.LinearAlgebra.PathCoxeterProducts

/-! # Characteristic polynomials of pattern and ordinary products on path representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights Langlands.LinearAlgebra.PathCoxeter

/-! ### Path matrices as matrices of the path Coxeter modules -/

section Matrices

variable {k : Type u} [Field k] {L : ℕ}

theorem pathSimpleFactorMatrix_eq_sfac (i : Fin L) (c : k) :
    pathSimpleFactorMatrix i c = sfac (L + 1) i c := by
  ext a b
  simp only [pathSimpleFactorMatrix, pathReflectionMatrix, sfac, Matrix.sub_apply,
    Matrix.single_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | ring

theorem pathEndpointReflectionMatrix_eq_endpointMat (i l : Fin (L + 1)) (a b : k) :
    pathEndpointReflectionMatrix i l a b = endpointMat (L + 1) i l a b := by
  ext s t
  simp only [pathEndpointReflectionMatrix, endpointMat, Fin.ext_iff]
  split_ifs <;> simp

theorem adjacentCorootMatrix_eq_torusMat (i : ℕ) (t : kˣ) :
    adjacentCorootMatrix L i t = torusMat (L + 1) i (t : k) ((t⁻¹ : kˣ) : k) :=
  rfl

end Matrices

/-! ### Positions on a path -/

section PathIndex

variable {Ω : Type*} {L : ℕ}

open Classical in
/-- The position of a vertex on a path, or `none` if the vertex is not on the path. -/
def pathIndex (β : Fin L → Ω) (w : Ω) : Option ℕ :=
  if h : ∃ v, β v = w then some (Classical.choose h).val else none

theorem pathIndex_apply {β : Fin L → Ω} (hβ : Function.Injective β) (v : Fin L) :
    pathIndex β (β v) = some (v : ℕ) := by
  have h : ∃ v', β v' = β v := ⟨v, rfl⟩
  rw [pathIndex, dite_eq_left h, hβ (Classical.choose_spec h)]

theorem pathIndex_eq_none {β : Fin L → Ω} {w : Ω} (hw : w ∉ Set.range β) :
    pathIndex β w = none := by
  have hw' : ¬∃ v, β v = w := fun ⟨v, hv⟩ => hw ⟨v, hv⟩
  rw [pathIndex, dite_eq_right hw']

theorem exists_of_pathIndex_eq_some {β : Fin L → Ω} {w : Ω} {v : ℕ}
    (h : pathIndex β w = some v) : ∃ hv : v < L, β ⟨v, hv⟩ = w := by
  unfold pathIndex at h
  split_ifs at h with hw
  · obtain rfl := Option.some_injective _ h
    exact ⟨(Classical.choose hw).2, Classical.choose_spec hw⟩

end PathIndex

/-! ### Factors on the normalized path lines -/

section Factors

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {V : Type} [Fintype V] [DecidableEq V] {ρ : MatrixRepresentation G V}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- A point acting trivially in the representation has the identity path matrix. -/
theorem normalizedPathMatrix_eq_one {g : rationalPoints G} (hg : ρ.rationalMatrix g = 1) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ g = 1 := by
  simp [normalizedPathMatrix, hg]

/-- The path matrix of a simple-root factor `x_w(c) n_w`: the simple factor on the lines `v`,
`v + 1` if `w` is the path vertex `v`, and the identity if `w` is off the path. -/
theorem normalizedPathMatrix_rootFactor (w : p.base.support) (c : k) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀
        ((x w).toRootParametrization.rationalPoint c *
          (canonicalSimpleReflectionRepresentatives x w).point) =
      (pathIndex β w).elim 1 fun v => sfac (L + 1) v c := by
  by_cases hw : w ∈ Set.range β
  · obtain ⟨v, rfl⟩ := hw
    rw [pathIndex_apply hβ.injective]
    exact (normalizedPathMatrix_simpleFactor hρ hβ hlam x v₀ hv₀ v c).trans
      (pathSimpleFactorMatrix_eq_sfac v c)
  · rw [pathIndex_eq_none hw]
    refine normalizedPathMatrix_eq_one hρ hβ hlam x v₀ hv₀
      (rationalMatrix_rootFactor_eq_one x ρ hρ.2.1 (fun ξ hξ => ?_) c)
    obtain ⟨j, -, rfl⟩ := exists_eq_pathWeight_of_isHighestWeight hρ hβ hlam hξ
    exact pairing_pathWeight_of_not_mem hβ hlam hw j

/-- **The merged blocks on the path lines.** Let the merged simple roots of `D` be the path
vertices `i` and `i + 1`. There are scalars `a b` with `a b = -1` such that
`u_b u_a x_α(s) n_α α^∨(t)` and `x_α(s) n_α` act on the lines `i, i+1, i+2` by the blocks
`blockBeta t t⁻¹ a b (s λ) c_a c_b` and `blockBeta 1 1 a b (s λ) 0 0`, where `λ` is the
coefficient of the supplied root map of `α` between the lines `i` and `i + 2`. -/
theorem exists_normalizedPathMatrix_block (D : p.SteinbergModifiedData) {i : ℕ}
    (hi : i + 2 ≤ L) (ha : D.a = β ⟨i, by omega⟩) (hb : D.b = β ⟨i + 1, by omega⟩)
    (hn : D.nAlpha.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root D.alpha)).carrier (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root D.alpha)).carrier
        (Over.mk (𝟙 _))) :
    ∃ a b : k, a * b = -1 ∧
      (∀ (s : k) (t : kˣ), normalizedPathMatrix hρ hβ hlam x v₀ hv₀
          (D.ub x * D.ua x * D.xAlpha.rationalPoint s * D.nAlpha.point *
            corootRationalPoint p D.alpha t) =
        core (L + 1) i (blockBeta (t : k) ((t⁻¹ : kˣ) : k) a b
          (s * pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨i, by omega⟩ ⟨i + 2, by omega⟩)
          D.ca D.cb)) ∧
      ∀ s : k, normalizedPathMatrix hρ hβ hlam x v₀ hv₀
          (D.xAlpha.rationalPoint s * D.nAlpha.point) =
        core (L + 1) i (blockBeta 1 1 a b
          (s * pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨i, by omega⟩ ⟨i + 2, by omega⟩)
          0 0) := by
  have hr : p.rootDatum.root D.alpha = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex) := by
    rw [D.root_eq, ha, hb]
  obtain ⟨a, b, hab, hN⟩ :=
    exists_normalizedPathMatrix_adjacentReflection hρ hβ hlam x v₀ hv₀ hi hr D.nAlpha hn
  have hX : ∀ s : k, normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (D.xAlpha.rationalPoint s) =
      1 + Matrix.single (⟨i, by omega⟩ : Fin (L + 1)) ⟨i + 2, by omega⟩
        (s * pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨i, by omega⟩ ⟨i + 2, by omega⟩) :=
    fun s => normalizedPathMatrix_pathRoot hρ hβ hlam x v₀ hv₀ D.xAlpha
      (⟨i, by omega⟩ : Fin (L + 1)) ⟨i + 2, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
      (adjacentRoot_eq_pathWeight_sub (lam := lam) hi hr) s
  refine ⟨a, b, hab, fun s t => ?_, fun s => ?_⟩
  · have hua : normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (D.ua x) =
        1 + Matrix.single (⟨i, by omega⟩ : Fin (L + 1)) ⟨i + 1, by omega⟩ D.ca := by
      unfold SteinbergModifiedData.ua
      rw [ha]
      exact normalizedPathMatrix_rationalRoot hρ hβ hlam x v₀ hv₀ ⟨i, by omega⟩ D.ca
    have hub : normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (D.ub x) =
        1 + Matrix.single (⟨i + 1, by omega⟩ : Fin (L + 1)) ⟨i + 2, by omega⟩ D.cb := by
      unfold SteinbergModifiedData.ub
      rw [hb]
      exact normalizedPathMatrix_rationalRoot hρ hβ hlam x v₀ hv₀ ⟨i + 1, by omega⟩ D.cb
    have key := block_eq_core (R := k) (n := L + 1) (i := i) (by omega) (t : k)
      ((t⁻¹ : kˣ) : k) a b
      (s * pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨i, by omega⟩ ⟨i + 2, by omega⟩) D.ca D.cb
    rw [map_mul, map_mul, map_mul, map_mul, hua, hub, hX, hN,
      normalizedPathMatrix_corootRationalPoint_adjacent hρ hβ hlam x v₀ hv₀ hi hr t,
      pathEndpointReflectionMatrix_eq_endpointMat, adjacentCorootMatrix_eq_torusMat]
    exact key
  · have key := block_eq_core_false (R := k) (n := L + 1) (i := i) (by omega) a b
      (s * pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨i, by omega⟩ ⟨i + 2, by omega⟩)
    rw [map_mul, hX, hN, pathEndpointReflectionMatrix_eq_endpointMat]
    exact key

include hρ hβ hlam hv₀ in
/-- **Ordinary products on a path representation.** Let the path have `2m + 2` vertices. For
every ordering `E` of the simple roots, the product of the factors `x_(E j)(γ_j) n_(E j)` has the
characteristic polynomial `ordPoly m` of the coordinates read along the path. -/
theorem charpoly_rootFactorProduct {m : ℕ} (hL : L = 2 * m + 2) {r : ℕ}
    (E : Fin r ≃ p.base.support) (cf : Fin r → k) :
    (ρ.rationalMatrix (List.ofFn fun j => (x (E j)).toRootParametrization.rationalPoint (cf j) *
        (canonicalSimpleReflectionRepresentatives x (E j)).point).prod :
          Matrix V V k).charpoly =
      ordPoly m (fun v => if h : v < L then cf (E.symm (β ⟨v, h⟩)) else 0) := by
  set cf' : ℕ → k := fun v => if h : v < L then cf (E.symm (β ⟨v, h⟩)) else 0
  set M := normalizedPathMatrix hρ hβ hlam x v₀ hv₀
  have hfac : ∀ j, M ((x (E j)).toRootParametrization.rationalPoint (cf j) *
      (canonicalSimpleReflectionRepresentatives x (E j)).point) =
        (pathIndex β (E j)).elim 1 (ordY (L + 1) m cf') := by
    intro j
    rw [normalizedPathMatrix_rootFactor hρ hβ hlam x v₀ hv₀]
    rcases hj : pathIndex β (E j) with _ | v
    · rfl
    · obtain ⟨hv, hβv⟩ := exists_of_pathIndex_eq_some hj
      change sfac (L + 1) v (cf j) = ordY (L + 1) m cf' v
      have hcf : cf' v = cf j := by
        simp only [cf', dite_eq_left hv, hβv, Equiv.symm_apply_apply]
      rw [ordY, ite_eq_left (by omega), hcf]
  have hperm : ((List.finRange r).filterMap fun j => pathIndex β (E j)).Perm
      (List.range (2 * m + 2)) := by
    refine perm_range_of_nodup ((List.nodup_finRange r).filterMap ?_) fun v => ?_
    · intro j j' v hj hj'
      obtain ⟨hv, hβv⟩ := exists_of_pathIndex_eq_some (Option.mem_def.mp hj)
      obtain ⟨hv', hβv'⟩ := exists_of_pathIndex_eq_some (Option.mem_def.mp hj')
      exact E.injective (hβv.symm.trans hβv')
    · rw [List.mem_filterMap]
      constructor
      · rintro ⟨j, -, hj⟩
        obtain ⟨hv, -⟩ := exists_of_pathIndex_eq_some hj
        omega
      · intro hv
        refine ⟨E.symm (β ⟨v, by omega⟩), List.mem_finRange _, ?_⟩
        rw [Equiv.apply_symm_apply, pathIndex_apply hβ.injective]
  rw [← charpoly_normalizedPathMatrix hρ hβ hlam x v₀ hv₀, map_list_prod, List.ofFn_eq_map,
    List.map_map]
  rw [show ((List.finRange r).map (⇑M ∘ fun j =>
      (x (E j)).toRootParametrization.rationalPoint (cf j) *
        (canonicalSimpleReflectionRepresentatives x (E j)).point)).prod =
      (((List.finRange r).filterMap fun j => pathIndex β (E j)).map
        (ordY (L + 1) m cf')).prod from
    list_prod_map_eq_filterMap _ _ _ hfac _]
  exact charpoly_prod_ordY (by omega) cf' hperm

end Factors

/-! ### Pattern products on the representation at the end of a path -/

section EvenChain

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {J : Type u} (C : p.EvenChainData J)

namespace EvenChainData

open Classical in
/-- The coordinates of the unmerged factors read along the path `c`: at the vertex `v` of `c`
it is the coordinate `z j` of the factor with `e j = c_v`, and it is `0` at the merged vertices
and beyond the path. -/
def restCoord {q : ℕ} (e : Fin q ≃ C.Rest) (z : Fin q → k) (c : J) (v : ℕ) : k :=
  if h : v < 2 * C.half c then
    (if h' : ∀ c', C.path c ⟨v, h⟩ ≠ (C.modified c').a ∧ C.path c ⟨v, h⟩ ≠ (C.modified c').b
      then z (e.symm ⟨C.path c ⟨v, h⟩, h'⟩) else 0)
  else 0

theorem restCoord_eq {q : ℕ} (e : Fin q ≃ C.Rest) (z : Fin q → k) {c : J} {j : Fin q}
    {v : ℕ} (hv : v < 2 * C.half c) (hj : ((e j : C.Rest) : p.base.support) = C.path c ⟨v, hv⟩) :
    C.restCoord e z c v = z j := by
  have h' : ∀ c', C.path c ⟨v, hv⟩ ≠ (C.modified c').a ∧
      C.path c ⟨v, hv⟩ ≠ (C.modified c').b := hj ▸ (e j).2
  rw [restCoord, dite_eq_left hv, dite_eq_left h']
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext hj.symm

/-- The merged first vertex of the path `c` is its vertex `half c - 1`. -/
theorem modified_a_eq {c : J} {m : ℕ} (hm : C.half c = m + 1) :
    (C.modified c).a = C.path c ⟨m, by omega⟩ := by
  rw [C.modified_a]
  congr 1
  ext
  simp only
  omega

/-- The merged second vertex of the path `c` is its vertex `half c`. -/
theorem modified_b_eq {c : J} {m : ℕ} (hm : C.half c = m + 1) :
    (C.modified c).b = C.path c ⟨m + 1, by omega⟩ := by
  rw [C.modified_b]
  congr 1
  ext
  simp only
  omega

/-- A path vertex other than the merged pair is unmerged. -/
theorem path_mem_rest {c : J} {m : ℕ} (hm : C.half c = m + 1) (v : Fin (2 * C.half c))
    (h1 : (v : ℕ) ≠ m) (h2 : (v : ℕ) ≠ m + 1) (c' : J) :
    C.path c v ≠ (C.modified c').a ∧ C.path c v ≠ (C.modified c').b := by
  by_cases hc : c' = c
  · subst hc
    rw [C.modified_a_eq hm, C.modified_b_eq hm]
    constructor
    · intro h
      exact h1 (congrArg Fin.val ((C.isPathComponent c').injective h))
    · intro h
      exact h2 (congrArg Fin.val ((C.isPathComponent c').injective h))
  · constructor
    · intro h
      rw [C.modified_a] at h
      exact hc (C.disjoint c c' v _ h).symm
    · intro h
      rw [C.modified_b] at h
      exact hc (C.disjoint c c' v _ h).symm

/-- An unmerged vertex on the path `c` is not one of its merged vertices. -/
theorem ne_of_rest_eq_path {c : J} {m : ℕ} (hm : C.half c = m + 1) (w : C.Rest)
    {v : Fin (2 * C.half c)} (hv : (w : p.base.support) = C.path c v) :
    (v : ℕ) ≠ m ∧ (v : ℕ) ≠ m + 1 := by
  obtain ⟨h1, h2⟩ := w.2 c
  rw [hv, C.modified_a_eq hm] at h1
  rw [hv, C.modified_b_eq hm] at h2
  constructor
  · intro h
    exact h1 (congrArg (C.path c) (Fin.ext h))
  · intro h
    exact h2 (congrArg (C.path c) (Fin.ext h))

variable {V : Type} [Fintype V] [DecidableEq V] {ρ : MatrixRepresentation G V}
  {lam : characterLattice p.torus} (x : p.NormalizedSimpleRootParametrizations)

/-- **Pattern products on the representation at the end of a path.** Let the path `c` have
`2m + 2` vertices, and let `ρ` have highest weight the fundamental weight of its end vertex.
There are nonzero constants `A`, `B` such that, for every pattern `ε` and all coordinates, the
characteristic polynomial of the pattern product is the ordinary one `ordPoly m` at the
coordinates `patCoord m d σ δ`, where `d` reads the unmerged coordinates along the path, and
`σ = -s A`, `δ = 0` if `ε c = false`, while `σ = -t s A`, `δ = t B` if `ε c = true`. -/
theorem charpoly_patternProduct (c : J) {m : ℕ} (hm : C.half c = m + 1)
    (hρ : p.IsHighestWeight ρ lam) (hlam : IsPathFundamental (C.path c) lam)
    (v₀ : p.representationWeightSpace ρ (pathWeight (C.path c) lam 0)) (hv₀ : v₀ ≠ 0) :
    ∃ A B : k, A ≠ 0 ∧ B ≠ 0 ∧ ∀ {r q : ℕ} (o : Fin r ≃ J) (e : Fin q ≃ C.Rest)
      (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k),
      (ρ.rationalMatrix (C.patternProduct x (canonicalSimpleReflectionRepresentatives x)
          o e ε s t z) : Matrix V V k).charpoly =
        ordPoly m (patCoord m (C.restCoord e z c)
          (if ε c then -((t c : k) * s c * A) else -(s c * A))
          (if ε c then (t c : k) * B else 0)) := by
  classical
  have hβ := C.isPathComponent c
  have hi : m + 2 ≤ 2 * C.half c := by omega
  set D := C.modified c with hD
  have ha := C.modified_a_eq hm
  have hb := C.modified_b_eq hm
  have hr : p.rootDatum.root D.alpha =
      p.rootDatum.root (C.path c ⟨m, by omega⟩ : p.rootIndex) +
        p.rootDatum.root (C.path c ⟨m + 1, by omega⟩ : p.rootIndex) := by
    rw [D.root_eq, ha, hb]
  obtain ⟨a, b, hab, htrue, hfalse⟩ :=
    exists_normalizedPathMatrix_block hρ hβ hlam x v₀ hv₀ D hi ha hb (C.nAlpha_mem c)
  set lam' := pathRootScalar hρ hβ hlam x v₀ hv₀ D.xAlpha ⟨m, by omega⟩ ⟨m + 2, by omega⟩
  have hlam' : lam' ≠ 0 :=
    pathRootScalar_adjacent_ne_zero hρ hβ hlam x v₀ hv₀ hi D.xAlpha hr
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hab
    exact zero_ne_one (neg_eq_zero.mp hab.symm).symm |>.elim
  refine ⟨lam' * a, a * D.ca * D.cb, mul_ne_zero hlam' ha0,
    mul_ne_zero (mul_ne_zero ha0 D.ca_ne_zero) D.cb_ne_zero, ?_⟩
  intro r q o e ε s t z
  set M := normalizedPathMatrix hρ hβ hlam x v₀ hv₀
  set c' := C.restCoord e z c
  set β' : ℕ → ℕ → k := if ε c then
      blockBeta (t c : k) ((t c)⁻¹ : kˣ) a b (s c * lam') D.ca D.cb
    else blockBeta 1 1 a b (s c * lam') 0 0 with hβ'
  set y := patY (2 * C.half c + 1) m c' β'
  let idxB : Fin r → Option ℕ := fun j => if o j = c then some m else none
  let shift : ℕ → ℕ := fun v => if v < m then v else v - 1
  let idxR : Fin q → Option ℕ := fun j => (pathIndex (C.path c) (e j : p.base.support)).map shift
  have hblock : ∀ j, M (C.block x (o j) (ε (o j)) (s (o j)) (t (o j))) = (idxB j).elim 1 y := by
    intro j
    by_cases hj : o j = c
    · simp only [idxB, hj, ite_true, Option.elim_some]
      change _ = patY (2 * C.half c + 1) m c' β' m
      rw [patY, ite_eq_right (lt_irrefl m), ite_eq_left rfl, hβ']
      unfold EvenChainData.block
      cases ε c
      · simp only [Bool.false_eq_true, ite_false]
        exact hfalse (s c)
      · simp only [ite_true]
        exact htrue (s c) (t c)
    · simp only [idxB, hj, ite_false, Option.elim_none]
      exact normalizedPathMatrix_eq_one hρ hβ hlam x v₀ hv₀
        (C.rationalMatrix_block_eq_one_of_ne x hρ hlam hj _ _ _)
  have hrest : ∀ j, M ((x (e j).1).toRootParametrization.rationalPoint (z j) *
      (canonicalSimpleReflectionRepresentatives x (e j).1).point) = (idxR j).elim 1 y := by
    intro j
    rw [normalizedPathMatrix_rootFactor hρ hβ hlam x v₀ hv₀]
    simp only [idxR]
    rcases hj : pathIndex (C.path c) (e j : p.base.support) with _ | v
    · rfl
    · obtain ⟨hv, hβv⟩ := exists_of_pathIndex_eq_some hj
      obtain ⟨h1, h2⟩ := C.ne_of_rest_eq_path hm (e j) hβv.symm
      simp only at h1 h2
      have hc' : c' v = z j := C.restCoord_eq e z hv hβv.symm
      change sfac (2 * C.half c + 1) v (z j) = patY (2 * C.half c + 1) m c' β' (shift v)
      by_cases hvm : v < m
      · simp only [shift, ite_eq_left hvm, patY, hc']
      · simp only [shift, ite_eq_right hvm, patY]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          show v - 1 + 1 = v by omega, hc']
  have hpermB : ∀ i, i ∈ (List.finRange r).filterMap idxB ↔ i = m := by
    intro i
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨j, -, hj⟩
      simp only [idxB] at hj
      split_ifs at hj
      exact (Option.some_injective _ hj).symm
    · rintro rfl
      exact ⟨o.symm c, List.mem_finRange _, by simp [idxB]⟩
  have hpermR : ∀ i, i ∈ (List.finRange q).filterMap idxR ↔ i < 2 * m + 1 ∧ i ≠ m := by
    intro i
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨j, -, hj⟩
      simp only [idxR, Option.map_eq_some_iff] at hj
      obtain ⟨v, hv, rfl⟩ := hj
      obtain ⟨hv', hβv⟩ := exists_of_pathIndex_eq_some hv
      obtain ⟨h1, h2⟩ := C.ne_of_rest_eq_path hm (e j) hβv.symm
      simp only at h1 h2
      simp only [shift]
      split_ifs <;> omega
    · rintro ⟨hi1, hi2⟩
      set v := if i < m then i else i + 1 with hv
      have hvL : v < 2 * C.half c := by rw [hv]; split_ifs <;> omega
      have h1 : v ≠ m := by rw [hv]; split_ifs <;> omega
      have h2 : v ≠ m + 1 := by rw [hv]; split_ifs <;> omega
      refine ⟨e.symm ⟨C.path c ⟨v, hvL⟩, C.path_mem_rest hm ⟨v, hvL⟩ h1 h2⟩,
        List.mem_finRange _, ?_⟩
      simp only [idxR, Equiv.apply_symm_apply, pathIndex_apply hβ.injective, Option.map_some,
        Option.some.injEq, shift]
      rw [hv]
      split_ifs <;> omega
  have hperm : ((List.finRange r).filterMap idxB ++ (List.finRange q).filterMap idxR).Perm
      (List.range (2 * m + 1)) := by
    refine perm_range_of_nodup ?_ fun i => ?_
    · rw [List.nodup_append]
      refine ⟨(List.nodup_finRange r).filterMap ?_, (List.nodup_finRange q).filterMap ?_, ?_⟩
      · intro j j' i hj hj'
        simp only [idxB, Option.mem_def] at hj hj'
        split_ifs at hj hj' with h h'
        exact o.injective (h.trans h'.symm)
      · intro j j' i hj hj'
        simp only [idxR, Option.mem_def, Option.map_eq_some_iff] at hj hj'
        obtain ⟨v, hv, rfl⟩ := hj
        obtain ⟨v', hv', hvv'⟩ := hj'
        obtain ⟨hvL, hβv⟩ := exists_of_pathIndex_eq_some hv
        obtain ⟨hvL', hβv'⟩ := exists_of_pathIndex_eq_some hv'
        obtain ⟨h1, h2⟩ := C.ne_of_rest_eq_path hm (e j) hβv.symm
        simp only at h1 h2
        obtain ⟨h1', h2'⟩ := C.ne_of_rest_eq_path hm (e j') hβv'.symm
        simp only at h1' h2'
        have hvv : v' = v := by
          simp only [shift] at hvv'
          split_ifs at hvv' <;> omega
        subst hvv
        exact e.injective (Subtype.ext (hβv.symm.trans hβv'))
      · intro i hi i' hi'
        rw [hpermB] at hi
        rw [hpermR] at hi'
        omega
    · rw [List.mem_append, hpermB, hpermR]
      omega
  have hprod : M (C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z) =
      (((List.finRange r).filterMap idxB ++ (List.finRange q).filterMap idxR).map y).prod := by
    rw [EvenChainData.patternProduct, map_mul, map_list_prod, map_list_prod, List.ofFn_eq_map,
      List.ofFn_eq_map, List.map_map, List.map_map, List.map_append, List.prod_append]
    congr 1
    · exact list_prod_map_eq_filterMap _ _ _ hblock _
    · exact list_prod_map_eq_filterMap _ _ _ hrest _
  rw [← charpoly_normalizedPathMatrix hρ hβ hlam x v₀ hv₀, hprod,
    charpoly_prod_patY (by omega) c' β' hperm]
  cases hε : ε c
  · have hβ'' : β' = blockBeta 1 1 a b (s c * lam') 0 0 := by
      rw [hβ', hε]
      rfl
    rw [hβ'', charpoly_pathMat_pattern_eq_ordPoly m c' _ (by simp [blockBeta])
      (by simp [blockBeta]) (by simp [blockBeta]) (by simp [blockBeta])
      (by simp [blockBeta]; linear_combination hab)]
    simp only [Bool.false_eq_true, ite_false]
    congr 2
    · simp only [blockBeta, ite_true]
      ring
    · simp [blockBeta]
  · have hβ'' : β' = blockBeta (t c : k) ((t c)⁻¹ : kˣ) a b (s c * lam') D.ca D.cb := by
      rw [hβ', hε]
      rfl
    have ht : (t c : k) * ((t c)⁻¹ : kˣ) = 1 := Units.mul_inv (t c)
    rw [hβ'', charpoly_pathMat_pattern_eq_ordPoly m c' _ (by simp [blockBeta])
      (by simp [blockBeta]) (by simp [blockBeta]) (by simp [blockBeta])
      (show b * (((t c)⁻¹ : kˣ) : k) * ((t c : k) * a) = -1 by
        linear_combination ((t c : k) * ((t c)⁻¹ : kˣ)) * hab - ht)]
    simp only [ite_true]
    congr 2
    · simp only [blockBeta, ite_true]
      ring
    · simp [blockBeta]
      ring

end EvenChainData

end EvenChain

end Langlands.GroupScheme.SplitPinning
