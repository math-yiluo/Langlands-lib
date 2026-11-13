import Langlands.GroupScheme.Rational.EvenChainPathCharpoly

/-! # Cross-section coordinates of even-path pattern products -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.LinearAlgebra.PathCoxeter

variable {R : Type*} [CommRing R]

/-- The coordinate `m` of `patCoord m d σ δ` is `σ` plus a quantity independent of `σ` and `δ`. -/
theorem patCoord_self (m : ℕ) (d : ℕ → R) (σ δ δ' : R) :
    patCoord m d σ δ m = patCoord m d 0 δ' m + σ := by
  simp only [patCoord, patU]
  split_ifs <;> first | omega | contradiction | ring

/-- The coordinate `m + 1` of `patCoord m d σ δ` is `δ` plus a quantity independent of `δ`. -/
theorem patCoord_succ_self (m : ℕ) (d : ℕ → R) (σ δ : R) :
    patCoord m d σ δ (m + 1) = patCoord m d σ 0 (m + 1) + δ := by
  simp only [patCoord, ite_true, add_zero]

end Langlands.LinearAlgebra.PathCoxeter

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights Langlands.LinearAlgebra.PathCoxeter

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {J : Type u} (C : p.EvenChainData J)

namespace EvenChainData

/-! ### Path positions -/

/-- A quantity attached to path positions takes the same value at two positions with the same
vertex. -/
theorem eq_of_path_eq {α : Sort*} (f : (c : J) → ℕ → α) {c c' : J} {v : Fin (2 * C.half c)}
    {v' : Fin (2 * C.half c')} (h : C.path c' v' = C.path c v) : f c' v' = f c v := by
  obtain rfl := C.disjoint c' c v' v h
  obtain rfl := (C.isPathComponent c').injective h
  rfl

theorem half_pos (c : J) : 0 < C.half c := by
  have := (C.isPathComponent c).pos
  omega

/-- A merged simple root is a path vertex. -/
theorem exists_path_eq_of_not_rest {w : p.base.support}
    (hw : ¬∀ c, w ≠ (C.modified c).a ∧ w ≠ (C.modified c).b) :
    ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = w := by
  by_contra hne
  apply hw
  intro c
  constructor
  · intro h
    rw [C.modified_a] at h
    exact hne ⟨c, _, h.symm⟩
  · intro h
    rw [C.modified_b] at h
    exact hne ⟨c, _, h.symm⟩

/-- A simple root off all paths is unmerged. -/
theorem rest_of_offPath {w : p.base.support} (hw : ∀ (c : J) (v : Fin (2 * C.half c)),
    C.path c v ≠ w) : ∀ c, w ≠ (C.modified c).a ∧ w ≠ (C.modified c).b := by
  by_contra h
  obtain ⟨c, v, hv⟩ := C.exists_path_eq_of_not_rest h
  exact hw c v hv

/-! ### The ordering with merged roots first -/

/-- The merged simple roots: the two middle vertices of each path. -/
abbrev Merged : Type u :=
  {j : p.base.support // ¬∀ c, j ≠ (C.modified c).a ∧ j ≠ (C.modified c).b}

open Classical in
/-- The number of merged simple roots. -/
def mergedCount : ℕ := Fintype.card C.Merged

open Classical in
/-- An ordering of all simple roots that lists the merged simple roots first (in a fixed
order) and then the unmerged ones in the order `e`. -/
def mergedFirstOrder {q : ℕ} (e : Fin q ≃ C.Rest) : Fin (C.mergedCount + q) ≃ p.base.support :=
  finSumFinEquiv.symm.trans
    (((Fintype.equivFin C.Merged).symm.sumCongr e).trans
      ((Equiv.sumComm _ _).trans
        (Equiv.sumCompl fun j : p.base.support =>
          ∀ c, j ≠ (C.modified c).a ∧ j ≠ (C.modified c).b)))

theorem mergedFirstOrder_natAdd {q : ℕ} (e : Fin q ≃ C.Rest) (j : Fin q) :
    C.mergedFirstOrder e (Fin.natAdd C.mergedCount j) = (e j : p.base.support) := by
  simp only [mergedFirstOrder, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem exists_path_eq_mergedFirstOrder_castAdd {q : ℕ} (e : Fin q ≃ C.Rest)
    (i : Fin C.mergedCount) :
    ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = C.mergedFirstOrder e (Fin.castAdd q i) := by
  classical
  apply C.exists_path_eq_of_not_rest
  have h : C.mergedFirstOrder e (Fin.castAdd q i) =
      ((Fintype.equivFin C.Merged).symm i : p.base.support) := by
    simp only [mergedFirstOrder, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  rw [h]
  exact ((Fintype.equivFin C.Merged).symm i).2

/-! ### Cross-section coordinates -/

/-- Steinberg's middle coordinate for the constant `A`: `-(t s A)` for the pattern value
`true` and `-(s A)` for `false`. -/
def crossSigma (A : k) (b : Bool) (s : k) (t : kˣ) : k :=
  if b then -((t : k) * s * A) else -(s * A)

/-- Steinberg's extra coordinate for the constant `B`: `t B` for the pattern value `true`
and `0` for `false`. -/
def crossDelta (B : k) (b : Bool) (t : kˣ) : k :=
  if b then (t : k) * B else 0

variable {q : ℕ} (e : Fin q ≃ C.Rest)

/-- The coordinates along the path `c` of the ordinary product attached to the pattern
coordinates `(ε, s, t, z)`. -/
def pathCoord (A B : J → k) (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k) (c : J) :
    ℕ → k :=
  patCoord (C.half c - 1) (C.restCoord e z c) (crossSigma (A c) (ε c) (s c) (t c))
    (crossDelta (B c) (ε c) (t c))

open Classical in
/-- The cross-section coordinates: at a vertex of the path `c` they are `pathCoord`, at an
unmerged simple root off all paths they are the unmerged coordinate, and `0` elsewhere (which
does not occur). -/
def crossFun (A B : J → k) (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k)
    (w : p.base.support) : k :=
  if h : ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = w then
    C.pathCoord e A B ε s t z h.choose h.choose_spec.choose
  else if h' : ∀ c, w ≠ (C.modified c).a ∧ w ≠ (C.modified c).b then z (e.symm ⟨w, h'⟩)
  else 0

theorem crossFun_path (A B : J → k) (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k)
    (c : J) (v : Fin (2 * C.half c)) :
    C.crossFun e A B ε s t z (C.path c v) = C.pathCoord e A B ε s t z c v := by
  have h : ∃ (c' : J) (v' : Fin (2 * C.half c')), C.path c' v' = C.path c v := ⟨c, v, rfl⟩
  rw [crossFun, dite_eq_left h]
  exact C.eq_of_path_eq (fun c' v' => C.pathCoord e A B ε s t z c' v')
    h.choose_spec.choose_spec

theorem crossFun_of_offPath (A B : J → k) (ε : J → Bool) (s : J → k) (t : J → kˣ)
    (z : Fin q → k) (j : Fin q)
    (hj : ∀ (c : J) (v : Fin (2 * C.half c)), C.path c v ≠ (e j : p.base.support)) :
    C.crossFun e A B ε s t z (e j : p.base.support) = z j := by
  have h : ¬∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = (e j : p.base.support) := by
    rintro ⟨c, v, hv⟩
    exact hj c v hv
  rw [crossFun, dite_eq_right h, dite_eq_left (e j).2]
  simp

/-- **Injectivity of the cross-section coordinates.** If `A` and `B` do not vanish, the
cross-section coordinates determine the pattern, `s`, the unmerged coordinates, and `t` on the
paths with pattern value `true`. -/
theorem eq_of_crossFun_eq {A B : J → k} (hA : ∀ c, A c ≠ 0) (hB : ∀ c, B c ≠ 0)
    {ε ε' : J → Bool} {s s' : J → k} {t t' : J → kˣ} {z z' : Fin q → k}
    (h : ∀ w, C.crossFun e A B ε s t z w = C.crossFun e A B ε' s' t' z' w) :
    ε = ε' ∧ s = s' ∧ (∀ c, ε c = true → t c = t' c) ∧ z = z' := by
  have hc : ∀ c, crossDelta (B c) (ε c) (t c) = crossDelta (B c) (ε' c) (t' c) ∧
      crossSigma (A c) (ε c) (s c) (t c) = crossSigma (A c) (ε' c) (s' c) (t' c) ∧
      (∀ i < C.half c - 1, C.restCoord e z c i = C.restCoord e z' c i) ∧
      (∀ i < C.half c - 1, C.restCoord e z c (C.half c - 1 + 2 + i) =
        C.restCoord e z' c (C.half c - 1 + 2 + i)) := by
    intro c
    apply eq_of_patCoord_eq
    intro v hv
    have hv' : v < 2 * C.half c := by have := C.half_pos c; omega
    have h1 := h (C.path c ⟨v, hv'⟩)
    rw [crossFun_path, crossFun_path] at h1
    exact h1
  have hε : ∀ c, ε c = ε' c := by
    intro c
    have h1 := (hc c).1
    unfold crossDelta at h1
    cases hεc : ε c <;> cases hεc' : ε' c <;>
      simp only [hεc, hεc', Bool.false_eq_true, ↓reduceIte] at h1
    · rfl
    · exact absurd h1.symm (mul_ne_zero (t' c).ne_zero (hB c))
    · exact absurd h1 (mul_ne_zero (t c).ne_zero (hB c))
    · rfl
  have ht : ∀ c, ε c = true → (t c : k) = t' c := by
    intro c hc'
    have h1 := (hc c).1
    unfold crossDelta at h1
    rw [← hε c, hc'] at h1
    simp only [↓reduceIte] at h1
    exact mul_right_cancel₀ (hB c) h1
  refine ⟨funext hε, funext fun c => ?_, fun c hc' => Units.ext (ht c hc'), funext fun j => ?_⟩
  · have h2 := (hc c).2.1
    unfold crossSigma at h2
    rw [← hε c] at h2
    cases hεc : ε c
    · simp only [hεc, Bool.false_eq_true, ↓reduceIte, neg_inj] at h2
      exact mul_right_cancel₀ (hA c) h2
    · simp only [hεc, ↓reduceIte, neg_inj] at h2
      rw [ht c hεc] at h2
      exact mul_left_cancel₀ (t' c).ne_zero (mul_right_cancel₀ (hA c) h2)
  · by_cases hj : ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = (e j : p.base.support)
    · obtain ⟨c, v, hv⟩ := hj
      obtain ⟨h1, h2⟩ := C.ne_of_rest_eq_path (m := C.half c - 1)
        (by have := C.half_pos c; omega) (e j) hv.symm
      rw [← C.restCoord_eq e z v.2 hv.symm, ← C.restCoord_eq e z' v.2 hv.symm]
      rcases Nat.lt_or_ge (v : ℕ) (C.half c - 1) with hlt | hge
      · exact (hc c).2.2.1 v hlt
      · have h3 := (hc c).2.2.2 ((v : ℕ) - (C.half c - 1 + 2)) (by have := v.2; omega)
        rwa [show C.half c - 1 + 2 + ((v : ℕ) - (C.half c - 1 + 2)) = v by omega] at h3
    · push Not at hj
      have h1 := h (e j)
      rwa [C.crossFun_of_offPath e _ _ _ _ _ _ j hj,
        C.crossFun_of_offPath e _ _ _ _ _ _ j hj] at h1

/-- **Surjectivity of the cross-section coordinates.** If `A` and `B` do not vanish, every
family of coordinates on the simple roots is the family of cross-section coordinates of some
pattern coordinates. -/
theorem exists_crossFun_eq {A B : J → k} (hA : ∀ c, A c ≠ 0) (hB : ∀ c, B c ≠ 0)
    (cv : p.base.support → k) :
    ∃ (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k),
      ∀ w, C.crossFun e A B ε s t z w = cv w := by
  classical
  let g : J → ℕ → k := fun c v => if h : v < 2 * C.half c then cv (C.path c ⟨v, h⟩) else 0
  choose d σ hd using fun c => exists_patCoord_eq (C.half c - 1) (g c)
  let δ : J → k := fun c => (-1) ^ (C.half c - 1 + 1) *
    ∑ i ∈ Finset.range (2 * (C.half c - 1) + 2), (-1) ^ i * g c i
  let ε : J → Bool := fun c => decide (δ c ≠ 0)
  let t : J → kˣ := fun c =>
    if h : δ c ≠ 0 then Units.mk0 (δ c / B c) (div_ne_zero h (hB c)) else 1
  let s : J → k := fun c => -σ c / (A c * t c)
  let z : Fin q → k := fun j =>
    if h : ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = (e j : p.base.support) then
      d h.choose h.choose_spec.choose
    else cv (e j)
  refine ⟨ε, s, t, z, fun w => ?_⟩
  by_cases hw : ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = w
  · obtain ⟨c, v, rfl⟩ := hw
    have hpos := C.half_pos c
    have hm : C.half c = C.half c - 1 + 1 := by omega
    rw [crossFun_path]
    have hσδ : crossSigma (A c) (ε c) (s c) (t c) = σ c ∧ crossDelta (B c) (ε c) (t c) = δ c := by
      unfold crossSigma crossDelta
      by_cases h0 : δ c = 0
      · have hε : ε c = false := by simp [ε, h0]
        have ht : t c = 1 := by simp [t, h0]
        simp only [hε, Bool.false_eq_true, ↓reduceIte, h0, s, ht, Units.val_one, mul_one,
          and_true]
        field_simp [hA c]
      · have hε : ε c = true := by simp [ε, h0]
        have ht : (t c : k) = δ c / B c := by simp [t, h0]
        simp only [hε, ↓reduceIte, s, ht]
        constructor
        · field_simp [hA c, hB c, h0]
        · field_simp [hB c]
    have hz : ∀ i (hi : i < 2 * C.half c), i ≠ C.half c - 1 → i ≠ C.half c - 1 + 1 →
        C.restCoord e z c i = d c i := by
      intro i hi h1 h2
      have hr := C.path_mem_rest hm ⟨i, hi⟩ h1 h2
      have hj : ((e (e.symm ⟨C.path c ⟨i, hi⟩, hr⟩) : C.Rest) : p.base.support) =
          C.path c ⟨i, hi⟩ := by simp
      rw [C.restCoord_eq e z hi hj]
      have hex : ∃ (c' : J) (v' : Fin (2 * C.half c')),
          C.path c' v' = ((e (e.symm ⟨C.path c ⟨i, hi⟩, hr⟩) : C.Rest) : p.base.support) :=
        ⟨c, ⟨i, hi⟩, hj.symm⟩
      simp only [z]
      rw [dite_eq_left hex]
      exact C.eq_of_path_eq (fun c' v' => d c' v') (hex.choose_spec.choose_spec.trans hj)
    unfold pathCoord
    rw [hσδ.1, hσδ.2, patCoord_congr _ _ (d' := d c)
      (fun i hi => hz i (by omega) (by omega) (by omega))
      (fun i hi1 hi2 => hz i (by omega) (by omega) (by omega)),
      hd c v (by have := v.2; omega)]
    simp only [g, dite_eq_left v.2]
  · have hr := C.rest_of_offPath (fun c v hv => hw ⟨c, v, hv⟩)
    have hj : ((e (e.symm ⟨w, hr⟩) : C.Rest) : p.base.support) = w := by simp
    have hoff : ∀ (c : J) (v : Fin (2 * C.half c)),
        C.path c v ≠ ((e (e.symm ⟨w, hr⟩) : C.Rest) : p.base.support) := by
      intro c v hv
      exact hw ⟨c, v, hv.trans hj⟩
    rw [← hj, C.crossFun_of_offPath e _ _ _ _ _ _ _ hoff]
    simp only [z]
    rw [dite_eq_right (fun ⟨c, v, hv⟩ => hoff c v hv)]

/-! ### Pattern products with the same coordinates -/

variable (x : p.NormalizedSimpleRootParametrizations)

/-- Pattern products agree if their patterns, `s` and unmerged coordinates agree and their
`t` agree on the paths with pattern value `true`. -/
theorem patternProduct_congr {r : ℕ} (o : Fin r ≃ J) {ε ε' : J → Bool} {s s' : J → k}
    {t t' : J → kˣ} {z z' : Fin q → k} (hε : ε = ε') (hs : s = s')
    (ht : ∀ c, ε c = true → t c = t' c) (hz : z = z') :
    C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t z =
      C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε' s' t' z' := by
  subst hε hs hz
  have hb : (fun j : Fin r => C.block x (o j) (ε (o j)) (s (o j)) (t (o j))) =
      fun j => C.block x (o j) (ε (o j)) (s (o j)) (t' (o j)) := by
    funext j
    cases hεc : ε (o j)
    · simp only [block, Bool.false_eq_true, ite_false]
    · rw [ht (o j) hεc]
  unfold patternProduct
  rw [hb]

/-! ### Representations whose highest weight is orthogonal to all paths -/

/-- Let `E'` list path vertices first (`N` of them) and then the unmerged simple roots in the
order `e`. On a representation whose highest weight is orthogonal to all path coroots, a
pattern product and the ordinary product along `E'` have the same matrix, as soon as the
coordinates of the ordinary product at the unmerged roots off all paths are the unmerged
coordinates. -/
theorem rationalMatrix_patternProduct_eq_of_offPath {V : Type} [Fintype V] [DecidableEq V]
    {ρ : MatrixRepresentation G V} {lam : characterLattice p.torus}
    (hρ : p.IsHighestWeight ρ lam)
    (hlam : ∀ c i, p.rootDatum.toLinearMap lam (p.rootDatum.coroot (C.path c i)) = 0)
    {N r : ℕ} (o : Fin r ≃ J) (E' : Fin (N + q) ≃ p.base.support)
    (h1 : ∀ i, ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = E' (Fin.castAdd q i))
    (h2 : ∀ j, E' (Fin.natAdd N j) = (e j : p.base.support))
    (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k) (cf : Fin (N + q) → k)
    (hcf : ∀ j, (∀ (c : J) (v : Fin (2 * C.half c)), C.path c v ≠ (e j : p.base.support)) →
      cf (Fin.natAdd N j) = z j) :
    ρ.rationalMatrix (C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s
        t z) =
      ρ.rationalMatrix (List.ofFn fun j =>
        (x (E' j)).toRootParametrization.rationalPoint (cf j) *
          (canonicalSimpleReflectionRepresentatives x (E' j)).point).prod := by
  have hfac : ∀ (w : p.base.support) (d : k), (∃ (c : J) (v : Fin (2 * C.half c)),
      C.path c v = w) → ρ.rationalMatrix ((x w).toRootParametrization.rationalPoint d *
        (canonicalSimpleReflectionRepresentatives x w).point) = 1 := by
    rintro w d ⟨c, v, rfl⟩
    exact C.rationalMatrix_rootFactor_eq_one_of_offPath x hρ hlam c v d
  unfold patternProduct
  rw [map_mul, map_list_prod, map_list_prod, List.ofFn_add, List.prod_append, map_mul,
    map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, List.map_ofFn, List.map_ofFn]
  have hb : (List.ofFn (ρ.rationalMatrix ∘ fun j : Fin r =>
      C.block x (o j) (ε (o j)) (s (o j)) (t (o j)))).prod = 1 := by
    apply List.prod_eq_one
    intro M hM
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hM
    exact C.rationalMatrix_block_eq_one_of_offPath x hρ hlam _ _ _ _
  have hm : (List.ofFn (ρ.rationalMatrix ∘ fun i : Fin N =>
      (x (E' (Fin.castLE (Nat.le_add_right N q) i))).toRootParametrization.rationalPoint
          (cf (Fin.castLE (Nat.le_add_right N q) i)) *
        (canonicalSimpleReflectionRepresentatives x
          (E' (Fin.castLE (Nat.le_add_right N q) i))).point)).prod = 1 := by
    apply List.prod_eq_one
    intro M hM
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
    exact hfac _ _ (h1 i)
  rw [hb, hm, one_mul, one_mul]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  rw [h2 j]
  by_cases hj : ∃ (c : J) (v : Fin (2 * C.half c)), C.path c v = (e j : p.base.support)
  · rw [hfac _ _ hj, hfac _ _ hj]
  · push Not at hj
    rw [hcf j hj]

/-! ### Coordinates from characteristic polynomials -/

/-- Let `ρ` have highest weight the fundamental weight of the end vertex of the path `c`, and
let `A'`, `B'` be constants describing the characteristic polynomials of the pattern products
on `ρ` as in `charpoly_patternProduct`. If a pattern product and an ordinary product along an
ordering `E'` have the same characteristic polynomial on `ρ`, then the coordinates of the
ordinary product along the path `c` are the pattern coordinates `patCoord`. -/
theorem patCoord_eq_of_charpoly_eq {V : Type} [Fintype V] [DecidableEq V]
    {ρ : MatrixRepresentation G V} {lam : characterLattice p.torus} (c : J) {m : ℕ}
    (hm : C.half c = m + 1) (hρ : p.IsHighestWeight ρ lam)
    (hlam : IsPathFundamental (C.path c) lam)
    (v₀ : p.representationWeightSpace ρ (pathWeight (C.path c) lam 0)) (hv₀ : v₀ ≠ 0)
    {A' B' : k}
    (hAB : ∀ {r q : ℕ} (o : Fin r ≃ J) (e : Fin q ≃ C.Rest)
      (ε : J → Bool) (s : J → k) (t : J → kˣ) (z : Fin q → k),
      (ρ.rationalMatrix (C.patternProduct x (canonicalSimpleReflectionRepresentatives x)
          o e ε s t z) : Matrix V V k).charpoly =
        ordPoly m (patCoord m (C.restCoord e z c)
          (if ε c then -((t c : k) * s c * A') else -(s c * A'))
          (if ε c then (t c : k) * B' else 0)))
    {N r : ℕ} (o : Fin r ≃ J) (E' : Fin N ≃ p.base.support) (ε : J → Bool) (s : J → k)
    (t : J → kˣ) (z : Fin q → k) (cf : Fin N → k)
    (h : (ρ.rationalMatrix (C.patternProduct x (canonicalSimpleReflectionRepresentatives x)
          o e ε s t z) : Matrix V V k).charpoly =
      (ρ.rationalMatrix (List.ofFn fun j =>
        (x (E' j)).toRootParametrization.rationalPoint (cf j) *
          (canonicalSimpleReflectionRepresentatives x (E' j)).point).prod :
            Matrix V V k).charpoly)
    (v : ℕ) (hv : v < 2 * C.half c) :
    patCoord m (C.restCoord e z c) (crossSigma A' (ε c) (s c) (t c))
        (crossDelta B' (ε c) (t c)) v = cf (E'.symm (C.path c ⟨v, hv⟩)) := by
  rw [hAB, charpoly_rootFactorProduct hρ (C.isPathComponent c) hlam x v₀ hv₀
    (show 2 * C.half c = 2 * m + 2 by omega) E' cf] at h
  have h1 := eq_of_ordPoly_eq h (show v < 2 * m + 2 by omega)
  rw [dite_eq_left hv] at h1
  exact h1

end EvenChainData

end Langlands.GroupScheme.SplitPinning
