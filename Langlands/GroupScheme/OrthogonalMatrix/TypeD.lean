import Langlands.GroupScheme.OrthogonalMatrix.Roots
import Langlands.GroupScheme.Reductive.LinkedRootsAlmostSimple
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # The type `D` root datum of the split orthogonal group and almost simplicity

The roots of the diagonal torus of `O_{2l}` are the characters `w(x) + w(y)` for indices
`x, y : l ⊕ l` with `x ≠ y` and `x ≠ swap y`, where `w(inl a) = e_a` and `w(inr a) = -e_a`.
The coroot at `w(x) + w(y)` is `w(x)^∨ + w(y)^∨`; this is forced by the reflections once `l`
has three elements. Two roots `w(swap x) + w(z)` and `w(x) + w(y)` with `z` of a third index
are linked, and these links join any two roots. Hence a nontrivial semisimple identity component
of the split orthogonal group over an algebraically closed field is almost simple.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TypeD

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} {l : Type}

omit [IsAffineHom G.X.hom] in
private theorem ne_swap_comm {x y : l ⊕ l} (h : x ≠ y.swap) : y ≠ x.swap := fun hy =>
  h (by rw [hy, Sum.swap_swap])

/-- **Linked roots of type `D`.** Let `w : l ⊕ l → X(T)` be characters such that every root of
`t` is `w x + w y` with `x ≠ y` and `x ≠ swap y`. Suppose that `w (swap x) + w z` is linked to
`w x + w y` whenever `z` differs from `x`, `y` and their swaps. If for any `x` and `y` such a
`z` exists, any two roots are joined by a chain of linked roots. -/
theorem reflTransGen_rootsLinked_of_typeD (w : l ⊕ l → characterLattice T)
    (hroots : ∀ χ ∈ relativeRoots t, ∃ x y, x ≠ y ∧ x ≠ y.swap ∧ χ = w x + w y)
    (hlink : ∀ x y z, x ≠ y → x ≠ y.swap → z ≠ x → z ≠ x.swap → z ≠ y → z ≠ y.swap →
      RootsLinked t (w x.swap + w z) (w x + w y))
    (hl : ∀ x y : l ⊕ l, ∃ z, z ≠ x ∧ z ≠ x.swap ∧ z ≠ y ∧ z ≠ y.swap) :
    ∀ α ∈ relativeRoots t, ∀ β ∈ relativeRoots t,
      Relation.ReflTransGen (RootsLinked t) α β := by
  let R := Relation.ReflTransGen (RootsLinked t)
  have edge : ∀ {α β}, RootsLinked t α β → R α β := fun h => Relation.ReflTransGen.single h
  have edge' : ∀ {α β}, RootsLinked t α β → R β α := fun h => Relation.ReflTransGen.single h.symm
  -- Changing the second index to its swap.
  have flip : ∀ x y, x ≠ y → x ≠ y.swap → R (w x + w y) (w x + w y.swap) := by
    intro x y h₁ h₂
    obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := hl x y
    have e₁ := hlink x y z h₁ h₂ hz₁ hz₂ hz₃ hz₄
    have e₂ := hlink x y.swap z h₂ (by rwa [Sum.swap_swap]) hz₁ hz₂ hz₄
      (by rwa [Sum.swap_swap])
    exact (edge' e₁).trans (edge e₂)
  -- Changing the second index arbitrarily.
  have same : ∀ x y y', x ≠ y → x ≠ y.swap → x ≠ y' → x ≠ y'.swap →
      R (w x + w y) (w x + w y') := by
    intro x y y' h₁ h₂ h₁' h₂'
    by_cases e₁ : y' = y
    · subst e₁
      exact Relation.ReflTransGen.refl
    by_cases e₂ : y' = y.swap
    · subst e₂
      exact flip x y h₁ h₂
    have a₁ := edge' (hlink y x y' (Ne.symm h₁) (ne_swap_comm h₂) e₁ e₂ (Ne.symm h₁')
      (ne_swap_comm h₂'))
    have a₂ := edge' (hlink y' y.swap x e₂ (by rwa [Sum.swap_swap]) h₁' h₂' h₂
      (by rwa [Sum.swap_swap]))
    have a₃ := flip x y'.swap h₂' (by rwa [Sum.swap_swap])
    rw [Sum.swap_swap] at a₃
    rw [add_comm (w x) (w y)]
    refine a₁.trans ?_
    rw [add_comm (w y.swap) (w y')]
    refine a₂.trans ?_
    rw [add_comm (w y'.swap) (w x)]
    exact a₃
  intro α hα β hβ
  obtain ⟨x, y, h₁, h₂, rfl⟩ := hroots α hα
  obtain ⟨x', y', h₁', h₂', rfl⟩ := hroots β hβ
  obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := hl x x'
  have s₁ := same x y z h₁ h₂ (Ne.symm hz₁) (ne_swap_comm hz₂)
  have s₂ := same z x x' hz₁ hz₂ hz₃ hz₄
  have s₃ := same x' z y' (Ne.symm hz₃) (ne_swap_comm hz₄) h₁' h₂'
  refine s₁.trans ?_
  rw [add_comm (w x) (w z)]
  refine s₂.trans ?_
  rw [add_comm (w z) (w x')]
  exact s₃

/-- **Almost simplicity from a type `D` root datum.** Over an algebraically closed field, let
`G` be nontrivial and semisimple with a split maximal torus `t`. Let `w : l ⊕ l → X(T)` and
`ω : l ⊕ l → X_*(T)` pair by `⟨w u, ω x⟩ = 1` if `u = x`, `-1` if `u = swap x`, and `0`
otherwise. Suppose the roots of `t` are exactly the characters `w x + w y` with `x ≠ y` and
`x ≠ swap y`, that a root datum `P` realizing `t` has coroot `ω x + ω y` at such a root, and
that for any `x, y` some `z` differs from `x`, `y` and their swaps. Then `G` is almost
simple. -/
theorem isAlmostSimple_of_typeD [IsAlgClosed k] [DecidableEq l] (hG : IsSemisimple G)
    (hT : IsSplitTorus T.toGrp) (hsplit : IsSplitSubtorus t) (hmax : IsMaximalTorus t)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥)
    (w : l ⊕ l → characterLattice T) (ω : l ⊕ l → cocharacterLattice T)
    (hdual : ∀ u x, latticePairing T (w u) (ω x) =
      if u = x then 1 else if u = x.swap then -1 else 0)
    (hroots : ∀ χ ∈ relativeRoots t, ∃ x y, x ≠ y ∧ x ≠ y.swap ∧ χ = w x + w y)
    (hmem : ∀ x y, x ≠ y → x ≠ y.swap → w x + w y ∈ relativeRoots t)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf t P)
    (hcoroot : ∀ r x y, x ≠ y → x ≠ y.swap → P.root r = w x + w y → P.coroot r = ω x + ω y)
    (hl : ∀ x y : l ⊕ l, ∃ z, z ≠ x ∧ z ≠ x.swap ∧ z ≠ y ∧ z ≠ y.swap) :
    IsAlmostSimple G := by
  have : Infinite k := inferInstance
  have hmemP : ∀ χ ∈ relativeRoots t, ∃ r, P.root r = χ := fun χ hχ => by
    have h : χ ∈ Set.range P.root := by rw [hP.2.1]; exact hχ
    exact h
  have hpair : ∀ r r', P.pairing r r' = latticePairing T (P.root r) (P.coroot r') :=
    fun r r' => by rw [← P.root_coroot_eq_pairing, hP.1]
  have hswap : ∀ x : l ⊕ l, x.swap ≠ x := fun x => by rcases x with a | a <;> simp
  -- Each `w u` pairs with `ω x + ω y` to `-1`, `0` or `1`.
  have hunit : ∀ x y u, x ≠ y → x ≠ y.swap →
      -1 ≤ latticePairing T (w u) (ω x + ω y) ∧ latticePairing T (w u) (ω x + ω y) ≤ 1 := by
    intro x y u h₁ h₂
    rw [map_add, hdual, hdual]
    by_cases hux : u = x
    · subst hux
      simp [h₁, h₂]
    by_cases hux' : u = x.swap
    · subst hux'
      have h₃ : x.swap ≠ y := ne_swap_comm h₂ |>.symm
      have h₄ : x.swap ≠ y.swap := fun h => h₁ (by simpa using congrArg Sum.swap h)
      simp [h₃, h₄, hswap]
    · simp only [hux, hux', ite_false, zero_add]
      split_ifs <;> omega
  have link : ∀ x y z, x ≠ y → x ≠ y.swap → z ≠ x → z ≠ x.swap → z ≠ y → z ≠ y.swap →
      RootsLinked t (w x.swap + w z) (w x + w y) := by
    intro x y z h₁ h₂ h₃ h₄ h₅ h₆
    have hxz : x.swap ≠ z := Ne.symm h₄
    have hxz' : x.swap ≠ z.swap := fun h => h₃ (by
      have h' := congrArg Sum.swap h
      rw [Sum.swap_swap, Sum.swap_swap] at h'
      exact h'.symm)
    obtain ⟨r, hr⟩ := hmemP _ (hmem x.swap z hxz hxz')
    obtain ⟨r', hr'⟩ := hmemP _ (hmem x y h₁ h₂)
    let g : characterLattice T →+ ℤ :=
      ((latticePairing T).flip (ω x + ω y)).toAddMonoidHom
    have hg : ∀ χ, g χ = latticePairing T χ (ω x + ω y) := fun _ => rfl
    have h₇ : x.swap ≠ y := ne_swap_comm h₂ |>.symm
    have h₈ : x.swap ≠ y.swap := fun h => h₁ (by simpa using congrArg Sum.swap h)
    have h₉ : y ≠ x := Ne.symm h₁
    have h₁₀ : y ≠ x.swap := ne_swap_comm h₂
    have hgβ : g (w x.swap + w z) = -1 := by
      simp only [hg, map_add, LinearMap.add_apply, hdual]
      simp [hswap, h₇, h₈, h₃, h₄, h₅, h₆]
    have hgβ' : g (w x + w y) = 2 := by
      simp only [hg, map_add, LinearMap.add_apply, hdual]
      simp [h₁, h₂, h₉, h₁₀]
    have hbound : ∀ χ ∈ roots t, -2 ≤ g χ := by
      intro χ hχ
      obtain ⟨u, v, -, -, rfl⟩ := hroots χ hχ
      have hu := hunit x y u h₁ h₂
      have hv := hunit x y v h₁ h₂
      rw [hg, LinearMap.map_add₂]
      omega
    have h := rootsLinked_of_pairing_eq_neg_one hG.isConnectedReductive hT hmax hP
      (r := r) (r' := r')
      (by rw [hpair, hr, hcoroot r' x y h₁ h₂ hr', ← hg, hgβ])
      (strict_combinations_of_coordinate g (by rw [hr]; exact hgβ) (by rw [hr']; exact hgβ')
        hbound)
    rwa [hr, hr'] at h
  exact isAlmostSimple_of_rootsLinked hG t hsplit hmax hnt
    (reflTransGen_rootsLinked_of_typeD w hroots link hl)

end TypeD

namespace OrthogonalMatrix

open SymplecticMatrix (weightCoord weightCoord_inl weightCoord_inr weightCoord_injective)

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Signs and coordinates of the weights -/

section Sign

/-- The sign `1` of `inl a` and `-1` of `inr a`. -/
def sgn (x : l ⊕ l) : ℤ :=
  Sum.elim (fun _ => 1) (fun _ => -1) x

omit [Fintype l] [DecidableEq l] in
@[simp] theorem sgn_inl (a : l) : sgn (Sum.inl a : l ⊕ l) = 1 := rfl

omit [Fintype l] [DecidableEq l] in
@[simp] theorem sgn_inr (a : l) : sgn (Sum.inr a : l ⊕ l) = -1 := rfl

omit [Fintype l] [DecidableEq l] in
theorem sgn_eq (x : l ⊕ l) : sgn x = 1 ∨ sgn x = -1 := by
  rcases x with a | a
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype l] in
/-- The weight `w(x)` in coordinates is `sgn x` at `index x`. -/
theorem weightCoord_eq_single (x : l ⊕ l) : weightCoord l x = Pi.single (index x) (sgn x) := by
  rcases x with a | a <;> rfl

omit [Fintype l] in
theorem weightCoord_apply_index (x : l ⊕ l) : weightCoord l x (index x) = sgn x := by
  rw [weightCoord_eq_single, Pi.single_eq_same]

omit [Fintype l] in
theorem weightCoord_apply_of_ne (x : l ⊕ l) {d : l} (h : d ≠ index x) :
    weightCoord l x d = 0 := by
  rw [weightCoord_eq_single, Pi.single_eq_of_ne h]

/-- Pairing a weight with a coordinate vector picks out the signed coordinate. -/
theorem sum_weightCoord_mul (x : l ⊕ l) (ν : l → ℤ) :
    ∑ c, weightCoord l x c * ν c = sgn x * ν (index x) := by
  rw [Finset.sum_eq_single (index x) (fun c _ hc => by rw [weightCoord_apply_of_ne x hc,
    zero_mul]) (by simp), weightCoord_apply_index]

end Sign

/-! ### The weight characters and cocharacters -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

variable (l k) in
/-- The character `w(x)` of the diagonal torus: `e_a` for `x = inl a`, `-e_a` for
`x = inr a`. -/
def weightChar (x : l ⊕ l) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv l k).symm (weightCoord l x)

variable (l k) in
/-- The cocharacter `w(x)^∨` of the diagonal torus: `e_a^∨` for `x = inl a`, `-e_a^∨` for
`x = inr a`. -/
def weightCochar (x : l ⊕ l) : cocharacterLattice 𝔻 :=
  (GeneralLinear.cocharacterCoordEquiv l k).symm (weightCoord l x)

theorem characterCoordEquiv_weightChar (x : l ⊕ l) :
    GeneralLinear.characterCoordEquiv l k (weightChar l k x) = weightCoord l x :=
  LinearEquiv.apply_symm_apply _ _

theorem cocharacterCoordEquiv_weightCochar (x : l ⊕ l) :
    GeneralLinear.cocharacterCoordEquiv l k (weightCochar l k x) = weightCoord l x :=
  LinearEquiv.apply_symm_apply _ _

/-- Pairing `w(x)` with a cocharacter picks out its signed coordinate at `index x`. -/
theorem latticePairing_weightChar (x : l ⊕ l) (ν : cocharacterLattice 𝔻) :
    latticePairing 𝔻 (weightChar l k x) ν =
      sgn x * GeneralLinear.cocharacterCoordEquiv l k ν (index x) := by
  rw [GeneralLinear.latticePairing_coord, characterCoordEquiv_weightChar, sum_weightCoord_mul]

/-- **Duality of the weights.** `⟨w(u), w(x)^∨⟩` is `1` if `u = x`, `-1` if `u = swap x` and
`0` otherwise. -/
theorem latticePairing_weightChar_weightCochar (u x : l ⊕ l) :
    latticePairing 𝔻 (weightChar l k u) (weightCochar l k x) =
      if u = x then 1 else if u = x.swap then -1 else 0 := by
  rw [latticePairing_weightChar, cocharacterCoordEquiv_weightCochar, weightCoord_eq_single]
  rcases u with a | a <;> rcases x with b | b <;> by_cases hab : a = b <;>
    simp [hab, Pi.single_apply]

/-- The roots of the diagonal torus, in terms of the weight characters. -/
theorem exists_eq_weightChar_add_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) :
    ∃ x y : l ⊕ l, x ≠ y ∧ x ≠ y.swap ∧ χ = weightChar l k x + weightChar l k y := by
  obtain ⟨x, y, hidx, hc⟩ := (mem_roots_iff χ).mp hχ
  refine ⟨x, y.swap, fun h => hidx (by rw [h, index_swap]), fun h => hidx (by
    rw [h, Sum.swap_swap]), ?_⟩
  apply (GeneralLinear.characterCoordEquiv l k).injective
  rw [hc, map_add, characterCoordEquiv_weightChar, characterCoordEquiv_weightChar,
    weightCoord_swap, sub_eq_add_neg]

theorem weightChar_add_mem_roots {x y : l ⊕ l} (h₁ : x ≠ y) (h₂ : x ≠ y.swap) :
    weightChar l k x + weightChar l k y ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
  rw [mem_roots_iff]
  refine ⟨x, y.swap, fun hidx => ?_, ?_⟩
  · rw [index_swap] at hidx
    rcases eq_or_eq_swap_of_index_eq hidx with h | h
    · exact h₁ h
    · exact h₂ h
  · rw [map_add, characterCoordEquiv_weightChar, characterCoordEquiv_weightChar,
      weightCoord_swap, sub_neg_eq_add]

/-- A root has at most two nonzero coordinates. -/
theorem coord_eq_zero_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) {c a b : l} (hca : c ≠ a)
    (hcb : c ≠ b) (hab : a ≠ b) :
    GeneralLinear.characterCoordEquiv l k χ c = 0 ∨
      GeneralLinear.characterCoordEquiv l k χ a = 0 ∨
        GeneralLinear.characterCoordEquiv l k χ b = 0 := by
  obtain ⟨p, q, -, hc⟩ := (mem_roots_iff χ).mp hχ
  have hd : ∀ d, GeneralLinear.characterCoordEquiv l k χ d ≠ 0 → d = index p ∨ d = index q := by
    intro d hd
    by_contra h
    push Not at h
    apply hd
    rw [hc, Pi.sub_apply, weightCoord_apply_of_ne p h.1, weightCoord_apply_of_ne q h.2,
      sub_zero]
  by_contra h
  push Not at h
  rcases hd c h.1 with hc' | hc' <;> rcases hd a h.2.1 with ha | ha <;>
    rcases hd b h.2.2 with hb | hb <;>
    first
    | exact hca (hc'.trans ha.symm)
    | exact hcb (hc'.trans hb.symm)
    | exact hab (ha.trans hb.symm)

/-! ### The coroots -/

section Coroot

/-- **The reflection constraint.** Let `P.root r = w(x) + w(y)` with distinct indices, `c` a
third index and `p` of index `index x`. The pairing `n = ν_c + sgn(p) ν_{index x}` of
`e_c + w(p)` with the coroot `ν` of `r` is `0` or satisfies `sgn p = n sgn x`, because the
reflected root `e_c + w(p) - n (w(x) + w(y))` has at most two nonzero coordinates. -/
theorem coroot_constraint {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (identityTorus l k) P) {r : J} {x y : l ⊕ l}
    (hr : P.root r = weightChar l k x + weightChar l k y) (hab : index x ≠ index y)
    {c : l} (hca : c ≠ index x) (hcb : c ≠ index y) (p : l ⊕ l) (hp : index p = index x) :
    GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) c +
        sgn p * GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) (index x) = 0 ∨
      sgn p = (GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) c +
        sgn p * GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) (index x)) * sgn x := by
  set ν := GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) with hν
  have hroots : roots (identityTorus l k) = roots (diagonalTorus l (CommRingCat.of k)) :=
    roots_identityTorus l k
  have h₁ : (Sum.inl c : l ⊕ l) ≠ p := fun h => hca (by rw [← hp, ← h, index_inl])
  have h₂ : (Sum.inl c : l ⊕ l) ≠ p.swap := fun h => hca (by
    rw [← hp, ← index_swap p, ← h, index_inl])
  obtain ⟨i, hi⟩ : weightChar l k (Sum.inl c) + weightChar l k p ∈ Set.range P.root := by
    rw [hP.2.1, hroots]
    exact weightChar_add_mem_roots h₁ h₂
  have hpair : P.pairing i r = ν c + sgn p * ν (index x) := by
    rw [← P.root_coroot_eq_pairing, hP.1, hi, map_add, LinearMap.add_apply,
      latticePairing_weightChar, latticePairing_weightChar, index_inl, sgn_inl, one_mul, hp]
  have hmem : P.root (P.reflectionPerm r i) ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
    rw [← hroots, ← hP.2.1]
    exact ⟨_, rfl⟩
  rw [P.root_reflectionPerm, P.reflection_apply_root, hi, hr, hpair] at hmem
  set n := ν c + sgn p * ν (index x)
  have hcoord : ∀ d, GeneralLinear.characterCoordEquiv l k
      (weightChar l k (Sum.inl c) + weightChar l k p -
        n • (weightChar l k x + weightChar l k y)) d =
      weightCoord l (Sum.inl c) d + weightCoord l p d - n * (weightCoord l x d +
        weightCoord l y d) := fun d => by
    rw [map_sub, map_add, map_zsmul, map_add, characterCoordEquiv_weightChar,
      characterCoordEquiv_weightChar, characterCoordEquiv_weightChar,
      characterCoordEquiv_weightChar]
    rfl
  have h := coord_eq_zero_of_mem_roots hmem hca hcb hab
  rw [hcoord, hcoord, hcoord] at h
  simp only [weightCoord_eq_single, Pi.single_apply, index_inl, sgn_inl, hp, hca, hcb, hab,
    Ne.symm hca, Ne.symm hcb, Ne.symm hab, ite_true, ite_false] at h
  rcases h with h | h | h
  · norm_num at h
  · right
    linear_combination h
  · left
    rcases sgn_eq y with hy | hy <;> rw [hy] at h
    · linear_combination -h
    · linear_combination h

/-- **The coroots.** If `l` has three elements, the coroot of a root datum of the diagonal torus
at the root `w(x) + w(y)` is `w(x)^∨ + w(y)^∨`. -/
theorem coroot_eq_weightCochar_add {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (identityTorus l k) P)
    (hl : 3 ≤ Fintype.card l) {r : J} {x y : l ⊕ l} (h₁ : x ≠ y) (h₂ : x ≠ y.swap)
    (hr : P.root r = weightChar l k x + weightChar l k y) :
    P.coroot r = weightCochar l k x + weightCochar l k y := by
  set ν := GeneralLinear.cocharacterCoordEquiv l k (P.coroot r) with hν
  have hab : index x ≠ index y := fun h => by
    rcases eq_or_eq_swap_of_index_eq h with h | h
    · exact h₁ h
    · exact h₂ h
  have hr' : P.root r = weightChar l k y + weightChar l k x := by rw [hr, add_comm]
  -- `⟨α, α^∨⟩ = 2`.
  have htwo : sgn x * ν (index x) + sgn y * ν (index y) = 2 := by
    have h := P.pairing_same r
    rw [← P.root_coroot_eq_pairing, hP.1, hr, map_add, LinearMap.add_apply,
      latticePairing_weightChar, latticePairing_weightChar] at h
    exact h
  -- The constraints at a third index `c`.
  have hcon : ∀ c, c ≠ index x → c ≠ index y →
      (ν c + ν (index x) = 0 ∨ 1 = (ν c + ν (index x)) * sgn x) ∧
      (ν c - ν (index x) = 0 ∨ -1 = (ν c - ν (index x)) * sgn x) ∧
      (ν c + ν (index y) = 0 ∨ 1 = (ν c + ν (index y)) * sgn y) ∧
      (ν c - ν (index y) = 0 ∨ -1 = (ν c - ν (index y)) * sgn y) := by
    intro c hcx hcy
    have e₁ := coroot_constraint hP hr hab hcx hcy (Sum.inl (index x)) rfl
    have e₂ := coroot_constraint hP hr hab hcx hcy (Sum.inr (index x)) rfl
    have e₃ := coroot_constraint hP hr' (Ne.symm hab) hcy hcx (Sum.inl (index y)) rfl
    have e₄ := coroot_constraint hP hr' (Ne.symm hab) hcy hcx (Sum.inr (index y)) rfl
    simp only [sgn_inl, sgn_inr, one_mul, neg_one_mul, ← sub_eq_add_neg] at e₁ e₂ e₃ e₄
    exact ⟨e₁, e₂, e₃, e₄⟩
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({index x, index y} : Finset l)) (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₀
  have hc₀' := hcon c₀ hc₀.1 hc₀.2
  have hx : ν (index x) = sgn x ∧ ν (index y) = sgn y := by
    rcases sgn_eq x with hx | hx <;> rcases sgn_eq y with hy | hy <;> rw [hx, hy] at hc₀' htwo <;>
      rw [hx, hy] <;> omega
  apply (GeneralLinear.cocharacterCoordEquiv l k).injective
  rw [map_add, cocharacterCoordEquiv_weightCochar, cocharacterCoordEquiv_weightCochar,
    ← hν]
  funext d
  rw [Pi.add_apply]
  by_cases hdx : d = index x
  · subst hdx
    rw [weightCoord_apply_index, weightCoord_apply_of_ne y hab, add_zero, hx.1]
  by_cases hdy : d = index y
  · subst hdy
    rw [weightCoord_apply_index, weightCoord_apply_of_ne x (Ne.symm hab), zero_add, hx.2]
  rw [weightCoord_apply_of_ne x hdx, weightCoord_apply_of_ne y hdy, add_zero]
  have hd := hcon d hdx hdy
  rcases sgn_eq x with hsx | hsx <;> rcases sgn_eq y with hsy | hsy <;>
    rw [hsx, hsy] at hd hx <;> omega

end Coroot

/-! ### Almost simplicity -/

/-- With three indices, any two indices of `l ⊕ l` avoid a common third index. -/
theorem exists_ne_swap (hl : 3 ≤ Fintype.card l) (x y : l ⊕ l) :
    ∃ z : l ⊕ l, z ≠ x ∧ z ≠ x.swap ∧ z ≠ y ∧ z ≠ y.swap := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({index x, index y} : Finset l)) (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨Sum.inl c, fun h => hc.1 ?_, fun h => hc.1 ?_, fun h => hc.2 ?_, fun h => hc.2 ?_⟩ <;>
    rw [← index_inl (l := l) c, h] <;> simp

variable (l k)

/-- **Almost simplicity of the split special orthogonal group.** Over an algebraically closed
field, if `l` has at least three elements and the identity component of the split orthogonal
group `O_{2l}` is semisimple and nontrivial, it is almost simple. Its roots for the diagonal
torus are `w(x) + w(y)`, a type `D` root system. -/
theorem isAlmostSimple_identityComponent [IsAlgClosed k] (hl : 3 ≤ Fintype.card l)
    (hG : IsSemisimple (identityComponent (groupScheme l (CommRingCat.of k))))
    (hnt : SubgroupFunctor.range (𝟙 (identityComponent (groupScheme l (CommRingCat.of k)))) ≠
      ⊥) :
    IsAlmostSimple (identityComponent (groupScheme l (CommRingCat.of k))) := by
  have : IsAffineHom (identityComponent (groupScheme l (CommRingCat.of k))).X.hom :=
    hG.isConnectedReductive.isAffineHom
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence k _ hG.isConnectedReductive 𝔻
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k) (identityTorus l k)
    (isMaximalTorus_identityTorus l k)
  have hroots : roots (identityTorus l k) = roots (diagonalTorus l (CommRingCat.of k)) :=
    roots_identityTorus l k
  refine isAlmostSimple_of_typeD (t := identityTorus l k) hG
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k) (isSplitSubtorus_identityTorus l k)
    (isMaximalTorus_identityTorus l k) hnt (weightChar l k) (weightCochar l k)
    latticePairing_weightChar_weightCochar (fun χ hχ => ?_) (fun x y h₁ h₂ => ?_) hP
    (fun r x y h₁ h₂ hr => coroot_eq_weightCochar_add hP hl h₁ h₂ hr) (exists_ne_swap hl)
  · change χ ∈ roots (identityTorus l k) at hχ
    rw [hroots] at hχ
    exact exists_eq_weightChar_add_of_mem_roots hχ
  · change _ ∈ roots (identityTorus l k)
    rw [hroots]
    exact weightChar_add_mem_roots h₁ h₂

end Field

end OrthogonalMatrix

end Langlands.GroupScheme
