import Langlands.GroupScheme.SimplyConnected.NonmultipliableCorootSpanStatement
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Proof: nonmultipliable relative coroots of a simply connected group span the cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.LinearAlgebra.MinusculeLattice

open RootPairing

variable {ι M N : Type*} [Fintype ι] [AddCommGroup M] [AddCommGroup N]
  (Q : RootPairing ι ℤ M N)

/-- The canonical root form of a finite root pairing is symmetric. -/
theorem rootForm_comm (x y : M) : Q.RootForm x y = Q.RootForm y x := by
  simp only [rootForm_apply_apply, mul_comm]

/-- Invariance of the root form in coordinates: `2 (α, x) = ⟨x, α∨⟩ (α, α)`. -/
theorem two_mul_rootForm_root (i : ι) (x : M) :
    2 * Q.RootForm (Q.root i) x = Q.coroot' i x * Q.RootForm (Q.root i) (Q.root i) := by
  have h := congrArg (fun n : N => Q.toLinearMap x n) (Q.rootForm_self_smul_coroot i)
  simp only [map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  rw [Q.toLinearMap_apply_apply_Polarization] at h
  have hc : Q.toLinearMap x (Q.coroot i) = Q.coroot' i x := rfl
  rw [hc] at h
  push_cast at h
  linarith

/-- The squared length of a root for the canonical form is at least `4`. -/
theorem four_le_rootForm_root (i : ι) : 4 ≤ Q.RootForm (Q.root i) (Q.root i) := by
  rw [rootForm_root_self]
  have h : Q.pairing i i * Q.pairing i i ≤ ∑ j, Q.pairing i j * Q.pairing i j :=
    Finset.single_le_sum (f := fun j => Q.pairing i j * Q.pairing i j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [pairing_same] at h
  linarith

/-- Subtracting a root changes the canonical squared length by `-(⟨x, α∨⟩ - 1) (α, α)`. -/
theorem rootForm_sub_root (i : ι) (x : M) :
    Q.RootForm (x - Q.root i) (x - Q.root i) =
      Q.RootForm x x - (Q.coroot' i x - 1) * Q.RootForm (Q.root i) (Q.root i) := by
  have h := two_mul_rootForm_root Q i x
  have hs := rootForm_comm Q x (Q.root i)
  simp only [map_sub, LinearMap.sub_apply]
  linear_combination -hs - h

/-- Adding a root changes the canonical squared length by `(⟨x, α∨⟩ + 1) (α, α)`. -/
theorem rootForm_add_root (i : ι) (x : M) :
    Q.RootForm (x + Q.root i) (x + Q.root i) =
      Q.RootForm x x + (Q.coroot' i x + 1) * Q.RootForm (Q.root i) (Q.root i) := by
  have h := two_mul_rootForm_root Q i x
  have hs := rootForm_comm Q x (Q.root i)
  simp only [map_add, LinearMap.add_apply]
  linear_combination hs + h

/-- **Minimal representatives modulo the root lattice.** Over `ℤ`, every vector is congruent
modulo the integral root span to a vector pairing with every coroot to an integer of absolute
value at most `1`. -/
theorem exists_sub_mem_rootSpan_forall_abs_le_one (x : M) :
    ∃ y : M, x - y ∈ Q.rootSpan ℤ ∧ ∀ i, |Q.coroot' i y| ≤ 1 := by
  suffices H : ∀ n : ℕ, ∀ x : M, (Q.RootForm x x).toNat = n →
      ∃ y : M, x - y ∈ Q.rootSpan ℤ ∧ ∀ i, |Q.coroot' i y| ≤ 1 from H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases h : ∀ i, |Q.coroot' i x| ≤ 1
    · exact ⟨x, by simp, h⟩
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hF := four_le_rootForm_root Q i
    have hr : Q.root i ∈ Q.rootSpan ℤ := Submodule.subset_span ⟨i, rfl⟩
    rcases le_or_gt 0 (Q.coroot' i x) with hc | hc
    · rw [abs_of_nonneg hc] at hi
      have h1 : 0 ≤ Q.RootForm (x - Q.root i) (x - Q.root i) := Q.zero_le_rootForm _
      have hkey := rootForm_sub_root Q i x
      have hlt : (Q.RootForm (x - Q.root i) (x - Q.root i)).toNat < n := by
        rw [← hx]
        have hm : 1 * Q.RootForm (Q.root i) (Q.root i) ≤
            (Q.coroot' i x - 1) * Q.RootForm (Q.root i) (Q.root i) :=
          mul_le_mul_of_nonneg_right (by omega) (by omega)
        omega
      obtain ⟨y, hy, hy'⟩ := ih _ hlt (x - Q.root i) rfl
      refine ⟨y, ?_, hy'⟩
      have he : x - y = (x - Q.root i - y) + Q.root i := by abel
      rw [he]
      exact add_mem hy hr
    · rw [abs_of_neg hc] at hi
      have h1 : 0 ≤ Q.RootForm (x + Q.root i) (x + Q.root i) := Q.zero_le_rootForm _
      have hkey := rootForm_add_root Q i x
      have hlt : (Q.RootForm (x + Q.root i) (x + Q.root i)).toNat < n := by
        rw [← hx]
        have hm : (Q.coroot' i x + 1) * Q.RootForm (Q.root i) (Q.root i) ≤
            (-1) * Q.RootForm (Q.root i) (Q.root i) :=
          mul_le_mul_of_nonneg_right (by omega) (by omega)
        omega
      obtain ⟨y, hy, hy'⟩ := ih _ hlt (x + Q.root i) rfl
      refine ⟨y, ?_, hy'⟩
      have he : x - y = (x + Q.root i - y) - Q.root i := by abel
      rw [he]
      exact sub_mem hy hr

/-- The canonical form of an integral combination of roots, expanded in the first variable. -/
theorem rootForm_sum_smul_root (n : ι → ℤ) (y : M) :
    Q.RootForm (∑ j, n j • Q.root j) y = ∑ j, n j * Q.RootForm (Q.root j) y := by
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]

/-- **No nonzero minuscule vector in the root lattice.** Over `ℤ`, a vector of the integral root
span pairing with every coroot to an integer of absolute value at most `1` is zero. -/
theorem eq_zero_of_mem_rootSpan_of_forall_abs_le_one {x : M} (hx : x ∈ Q.rootSpan ℤ)
    (h : ∀ i, |Q.coroot' i x| ≤ 1) : x = 0 := by
  classical
  obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  suffices H : ∀ m : ℕ, ∀ n : ι → ℤ, (∑ j, |n j|).toNat = m →
      (∀ i, |Q.coroot' i (∑ j, n j • Q.root j)| ≤ 1) → ∑ j, n j • Q.root j = 0 from
    H _ n rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm hn
    by_contra hne
    have hxs : ∑ j, n j • Q.root j ∈ Q.rootSpan ℤ :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hpos := Q.rootForm_pos_of_ne_zero hxs hne
    rw [rootForm_sum_smul_root] at hpos
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ,
        0 < n i * Q.RootForm (Q.root i) (∑ j, n j • Q.root j) := by
      by_contra hall
      push Not at hall
      exact absurd (Finset.sum_nonpos hall) (not_le.mpr hpos)
    set x := ∑ j, n j • Q.root j with hxdef
    set c := Q.coroot' i x with hcdef
    have hF := four_le_rootForm_root Q i
    have h2 := two_mul_rootForm_root Q i x
    rw [← hcdef] at h2
    have hnc : 0 < n i * c := by
      by_contra hle
      push Not at hle
      have : n i * c * Q.RootForm (Q.root i) (Q.root i) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle (by omega)
      have h3 : 2 * (n i * Q.RootForm (Q.root i) x) =
          n i * c * Q.RootForm (Q.root i) (Q.root i) := by
        linear_combination n i * h2
      linarith
    have hc1 : |c| ≤ 1 := hn i
    -- the new coefficients
    let n' : ι → ℤ := fun j => n j - if j = i then c else 0
    have hx' : ∑ j, n' j • Q.root j = Q.reflection i x := by
      rw [reflection_apply, ← hcdef]
      simp only [n', sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    have hcoef : |n' i| + 1 = |n i| := by
      have hc0 : c ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hnc
        exact lt_irrefl _ hnc
      have hc' : c = 1 ∨ c = -1 := by
        rcases abs_le.mp hc1 with ⟨h1, h2⟩
        omega
      have hn'i : n' i = n i - c := by simp [n']
      rcases hc' with h | h <;> rw [h] at hnc hn'i <;>
      rcases abs_cases (n' i) with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
      rcases abs_cases (n i) with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
      linarith
    have hsum : (∑ j, |n' j|) + 1 = ∑ j, |n j| := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, |n' j| = ∑ j ∈ Finset.univ.erase i, |n j| := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [n', Finset.ne_of_mem_erase hj]
      rw [hrest]
      linarith
    have hnn : 0 ≤ ∑ j, |n' j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hlt : (∑ j, |n' j|).toNat < m := by
      rw [← hm]
      omega
    have hn' : ∀ j, |Q.coroot' j (∑ j, n' j • Q.root j)| ≤ 1 := by
      intro j
      rw [hx', coroot'_reflection]
      exact hn _
    have hzero := ih _ hlt n' rfl hn'
    rw [hx'] at hzero
    exact hne ((Q.reflection i).map_eq_zero_iff.mp hzero)

/-- Coroot form of `exists_sub_mem_rootSpan_forall_abs_le_one`. -/
theorem exists_sub_mem_corootSpan_forall_abs_le_one (x : N) :
    ∃ y : N, x - y ∈ Q.corootSpan ℤ ∧ ∀ i, |Q.root' i y| ≤ 1 :=
  exists_sub_mem_rootSpan_forall_abs_le_one Q.flip x

/-- Coroot form of `eq_zero_of_mem_rootSpan_of_forall_abs_le_one`. -/
theorem eq_zero_of_mem_corootSpan_of_forall_abs_le_one {x : N} (hx : x ∈ Q.corootSpan ℤ)
    (h : ∀ i, |Q.root' i x| ≤ 1) : x = 0 :=
  eq_zero_of_mem_rootSpan_of_forall_abs_le_one Q.flip hx h

end Langlands.LinearAlgebra.MinusculeLattice

namespace Langlands.GroupScheme

namespace NonmultipliableCorootSpan

/-- If a finite set `s` contains `2 • a` whenever a member `a` has `|g a| > 1`, then every
member `c` has `|g c| ≤ 1`: otherwise `s` would contain all `2 ^ n • c`. -/
theorem abs_le_one_of_doubling {X : Type*} [AddCommGroup X] (g : X →ₗ[ℤ] ℤ) {s : Set X}
    (hs : s.Finite) (h : ∀ a ∈ s, (2 : ℤ) • a ∉ s → |g a| ≤ 1) {c : X} (hc : c ∈ s) :
    |g c| ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hval : ∀ n : ℕ, g (((2 : ℤ) ^ n) • c) = 2 ^ n * g c := fun n => by
    rw [map_zsmul, smul_eq_mul]
  have hmem : ∀ n : ℕ, ((2 : ℤ) ^ n) • c ∈ s := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ihn =>
      by_contra hn
      have h2 : (2 : ℤ) • (((2 : ℤ) ^ n) • c) ∉ s := by
        rwa [smul_smul, ← pow_succ']
      have hle := h _ ihn h2
      rw [hval, abs_mul, abs_pow, abs_two] at hle
      have hp : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith [abs_nonneg (g c)]
  have hgc : g c ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgt
    omega
  have hinj : Function.Injective (fun n : ℕ => ((2 : ℤ) ^ n) • c) := by
    intro a b hab
    have h' := congrArg g hab
    simp only [hval] at h'
    have h'' : (2 : ℤ) ^ a = 2 ^ b := mul_right_cancel₀ hgc h'
    have h''' : (2 : ℕ) ^ a = 2 ^ b := by exact_mod_cast h''
    exact Nat.pow_right_injective (le_refl 2) h'''
  exact Set.infinite_of_injective_forall_mem hinj hmem hs

end NonmultipliableCorootSpan

open NonmultipliableCorootSpan Langlands.LinearAlgebra.MinusculeLattice in
/-- **Borel–Tits (1972), 4.3 (ii)′ and 4.4, lattice form.** The integral coroots of any root
datum on the lattices of a maximal split torus of a simply connected group, with the lattice
pairing and with exactly the nonmultipliable relative roots as roots, span the cocharacter
lattice. -/
theorem nonmultipliableCorootSpan : NonmultipliableCorootSpanStatement.{u} := by
  intro k _ G hG S i hi J P hpair hroots _hrefl
  have hCR := hG.isSemisimple.isConnectedReductive
  have := hCR.smooth
  have := hCR.isAffineHom
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hfin : (roots i).Finite := hS.finite_relativeRoots i
  -- finiteness of the index type of `P`
  have hrange : (Set.range P.root).Finite :=
    hfin.subset (by rw [hroots]; exact fun a ha => ha.1)
  have : Finite J := (Set.finite_range_iff P.root.injective).mp hrange
  let : Fintype J := Fintype.ofFinite J
  -- a maximal torus containing `S`, split over a field `K`
  obtain ⟨M, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hS.isTorus hi.1.2
  obtain ⟨K, _, _, hMK⟩ := hj.1
  let b := algebraBaseMap k K
  have hGK : IsConnectedReductive ((GroupScheme.baseChange b).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hCR
  have hjK : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj M)
      ((GroupScheme.baseChange b).map j) :=
    (maximalTorusBaseChange k K G M j hj.1 hj.2.1).mp hj
  have := hGK.isAffineHom
  obtain ⟨J', _, Q, hQ, hred⟩ := rootDatumExistence K _ hGK _ hMK _ hjK
  let : Fintype J' := Fintype.ofFinite J'
  have hscK : IsSimplyConnected ((GroupScheme.baseChange b).obj G) :=
    isSimplyConnectedFieldExtension k K G hG
  have hspan : Q.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan K _ hscK _ hMK _ hjK J' Q hQ hred
  -- the torus map over `K` and the restriction of absolute roots
  let fK : (CommGroupScheme.baseChange b).obj S ⟶ (CommGroupScheme.baseChange b).obj M :=
    (CommGroupScheme.baseChange b).map (Additive.ofMul f)
  let r : J' → characterLattice S := fun a =>
    (characterLattice.baseChangeEquiv b S hS).symm (fK ≫ Q.root a)
  have hpairQ : ∀ (a : J') (μ : cocharacterLattice S),
      Q.root' a (RealTorusSpace.cocharacterMapInt fK (cocharacterLattice.baseChange b S μ)) =
        P.toLinearMap (r a) μ := by
    intro a μ
    rw [hpair, TitsIndexExistence.latticePairing_restriction hS (Additive.ofMul f) (Q.root a) μ,
      ← hQ.1]
    rfl
  have hr : ∀ a, r a = 0 ∨ r a ∈ roots i := by
    intro a
    by_cases h0 : r a = 0
    · exact Or.inl h0
    right
    have hβ : Q.root a ∈ roots ((GroupScheme.baseChange b).map j) := by
      rw [← hQ.2.1]
      exact Set.mem_range_self a
    have hmem := (mem_roots_iff_exists_splittingField_restriction (K := K) hS hMK
      (Additive.ofMul f) j (r a)).mpr ⟨h0, Q.root a, hβ, by
        rw [← characterLattice.baseChangeEquiv_apply b S hS, AddEquiv.apply_symm_apply]⟩
    have hfi : CommGroupScheme.groupHom (Additive.ofMul f) ≫ j = i := hf
    rwa [hfi] at hmem
  -- injectivity of the cocharacter map `X_*(S) → X_*(M_K)`
  have hcl : IsClosedSubgroup ((GroupScheme.baseChange b).map i) := hi.1.2.baseChange b
  have hcomp : (GroupScheme.baseChange b).map i =
      CommGroupScheme.groupHom fK ≫ (GroupScheme.baseChange b).map j := by
    rw [← hf, Functor.map_comp]
    rfl
  have : Mono (CommGroupScheme.groupHom fK).hom.hom.left := by
    have hm : Mono ((GroupScheme.baseChange b).map i).hom.hom.left := hcl.mono
    rw [hcomp] at hm
    have hm' : Mono ((CommGroupScheme.groupHom fK).hom.hom.left ≫
        ((GroupScheme.baseChange b).map j).hom.hom.left) := hm
    exact mono_of_mono _ ((GroupScheme.baseChange b).map j).hom.hom.left
  have hinj1 := RealTorusSpace.cocharacterMapInt_injective fK
  have hinj2 := hS.cocharacterLattice_baseChange_bijective b S |>.1
  -- bound on all relative roots for a minimal representative
  have hbound : ∀ μ : cocharacterLattice S, (∀ c : J, |P.root' c μ| ≤ 1) →
      ∀ a ∈ roots i, |P.toLinearMap a μ| ≤ 1 := by
    intro μ hμ a ha
    refine abs_le_one_of_doubling (P.toLinearMap.flip μ) hfin ?_ ha
    intro a' ha' h2
    have hmem : a' ∈ Set.range P.root := by
      rw [hroots]
      exact ⟨ha', h2⟩
    obtain ⟨c, rfl⟩ := hmem
    exact hμ c
  -- main argument
  rw [eq_top_iff]
  intro x _
  obtain ⟨μ, hμ, hμ'⟩ := exists_sub_mem_corootSpan_forall_abs_le_one P x
  have hK : RealTorusSpace.cocharacterMapInt fK (cocharacterLattice.baseChange b S μ) = 0 := by
    apply eq_zero_of_mem_corootSpan_of_forall_abs_le_one Q
    · rw [hspan]
      exact Submodule.mem_top
    · intro a
      rw [hpairQ]
      rcases hr a with h0 | hroot
      · rw [h0, map_zero, LinearMap.zero_apply, abs_zero]
        exact zero_le_one
      · exact hbound μ hμ' _ hroot
  have hμ0 : μ = 0 := by
    have h1 : cocharacterLattice.baseChange b S μ = 0 :=
      (injective_iff_map_eq_zero _).mp hinj1 _ hK
    exact (injective_iff_map_eq_zero (cocharacterLattice.baseChange b S)).mp hinj2 _ h1
  rw [hμ0, sub_zero] at hμ
  exact hμ

end Langlands.GroupScheme
