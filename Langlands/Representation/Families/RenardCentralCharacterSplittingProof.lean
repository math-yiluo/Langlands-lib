import Langlands.Representation.Families.RenardCentralCharacterSplittingStatement
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Module

/-!
# Proof of Renard VI.8.5 Lemma: filtrations with distinct central characters split

For each index `i`, a product of operators `ρ z - χ j z`, with `z` a central element
separating `χ i` from `χ j` for each `j ≠ i`, is rescaled to an equivariant operator that is
the identity on the `χ i`-eigenvectors and zero on the `χ j`-eigenvectors. Induction along
the filtration shows that the eigen-subrepresentations span the representation, that the
operators are complementary projections onto them, and that each eigen-subrepresentation
maps isomorphically onto its graded quotient. These maps form a bicone, which is a
biproduct and hence a coproduct.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AlgebraicFamily

universe uk uG uV

namespace CentralCharacterSplittingProof

section Operators

variable {k : Type uk} [Field k] {G : Type uG} [Group G] {Z : Subgroup G}
  {V : Type uV} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The composite of the operators `ρ z - a` over a list of pairs `(z, a)`; the last pair
acts first. -/
def factorProduct : List (Z × k) → Module.End k V
  | [] => 1
  | p :: L => (ρ p.1 - p.2 • 1) * factorProduct L

/-- The scalar `∏ (ψ z - a)` by which `factorProduct` acts on the eigenvectors of `ψ`. -/
def factorValue (ψ : Z →* kˣ) (L : List (Z × k)) : k :=
  (L.map fun p => ((ψ p.1 : kˣ) : k) - p.2).prod

theorem factorProduct_cons_apply (p : Z × k) (L : List (Z × k)) (v : V) :
    factorProduct ρ (p :: L) v =
      ρ p.1 (factorProduct ρ L v) - p.2 • factorProduct ρ L v := by
  simp [factorProduct]

theorem factorValue_cons (ψ : Z →* kˣ) (p : Z × k) (L : List (Z × k)) :
    factorValue ψ (p :: L) = (((ψ p.1 : kˣ) : k) - p.2) * factorValue ψ L := by
  simp [factorValue]

/-- Since `Z` is central, `factorProduct` commutes with the action of `G`. -/
theorem commute_factorProduct (hZ : Z ≤ Subgroup.center G) (g : G) :
    ∀ L : List (Z × k), Commute (ρ g) (factorProduct ρ L)
  | [] => Commute.one_right _
  | p :: L => by
      have h : Commute (ρ g) (ρ p.1) := by
        change ρ g * ρ p.1 = ρ p.1 * ρ g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ p.1.2) g]
      exact (h.sub_right ((Commute.one_right _).smul_right _)).mul_right
        (commute_factorProduct hZ g L)

/-- If `Z` acts through `ψ` on `v` modulo a `Z`-stable submodule `W`, then
`factorProduct` acts on `v` by `factorValue` modulo `W`. -/
theorem factorProduct_sub_smul_mem (W : Submodule k V)
    (hW : ∀ (y : Z), ∀ w ∈ W, ρ y w ∈ W) (ψ : Z →* kˣ) {v : V}
    (hv : ∀ y : Z, ρ y v - ((ψ y : kˣ) : k) • v ∈ W) :
    ∀ L : List (Z × k), factorProduct ρ L v - factorValue ψ L • v ∈ W
  | [] => by simp [factorProduct, factorValue]
  | p :: L => by
      obtain ⟨u, hu, hF⟩ : ∃ u ∈ W, factorProduct ρ L v = u + factorValue ψ L • v :=
        ⟨_, factorProduct_sub_smul_mem W hW ψ hv L, (sub_add_cancel _ _).symm⟩
      have key : factorProduct ρ (p :: L) v - factorValue ψ (p :: L) • v =
          (ρ p.1 u - p.2 • u) + factorValue ψ L • (ρ p.1 v - ((ψ p.1 : kˣ) : k) • v) := by
        rw [factorProduct_cons_apply, factorValue_cons, hF, map_add, map_smul]
        module
      rw [key]
      exact W.add_mem (W.sub_mem (hW _ _ hu) (W.smul_mem _ hu)) (W.smul_mem _ (hv _))

/-- On an eigenvector of `ψ`, `factorProduct` acts by `factorValue`. -/
theorem factorProduct_apply_of_eigen (ψ : Z →* kˣ) {v : V}
    (hv : ∀ y : Z, ρ y v = ((ψ y : kˣ) : k) • v) (L : List (Z × k)) :
    factorProduct ρ L v = factorValue ψ L • v := by
  have h := factorProduct_sub_smul_mem ρ ⊥
    (fun y w hw => by rw [(Submodule.mem_bot k).mp hw, map_zero]; exact Submodule.zero_mem _)
    ψ (v := v) (fun y => by rw [hv y, sub_self]; exact Submodule.zero_mem _) L
  exact sub_eq_zero.mp ((Submodule.mem_bot k).mp h)

open Classical in
/-- A point of `Z` at which two characters differ, or `1` if they are equal. -/
def separatingPoint (ψ φ : Z →* kˣ) : Z :=
  if h : ψ = φ then 1 else (DFunLike.ne_iff.mp h).choose

theorem separatingPoint_spec {ψ φ : Z →* kˣ} (h : ψ ≠ φ) :
    ((ψ (separatingPoint ψ φ) : kˣ) : k) ≠ φ (separatingPoint ψ φ) := by
  have hs := (DFunLike.ne_iff.mp h).choose_spec
  have he : separatingPoint ψ φ = (DFunLike.ne_iff.mp h).choose := by
    simp [separatingPoint, h]
  rw [he]
  exact fun he => hs (Units.val_injective he)

end Operators

section Filtration

variable {k : Type uk} [Field k] {G : Type uG} [Group G] {Z : Subgroup G}
  (hZ : Z ≤ Subgroup.center G) {A : Rep.{uV} k G} {n : ℕ} (s : ObjectRepFiltration A n)
  (χ : Fin n → Z →* kˣ) (hχ : Function.Injective χ)
  (hgr : ∀ (i : Fin n) (z : Z) (v : s.gradedRepresentation i),
    (s.gradedRepresentation i).ρ (z : G) v = ((χ i z : kˣ) : k) • v)

/-- The vectors on which `Z` acts through the character `ψ`. Since `Z` is central, this is
a subrepresentation. -/
def charSubrep (A : Rep.{uV} k G) (hZ : Z ≤ Subgroup.center G) (ψ : Z →* kˣ) :
    Subrepresentation A.ρ where
  toSubmodule :=
    { carrier := {v | ∀ y : Z, A.ρ (y : G) v = ((ψ y : kˣ) : k) • v}
      add_mem' := fun {a b} ha hb y => by
        change A.ρ (y : G) (a + b) = _
        rw [map_add, ha y, hb y, smul_add]
      zero_mem' := fun y => by simp
      smul_mem' := fun c v hv y => by
        change A.ρ (y : G) (c • v) = _
        rw [map_smul, hv y, smul_comm] }
  apply_mem_toSubmodule g v hv y := by
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.mp (hZ y.2) g, map_mul,
      Module.End.mul_apply, hv y, map_smul]

/-- The pairs `(z, χ j z)` for `j ≠ i`, where `z` separates `χ i` from `χ j`. -/
def factorList (i : Fin n) : List (Z × k) :=
  ((List.finRange n).filter (fun j => j ≠ i)).map
    (fun j => (separatingPoint (χ i) (χ j), ((χ j (separatingPoint (χ i) (χ j)) : kˣ) : k)))

theorem factorValue_factorList_of_ne {i j : Fin n} (h : j ≠ i) :
    factorValue (χ j) (factorList χ i) = 0 := by
  apply List.prod_eq_zero
  rw [List.mem_map]
  refine ⟨(separatingPoint (χ i) (χ j), ((χ j (separatingPoint (χ i) (χ j)) : kˣ) : k)),
    ?_, sub_self _⟩
  rw [factorList, List.mem_map]
  exact ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using h⟩, rfl⟩

include hχ in
theorem factorValue_factorList_self (i : Fin n) :
    factorValue (χ i) (factorList χ i) ≠ 0 := by
  apply List.prod_ne_zero
  intro h0
  rw [List.mem_map] at h0
  obtain ⟨p, hp, hp0⟩ := h0
  rw [factorList, List.mem_map] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hji : j ≠ i := by simpa using (List.mem_filter.mp hj).2
  exact separatingPoint_spec (fun h => hji (hχ h).symm) (sub_eq_zero.mp hp0)

/-- The rescaled product: the identity on the `χ i`-eigenvectors and zero on the
`χ j`-eigenvectors for `j ≠ i`. -/
def proj (A : Rep.{uV} k G) (χ : Fin n → Z →* kˣ) (i : Fin n) : Module.End k A :=
  (factorValue (χ i) (factorList χ i))⁻¹ • factorProduct A.ρ (factorList χ i)

theorem proj_apply_of_mem_ne {i j : Fin n} (h : j ≠ i) {v : A}
    (hv : v ∈ (charSubrep A hZ (χ j)).toSubmodule) : proj A χ i v = 0 := by
  rw [proj, LinearMap.smul_apply, factorProduct_apply_of_eigen A.ρ (χ j) hv,
    factorValue_factorList_of_ne χ h, zero_smul, smul_zero]

/-- `proj A χ i` vanishes on the eigen-subrepresentations of the earlier indices. -/
theorem proj_apply_of_mem_iSup_lt (i : Fin n) {w : A}
    (hw : w ∈ ⨆ (j : Fin n) (_ : j.val < i.val), (charSubrep A hZ (χ j)).toSubmodule) :
    proj A χ i w = 0 := by
  have hle : ⨆ (j : Fin n) (_ : j.val < i.val), (charSubrep A hZ (χ j)).toSubmodule ≤
      LinearMap.ker (proj A χ i) :=
    iSup₂_le fun j hj x hx => LinearMap.mem_ker.mpr
      (proj_apply_of_mem_ne hZ χ (Fin.ne_of_val_ne (Nat.ne_of_lt hj)) hx)
  exact LinearMap.mem_ker.mp (hle hw)

include hχ in
theorem proj_apply_of_mem_self (i : Fin n) {v : A}
    (hv : v ∈ (charSubrep A hZ (χ i)).toSubmodule) : proj A χ i v = v := by
  rw [proj, LinearMap.smul_apply, factorProduct_apply_of_eigen A.ρ (χ i) hv,
    inv_smul_smul₀ (factorValue_factorList_self χ hχ i)]

include hZ in
theorem proj_apply_rho (i : Fin n) (g : G) (v : A) :
    proj A χ i (A.ρ g v) = A.ρ g (proj A χ i v) := by
  have h := congrArg (fun T : Module.End k A => T v)
    (commute_factorProduct A.ρ hZ g (factorList χ i)).eq
  simp only [Module.End.mul_apply] at h
  rw [proj, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]

include hχ hgr in
/-- On the step above the `i`th graded quotient, `proj A χ i` is the identity modulo the
step below. -/
theorem proj_sub_mem (i : Fin n) {v : A} (hv : v ∈ (s.subrepresentation i.succ).toSubmodule) :
    proj A χ i v - v ∈ (s.subrepresentation i.castSucc).toSubmodule := by
  set W := (s.subrepresentation i.castSucc).toSubmodule
  have hW : ∀ (y : Z), ∀ w ∈ W, A.ρ (y : G) w ∈ W := fun y _ hw =>
    (s.subrepresentation i.castSucc).apply_mem_toSubmodule (y : G) hw
  have hv' : ∀ y : Z, A.ρ (y : G) v - ((χ i y : kˣ) : k) • v ∈ W := fun y =>
    CentralEigenspaceSplitting.sub_smul_mem_of_graded s (y : G) (fun j => ((χ j y : kˣ) : k))
      (fun j w => hgr j y w) i hv
  have h := W.smul_mem (factorValue (χ i) (factorList χ i))⁻¹
    (factorProduct_sub_smul_mem A.ρ W hW (χ i) hv' (factorList χ i))
  rwa [smul_sub, inv_smul_smul₀ (factorValue_factorList_self χ hχ i)] at h

include hχ hgr in
/-- Each step of the filtration is contained in the sum of the eigen-subrepresentations of
the earlier graded quotients. -/
theorem le_iSup_charSubrep : ∀ (m : ℕ) (hm : m ≤ n),
    (s.subrepresentation ⟨m, Nat.lt_succ_of_le hm⟩).toSubmodule ≤
      ⨆ (j : Fin n) (_ : j.val < m), (charSubrep A hZ (χ j)).toSubmodule
  | 0, _ => by
      intro v hv
      change v ∈ s.subrepresentation 0 at hv
      rw [s.subrepresentation_zero, CentralEigenspaceSplitting.mem_bot_iff] at hv
      rw [hv]
      exact Submodule.zero_mem _
  | m + 1, hm => by
      intro v hv
      let i : Fin n := ⟨m, hm⟩
      have IH := le_iSup_charSubrep m (Nat.le_of_succ_le hm)
      have hvi : v ∈ (s.subrepresentation i.succ).toSubmodule := hv
      have hu : proj A χ i v ∈ (charSubrep A hZ (χ i)).toSubmodule := by
        intro y
        have hw := CentralEigenspaceSplitting.sub_smul_mem_of_graded s (y : G)
          (fun j => ((χ j y : kˣ) : k)) (fun j w => hgr j y w) i hvi
        have h0 := proj_apply_of_mem_iSup_lt hZ χ i (IH hw)
        rw [map_sub, map_smul, proj_apply_rho hZ χ i (y : G) v] at h0
        exact sub_eq_zero.mp h0
      have hr : v - proj A χ i v ∈ ⨆ (j : Fin n) (_ : j.val < m),
          (charSubrep A hZ (χ j)).toSubmodule := by
        apply IH
        rw [← neg_sub]
        exact Submodule.neg_mem _ (proj_sub_mem s χ hχ hgr i hvi)
      rw [← add_sub_cancel (proj A χ i v) v]
      apply Submodule.add_mem
      · exact (le_iSup₂ (f := fun (j : Fin n) (_ : j.val < m + 1) =>
          (charSubrep A hZ (χ j)).toSubmodule) i (Nat.lt_succ_self m)) hu
      · exact (biSup_mono (f := fun j : Fin n => (charSubrep A hZ (χ j)).toSubmodule)
          fun j hj => Nat.lt_succ_of_lt hj) hr

include hχ hgr in
theorem iSup_charSubrep_eq_top : ⨆ j, (charSubrep A hZ (χ j)).toSubmodule = ⊤ := by
  have h := le_iSup_charSubrep hZ s χ hχ hgr n le_rfl
  apply eq_top_iff.mpr
  intro v _
  have hv : v ∈ (s.subrepresentation (Fin.last n)).toSubmodule := by
    rw [s.subrepresentation_last]
    exact CentralEigenspaceSplitting.mem_top v
  exact (iSup₂_le fun j _ => le_iSup (fun j => (charSubrep A hZ (χ j)).toSubmodule) j) (h hv)

include hχ hgr in
theorem proj_mem (i : Fin n) (v : A) : proj A χ i v ∈ (charSubrep A hZ (χ i)).toSubmodule := by
  have hv : v ∈ ⨆ j, (charSubrep A hZ (χ j)).toSubmodule := by
    rw [iSup_charSubrep_eq_top hZ s χ hχ hgr]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => proj A χ i w ∈
    (charSubrep A hZ (χ i)).toSubmodule) hv ?_ ?_ ?_
  · intro j w hw
    by_cases h : j = i
    · subst h
      rw [proj_apply_of_mem_self hZ χ hχ j hw]
      exact hw
    · rw [proj_apply_of_mem_ne hZ χ h hw]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

include hZ hχ hgr in
theorem sum_proj (v : A) : ∑ i, proj A χ i v = v := by
  have hv : v ∈ ⨆ j, (charSubrep A hZ (χ j)).toSubmodule := by
    rw [iSup_charSubrep_eq_top hZ s χ hχ hgr]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => ∑ i, proj A χ i w = w) hv ?_ ?_ ?_
  · intro j w hw
    rw [Finset.sum_eq_single j (fun i _ hij => proj_apply_of_mem_ne hZ χ (Ne.symm hij) hw)
      (fun h => absurd (Finset.mem_univ j) h)]
    exact proj_apply_of_mem_self hZ χ hχ j hw
  · simp
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

include hχ hgr in
/-- The `χ i`-eigen-subrepresentation lies in the step above the `i`th graded quotient. -/
theorem charSubrep_le (i : Fin n) :
    (charSubrep A hZ (χ i)).toSubmodule ≤ (s.subrepresentation i.succ).toSubmodule := by
  intro v hv
  have step : ∀ j : Fin n, i ≠ j → v ∈ (s.subrepresentation j.succ).toSubmodule →
      v ∈ (s.subrepresentation j.castSucc).toSubmodule := by
    intro j hij hvj
    have h := proj_sub_mem s χ hχ hgr j hvj
    rw [proj_apply_of_mem_ne hZ χ hij hv, zero_sub] at h
    simpa using Submodule.neg_mem _ h
  have key : ∀ (d : ℕ) (m : Fin (n + 1)), m.val + d = n → i.val < m.val →
      v ∈ (s.subrepresentation m).toSubmodule := by
    intro d
    induction d with
    | zero =>
        intro m hmd _
        obtain rfl : m = Fin.last n := Fin.ext (by simpa using hmd)
        rw [s.subrepresentation_last]
        exact CentralEigenspaceSplitting.mem_top v
    | succ d ih =>
        intro m hmd him
        let j : Fin n := ⟨m.val, by omega⟩
        have hj : v ∈ (s.subrepresentation j.succ).toSubmodule :=
          ih j.succ (by show m.val + 1 + d = n; omega) (by show i.val < m.val + 1; omega)
        exact step j (Fin.ne_of_val_ne (Nat.ne_of_lt him)) hj
  exact key (n - (i.val + 1)) i.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega)

/-- The graded projection restricted to the `χ i`-eigen-subrepresentation. -/
def gradedHom (i : Fin n) :
    (charSubrep A hZ (χ i)).toRepresentation.IntertwiningMap (s.gradedRepresentation i).ρ where
  toLinearMap := (s.gradedProjection i).hom.toLinearMap ∘ₗ
    Submodule.inclusion (charSubrep_le hZ s χ hχ hgr i)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact Rep.hom_comm_apply (s.gradedProjection i) g
      (Submodule.inclusion (charSubrep_le hZ s χ hχ hgr i) v)

theorem gradedHom_apply (i : Fin n) (v : (charSubrep A hZ (χ i)).toSubmodule) :
    gradedHom hZ s χ hχ hgr i v =
      (s.gradedProjection i).hom (Submodule.inclusion (charSubrep_le hZ s χ hχ hgr i) v) :=
  rfl

theorem gradedHom_bijective (i : Fin n) : Function.Bijective (gradedHom hZ s χ hχ hgr i) := by
  constructor
  · refine (injective_iff_map_eq_zero (gradedHom hZ s χ hχ hgr i)).mpr fun v hv => ?_
    have h0 : (s.gradedProjection i).hom
        (Submodule.inclusion (charSubrep_le hZ s χ hχ hgr i) v) = 0 := hv
    rw [CentralEigenspaceSplitting.gradedProjection_eq_zero_iff] at h0
    have hle := le_iSup_charSubrep hZ s χ hχ hgr i.val (Nat.le_of_lt i.isLt) h0
    have hz : proj A χ i v = 0 := proj_apply_of_mem_iSup_lt hZ χ i hle
    rw [proj_apply_of_mem_self hZ χ hχ i v.2] at hz
    exact Subtype.ext hz
  · intro x
    obtain ⟨w, rfl⟩ := s.gradedProjection_surjective i x
    refine ⟨⟨proj A χ i w, proj_mem hZ s χ hχ hgr i w⟩, ?_⟩
    rw [gradedHom_apply, ← sub_eq_zero, ← map_sub,
      CentralEigenspaceSplitting.gradedProjection_eq_zero_iff]
    exact proj_sub_mem s χ hχ hgr i w.2

/-- The `χ i`-eigen-subrepresentation is equivalent to the `i`th graded quotient. -/
def gradedEquiv (i : Fin n) :
    (charSubrep A hZ (χ i)).toRepresentation.Equiv (s.gradedRepresentation i).ρ :=
  (gradedHom hZ s χ hχ hgr i).ofBijective (gradedHom_bijective hZ s χ hχ hgr i)

theorem gradedEquiv_symm_apply_gradedHom (i : Fin n)
    (v : (charSubrep A hZ (χ i)).toSubmodule) :
    (gradedEquiv hZ s χ hχ hgr i).symm (gradedHom hZ s χ hχ hgr i v) = v :=
  (gradedEquiv hZ s χ hχ hgr i).symm_apply_apply v

/-- `proj A χ i` as an intertwining map onto the `χ i`-eigen-subrepresentation. -/
def projHom (i : Fin n) : A.ρ.IntertwiningMap (charSubrep A hZ (χ i)).toRepresentation where
  toLinearMap := LinearMap.codRestrict _ (proj A χ i) (proj_mem hZ s χ hχ hgr i)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact Subtype.ext (proj_apply_rho hZ χ i g v)

/-- The bicone of the splitting: the vertex is `A`, the projections are `projHom` followed
by `gradedEquiv`, and the inclusions are the inverse of `gradedEquiv` followed by the
inclusion of the eigen-subrepresentation. -/
def splittingBicone : Bicone (fun i => s.gradedRepresentation i) where
  pt := A
  π i := ConcreteCategory.ofHom (C := Rep k G)
    ((gradedHom hZ s χ hχ hgr i).comp (projHom hZ s χ hχ hgr i))
  ι i := ConcreteCategory.ofHom (C := Rep k G)
    ((CentralEigenspaceSplitting.subrepInclusion (charSubrep A hZ (χ i))).comp
      (gradedEquiv hZ s χ hχ hgr i).symm.toIntertwiningMap)
  ι_π i j := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    set u := (gradedEquiv hZ s χ hχ hgr i).symm x with hu
    have hx : x = gradedHom hZ s χ hχ hgr i u := by
      rw [hu]
      exact ((gradedEquiv hZ s χ hχ hgr i).apply_symm_apply x).symm
    split_ifs with h
    · subst h
      rw [eqToHom_refl]
      change gradedHom hZ s χ hχ hgr i
        ⟨proj A χ i (u : A), proj_mem hZ s χ hχ hgr i (u : A)⟩ = x
      rw [hx]
      congr 1
      exact Subtype.ext (proj_apply_of_mem_self hZ χ hχ i u.2)
    · change gradedHom hZ s χ hχ hgr j
        ⟨proj A χ j (u : A), proj_mem hZ s χ hχ hgr j (u : A)⟩ = 0
      have h0 : (⟨proj A χ j (u : A), proj_mem hZ s χ hχ hgr j (u : A)⟩ :
          (charSubrep A hZ (χ j)).toSubmodule) = 0 :=
        Subtype.ext (proj_apply_of_mem_ne hZ χ h u.2)
      rw [h0, map_zero]

theorem splittingBicone_total :
    ∑ j, (splittingBicone hZ s χ hχ hgr).π j ≫ (splittingBicone hZ s χ hχ hgr).ι j =
      𝟙 (splittingBicone hZ s χ hχ hgr).pt := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  change ∑ j, ((gradedEquiv hZ s χ hχ hgr j).symm
    (gradedHom hZ s χ hχ hgr j ⟨proj A χ j v, proj_mem hZ s χ hχ hgr j v⟩) : A) = v
  simp only [gradedEquiv_symm_apply_gradedHom]
  exact sum_proj hZ s χ hχ hgr v

end Filtration

end CentralCharacterSplittingProof

open CentralCharacterSplittingProof in
/-- Renard VI.8.5 Lemma: a finite filtration whose graded quotients have pairwise distinct
central characters splits as the coproduct of its graded quotients. -/
theorem centralCharacterSplitting : CentralCharacterSplittingStatement.{uk, uG, uV} := by
  intro k _ G _ Z hZ A n s χ hχ hgr
  let b := splittingBicone hZ s χ hχ hgr
  exact ⟨(isBilimitOfTotal b (splittingBicone_total hZ s χ hχ hgr)).isColimit
    |>.coconePointUniqueUpToIso (colimit.isColimit _)⟩

end Langlands.Renard.AlgebraicFamily
