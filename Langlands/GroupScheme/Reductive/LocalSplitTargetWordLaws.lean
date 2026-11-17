import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction

/-! # Commutator transfer from source geometry and explicit target word laws -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I J : Type u}
  {H : GroupScheme (Spec (CommRingCat.of R))}

/-- The actual word relations needed of a target family in the commutator reduction.
The target torus, root subgroup representation, and geometric properties are not inputs. -/
structure TargetWordRelations (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ H)) : Prop where
  pointsCommute : ∀ {x y : J}, P.root x ≠ -P.root y →
    (∀ (α : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
      (s : ℤ) • P.root x + (t : ℤ) • P.root y ≠ P.root α) →
    PointsCommute (weylFamily P W u x) (weylFamily P W u y)
  a2_commRel : ∀ {a c : J}
    (_ha : a ∈ b.support) (_hc : c ∈ b.support) (_hac : a ≠ c)
    (_h1 : P.pairingIn ℤ a c = -1) (_h2 : P.pairingIn ℤ c a = -1),
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([a], c, -1, 1, 1)])
  b2_commRels : ∀ {a c : J}
    (_ha : a ∈ b.support) (_hc : c ∈ b.support) (_hac : a ≠ c)
    (_h1 : P.pairingIn ℤ a c = -1) (_h2 : P.pairingIn ℤ c a = -2),
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([c], a, 1, 1, 1), ([a], c, 1, 2, 1)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([a], c, 2, 1, 1)])
  g2_commRels : ∀ {a c : J}
    (_ha : a ∈ b.support) (_hc : c ∈ b.support) (_hac : a ≠ c)
    (_h1 : P.pairingIn ℤ a c = -1) (_h2 : P.pairingIn ℤ c a = -3),
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([c], a, 1, 1, 1), ([a, c], a, 1, 2, 1), ([a], c, -1, 3, 1), ([c, a], c, -1, 3, 2)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u)
        [([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [a, c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([a], c, -3, 1, 1)]) ∧
    CommRel (weylFamily P W u c) (wordConj P u [a] (weylFamily P W u c))
      (wordTerms (P := P) u (weylFamily P W u) [([c, a], c, -1, 1, 1)]) ∧
    CommRel (wordConj P u [c] (weylFamily P W u a)) (wordConj P u [a, c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([c, a], c, -3, 1, 1)])

namespace TargetWordProofs

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b b' : P.Base}
  {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

omit [IsLocalRing R] in
/-- **A commuting pair.** If the standard pair has no root in its cone, so does the transported
pair, and the formula is empty. -/
theorem pairFormula_of_commute_std [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {s₁ ε₀ : J} (hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) (hneg : P.root s₁ ≠ -P.root ε₀)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root s₁ + (dT : ℤ) • P.root ε₀ ≠ P.root α) :
    PairFormula b' W u u' q β ε :=
  hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) hl (by simp) (by simp) []
    (by simp) (by rw [List.append_nil]; exact hβl) (by rw [List.append_nil]; exact hεl)
    (by simp) (by simp) List.Pairwise.nil
    (commRel_nil (hdG.pointsCommute hneg hcone)) (commRel_nil (hdH.pointsCommute hneg hcone))

omit [IsLocalRing R] in
/-- **A commuting pair, from coefficients.** -/
theorem pairFormula_of_commute_coeffs [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c s₁ ε₀ : J} (hli : LinearIndependent ℤ ![P.root a, P.root c])
    (hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {m₁ n₁ m₂ n₂ : ℤ}
    (hx : P.root s₁ = m₁ • P.root a + n₁ • P.root c)
    (hy : P.root ε₀ = m₂ • P.root a + n₂ • P.root c) {Φ : ℤ → ℤ → Prop}
    (hΦ : ∀ (α : J) (m n : ℤ), P.root α = m • P.root a + n • P.root c → Φ m n)
    (hopp : m₁ + m₂ ≠ 0 ∨ n₁ + n₂ ≠ 0)
    (hno : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m₁ + dT * m₂) (dS * n₁ + dT * n₂) → False) :
    PairFormula b' W u u' q β ε :=
  have h := noOpp_cone_of_coeffs hli hx hy hΦ hopp hno
  pairFormula_of_commute_std hdG hdH hU q hq hβ hε hl hβl hεl h.1 h.2

omit [IsLocalRing R] in
/-- Word conjugates of the Weyl families whose roots have no root in their cone commute, in
both groups. -/
theorem pointsCommute_wordConj
    (hU : WeylConjugationRelations P b W u u')
    (hdG : IsNormalSimpleData i P b W u) (hdH : TargetWordRelations P b W u')
    {l₁ l₂ : List J} (hl₁ : ∀ c ∈ l₁, c ∈ b.support) (hl₂ : ∀ c ∈ l₂, c ∈ b.support)
    {d₁ d₂ : J}
    (h : P.root (Langlands.LinearAlgebra.wordPerm P l₁ d₁) ≠
        -P.root (Langlands.LinearAlgebra.wordPerm P l₂ d₂) ∧
      ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
        (dS : ℤ) • P.root (Langlands.LinearAlgebra.wordPerm P l₁ d₁) +
          (dT : ℤ) • P.root (Langlands.LinearAlgebra.wordPerm P l₂ d₂) ≠ P.root α) :
    PointsCommute (wordConj P u l₁ (weylFamily P W u d₁))
        (wordConj P u l₂ (weylFamily P W u d₂)) ∧
      PointsCommute (wordConj P u' l₁ (weylFamily P W u' d₁))
        (wordConj P u' l₂ (weylFamily P W u' d₂)) := by
  obtain ⟨κ₁, e₁, e₁'⟩ := hU.wordConj_weylFamily hl₁ d₁
  obtain ⟨κ₂, e₂, e₂'⟩ := hU.wordConj_weylFamily hl₂ d₂
  exact ⟨PointsCommute.of_scaleHom (hdG.pointsCommute h.1 h.2) _ _ e₁ e₂,
    PointsCommute.of_scaleHom (hdH.pointsCommute h.1 h.2) _ _ e₁' e₂'⟩

/-- **Pairs of type `G₂` with a short first root.** -/
theorem pairFormula_g2_short [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    (hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2, r3, r4⟩ := g2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a (P.reflectionPerm c a)) =
      (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by rw [r2]; simp
  have rd3 : P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r3]; simp
  have rd4 : P.root (P.reflectionPerm c (P.reflectionPerm a c)) =
      (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := r4
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  have hlac : ∀ x ∈ [a, c], x ∈ b.support := by simp [ha, hc]
  have hlca : ∀ x ∈ [c, a], x ∈ b.support := by simp [ha, hc]
  obtain ⟨g1, g2, g3, -, -⟩ := hdG.g2_commRels ha hc hac h1 h2
  obtain ⟨k1, k2, k3, -, -⟩ := hdH.g2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide)) g1 k1
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, rd3, rd4, Nat.cast_one, Nat.cast_ofNat]
      try module
  · -- `ε₀ = a + c`
    have hε₀' : P.reflectionPerm c a = ε₀ := eq_of_coeffs rd1 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    have hroot : ∀ t ∈ ([([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)] :
        List (List J × J × R × ℕ × ℕ)),
        P.root (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) =
          (t.2.2.2.1 : ℤ) • P.root β + (t.2.2.2.2 : ℤ) • P.root ε := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      all_goals
        refine root_transport hβl hεl ?_
        simp only [wordPerm_cons, wordPerm_nil, rd2, rd3, rd4, hε₀, Nat.cast_one, Nat.cast_ofNat]
        try module
    have hpos₂ : b'.IsPos (Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c) :=
      isPos_of_combo hβ hε (i := 2) (j := 1) (by norm_num) le_rfl
        (hroot ([a], c, -3, 2, 1) (by simp))
    have hpos₃ : b'.IsPos (Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c) :=
      isPos_of_combo hβ hε (i := 1) (j := 2) le_rfl (by norm_num)
        (hroot ([c, a], c, -3, 1, 2) (by simp))
    have hne : Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c ≠
        Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c := by
      intro h
      rw [wordPerm_append, wordPerm_append] at h
      have h' := wordPerm_injective l h
      simp only [wordPerm_cons, wordPerm_nil] at h'
      have := coeffs_eq_of_eq hli rd3 rd4 h'
      omega
    rcases lt_trichotomy (q (Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c))
        (q (Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c)) with hlt | heq | hgt
    · refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
        hl (by simp) hlc _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε' hroot
        (by simp) ?_ g2 k2
      refine .cons ?_ (.cons ?_ (.cons (fun _ h => by simp at h) .nil))
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact Or.inl (by norm_num)
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        exact Or.inr hlt
    · exact absurd (hqinj _ _ hpos₂ hpos₃ heq) hne
    · have hc23 := pointsCommute_wordConj hU hdG hdH hla hlca (d₁ := c) (d₂ := c)
        (noOpp_cone_of_coeffs hli rd3 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
      refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
        hl (by simp) hlc [([a, c], a, 2, 1, 1), ([c, a], c, -3, 1, 2), ([a], c, -3, 2, 1)]
        (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε'
        (fun t ht => hroot t (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
          tauto))
        (by simp) ?_ (CommRel.swap (L₁ := [_]) (L₂ := []) g2 hc23.1)
        (CommRel.swap (L₁ := [_]) (L₂ := []) k2 hc23.2)
      refine .cons ?_ (.cons ?_ (.cons (fun _ h => by simp at h) .nil))
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact Or.inl (by norm_num)
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        exact Or.inr hgt
  · -- `ε₀ = 2 a + c`
    have hε₀' : P.reflectionPerm a (P.reflectionPerm c a) = ε₀ := eq_of_coeffs rd2 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [a, c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [a, c]) (d₁ := a) (d₂ := a)
      hl (by simp) hlac _ (by simp [ha]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g3 k3
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd3, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `G₂` with a long first root.** -/
theorem pairFormula_g2_long [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3)
    (hβl : Langlands.LinearAlgebra.wordPerm P l c = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀c : ε₀ ≠ c) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2, r3, r4⟩ := g2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a (P.reflectionPerm c a)) =
      (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by rw [r2]; simp
  have rd3 : P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r3]; simp
  have rd4 : P.root (P.reflectionPerm c (P.reflectionPerm a c)) =
      (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := r4
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  have hlac : ∀ x ∈ [a, c], x ∈ b.support := by simp [ha, hc]
  have hlca : ∀ x ∈ [c, a], x ∈ b.support := by simp [ha, hc]
  obtain ⟨g1, -, -, g4, g5⟩ := hdG.g2_commRels ha hc hac h1 h2
  obtain ⟨k1, -, -, k4, k5⟩ := hdH.g2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · -- `ε₀ = a`: the reversed formula
    rw [eq_of_coeffs hε₀ ra rfl rfl] at hεl
    have c13 := pointsCommute_wordConj hU hdG hdH hlc hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd3 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c14 := pointsCommute_wordConj hU hdG hdH hlc hlca (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c23 := pointsCommute_wordConj hU hdG hdH hlac hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd2 rd3 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c24 := pointsCommute_wordConj hU hdG hdH hlac hlca (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd2 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c34 := pointsCommute_wordConj hU hdG hdH hla hlca (d₁ := c) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd3 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := c) (d₂ := a) hl
      (by simp) (by simp)
      [([c], a, -1, 1, 1), ([a, c], a, -1, 1, 2), ([a], c, 1, 1, 3), ([c, a], c, -2, 2, 3)]
      (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide))
      (CommRel.g2_reverse g1 g5 c13.1 c14.1 c23.1 c24.1 c34.1)
      (CommRel.g2_reverse k1 k5 c13.2 c14.2 c23.2 c24.2 c34.2)
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, rd3, rd4, Nat.cast_one, Nat.cast_ofNat]
      try module
  · exact absurd (eq_of_coeffs hε₀ rc rfl rfl) hε₀c
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · -- `ε₀ = 3 a + c`
    have hε₀' : P.reflectionPerm a c = ε₀ := eq_of_coeffs rd3 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [a]) (d₁ := c) (d₂ := c)
      hl (by simp) hla _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g4 k4
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd4, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `B₂` with a short first root.** -/
theorem pairFormula_b2_short [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2⟩ := b2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a c) = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r2]; simp
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  obtain ⟨g1, g2⟩ := hdG.b2_commRels ha hc hac h1 h2
  obtain ⟨k1, k2⟩ := hdH.b2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide)) g1 k1
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, Nat.cast_one, Nat.cast_ofNat]
      try module
  · -- `ε₀ = a + c`
    have hε₀' : P.reflectionPerm c a = ε₀ := eq_of_coeffs rd1 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
      hl (by simp) hlc _ (by simp [ha]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g2 k2
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd2, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `B₂` with a long first root.** -/
theorem pairFormula_b2_long [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2)
    (hβl : Langlands.LinearAlgebra.wordPerm P l c = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀c : ε₀ ≠ c) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2⟩ := b2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a c) = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r2]; simp
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  obtain ⟨g1, -⟩ := hdG.b2_commRels ha hc hac h1 h2
  obtain ⟨k1, -⟩ := hdH.b2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · -- `ε₀ = a`: the reversed formula
    rw [eq_of_coeffs hε₀ ra rfl rfl] at hεl
    have c12 := pointsCommute_wordConj hU hdG hdH hlc hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd2 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := c) (d₂ := a) hl
      (by simp) (by simp) [([c], a, -1, 1, 1), ([a], c, -1, 1, 2)]
      (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide))
      (CommRel.b2_reverse g1 c12.1) (CommRel.b2_reverse k1 c12.2)
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, Nat.cast_one, Nat.cast_ofNat]
      try module
  · exact absurd (eq_of_coeffs hε₀ rc rfl rfl) hε₀c
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

omit [IsLocalRing R] in
/-- **Pairs of type `A₂`.** -/
theorem pairFormula_a2 [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.a2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd : P.root (P.reflectionPerm a c) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
      pairing_eq_of_pairingIn h2]
    module
  have g := hdG.a2_commRel ha hc hac h1 h2
  have k := hdH.a2_commRel ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.a2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp) (pairwise_of_exps (by simp)) g k
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd, Nat.cast_one]
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

omit [IsLocalRing R] in
/-- **Pairs of type `A₁ × A₁`.** -/
theorem pairFormula_a1a1 [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h2 : P.pairingIn ℤ c a = 0)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.a1a1_coeffs ha hc hac h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  rcases Langlands.LinearAlgebra.a1a1_coeffs_of_nonneg ha hc hac h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Every pair of distinct positive roots has a good formula.** -/
theorem pairFormula_of_pos [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    (hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) (hne : β ≠ ε) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root β, P.root ε] := by
    by_contra hdep
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) β ε hdep with h | h
    · exact hne (P.root.injective h)
    · have h' : β = P.reflectionPerm ε ε := P.root.injective (by
        rw [h, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self])
      rw [h'] at hβ
      exact (RootPairing.Base.IsPos.neg_iff_not (b := b') ε).mp hβ hε
  obtain ⟨l, s₁, s₂, hl, hs₁, hs₂, hs₁₂, hβr, p₀, q₀, hεr⟩ :=
    Langlands.LinearAlgebra.exists_word_rankTwo P b hli
  obtain ⟨ε₀, hεl, hε₀⟩ : ∃ ε₀, Langlands.LinearAlgebra.wordPerm P l ε₀ = ε ∧
      P.root ε₀ = (p₀ : ℤ) • P.root s₁ + (q₀ : ℤ) • P.root s₂ :=
    ⟨Langlands.LinearAlgebra.wordPerm P l.reverse ε, wordPerm_reverse l ε, by
      rw [Langlands.LinearAlgebra.root_wordPerm, hεr, wordReflect_reverse]⟩
  have hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β :=
    P.root.injective (by rw [Langlands.LinearAlgebra.root_wordPerm, hβr])
  have hε₀s : ε₀ ≠ s₁ := by
    intro h
    apply hne
    rw [← hβl, ← hεl, h]
  have hli₁₂ : LinearIndependent ℤ ![P.root s₁, P.root s₂] :=
    b.linearIndependent_pair_of_ne (i := ⟨s₁, hs₁⟩) (j := ⟨s₂, hs₂⟩)
      (fun h' => hs₁₂ (congrArg Subtype.val h'))
  have hr1 : P.root s₁ ≠ P.root s₂ := fun h => hs₁₂ (P.root.injective h)
  have hr2 : P.root s₁ ≠ -P.root s₂ := by
    intro h
    have := LinearIndependent.pair_iff.mp hli₁₂ 1 1 (by rw [h]; module)
    simp at this
  have hle1 : P.pairingIn ℤ s₁ s₂ ≤ 0 := b.pairingIn_le_zero_of_ne hs₁₂ hs₁ hs₂
  have hle2 : P.pairingIn ℤ s₂ s₁ ≤ 0 := b.pairingIn_le_zero_of_ne hs₁₂.symm hs₂ hs₁
  have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' s₁ s₂ hr1 hr2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  have hε₀' : P.root ε₀ = (q₀ : ℤ) • P.root s₂ + (p₀ : ℤ) • P.root s₁ := by
    rw [hε₀, add_comm]
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact pairFormula_a1a1 hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h2 hβl hεl hε₀ hε₀s
  · omega
  · exact pairFormula_a2 hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀ hε₀s
  · omega
  · omega
  · exact pairFormula_b2_short hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀ hε₀s
  · exact pairFormula_b2_long hdG hdH hU q hq hβ hε hl hs₂ hs₁ hs₁₂.symm h2 h1 hβl hεl hε₀'
      hε₀s
  · omega
  · omega
  · exact pairFormula_g2_short hdG hdH hU q hq hqinj hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀
      hε₀s
  · exact pairFormula_g2_long hdG hdH hU q hq hβ hε hl hs₂ hs₁ hs₁₂.symm h2 h1 hβl hεl hε₀'
      hε₀s

/-- **Common universal coordinates for an enumeration by height.** For an enumeration `pos`
of the positive roots of a base `b'` by increasing `b'`-height, any two positions `k < l` have
the same universal commutator coordinates in the two Weyl families. -/
theorem exists_common_isUnivComm_of_base [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    (b' : P.Base) {n : ℕ} (pos : Fin n ≃ {α // b'.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b'.height (pos p : J) ≤ b'.height (pos q : J))
    (k l : Fin n) (hkl : k < l) :
    ∃ E : Fin n → Polynomial (Polynomial R),
      IsUnivComm (weylFamily P W u) (fun k => (pos k : J)) k l E ∧
        IsUnivComm (weylFamily P W u') (fun k => (pos k : J)) k l E := by
  classical
  let q : J → Fin n := fun j => if h : b'.IsPos j then pos.symm ⟨j, h⟩ else k
  have hqpos : ∀ j (h : b'.IsPos j), q j = pos.symm ⟨j, h⟩ := fun j h => by
    simp only [q, h, ↓reduceDIte]
  have hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y := by
    intro x y hx hy hxy
    rw [hqpos x hx, hqpos y hy]
    by_contra hle
    rw [not_lt] at hle
    have := hmono _ _ hle
    simp only [Equiv.apply_symm_apply] at this
    omega
  have hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y := by
    intro x y hx hy hxy
    rw [hqpos x hx, hqpos y hy] at hxy
    exact congrArg Subtype.val (pos.symm.injective hxy)
  have hkl' : (pos k : J) ≠ (pos l : J) :=
    fun h => (ne_of_lt hkl) (pos.injective (Subtype.ext h))
  obtain ⟨L, hLpos, hLsort, hG', hH'⟩ :=
    pairFormula_of_pos hdG hdH hU q hq hqinj (pos k).2 (pos l).2 hkl'
  exact exists_common_isUnivComm (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J))
    k l L q (fun t ht => by simp only [hqpos t.1 (hLpos t ht), Equiv.apply_symm_apply])
    hLsort hG' hH'

/-- Source geometry and the stated target laws give transfer of all positive commutators. -/
theorem commutatorRelations (hdG : IsNormalSimpleData i P b W u)
    (hdH : TargetWordRelations P b W u')
    (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) :
    CommutatorRelations b W u u' (fun k => (pos k : J)) := by
  classical
  have : Finite J := hdG.rootDatum.finite
  exact commutatorRelations_of_isUnivComm hdG.reductive hdG.maximal hdG.rootDatum W
    (fun a ha => (hdG.param a ha).1) hdG.weyl
    (Finite.equivFin {α // ¬ b.IsPos α}).symm pos
    (fun k l hkl => exists_common_isUnivComm_of_base hdG hdH hU b pos hmono k l hkl)

end TargetWordProofs

/-- The arbitrary-target commutator reduction over a local ring. -/
def TargetWordCommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
    IsNormalSimpleData i P b W u → TargetWordRelations P b W u' →
    WeylConjugationRelations P b W u u' →
    ∀ (n : ℕ) (pos : Fin n ≃ {α // b.IsPos α}),
    (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
      CommutatorRelations b W u u' (fun k => (pos k : J))

/-- The stated laws suffice without a target root-parametrization hypothesis. -/
theorem targetWordCommutator : TargetWordCommutatorStatement.{u} := by
  intro R _ _ I _ _ J G H _ i P b W u u' hdG hdH hU n pos hmono
  exact TargetWordProofs.commutatorRelations hdG hdH hU pos hmono

end Langlands.GroupScheme.LocalSplitCell
