import Langlands.GroupScheme.Reductive.AffineSplitIsogenyG2Relations

/-! # Common-power transport of word commutator relations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {b : P.Base} {b' : Q.Base}

/-- Transport the root indices and reflection words of an annotated term list, retaining
its coefficients, degrees, and order. -/
def reindexWordData (L : List (List J × J × R × ℕ × ℕ)) :
    List (List J' × J' × R × ℕ × ℕ) :=
  L.map fun t => (t.1.map f.indexEquiv.symm, f.indexEquiv.symm t.2.1, t.2.2)

/-- A literal target word relation transports to the source word expressions whenever
all input and term roots have the same root factor and the coefficients are integers. -/
theorem wordCommRel_of_equalFactors
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (l₁ l₂ : List J) (d₁ d₂ : J) (L : List (List J × J × R × ℕ × ℕ))
    (h₂ : f.rootFactor (f.indexEquiv.symm d₂) = f.rootFactor (f.indexEquiv.symm d₁))
    (hL : ∀ t ∈ L,
      f.rootFactor (f.indexEquiv.symm t.2.1) = f.rootFactor (f.indexEquiv.symm d₁))
    (hcoeff : ∀ t ∈ L, ∃ n : ℤ, t.2.2.1 = (n : R))
    (h : CommRel
      (wordConj Q u' (l₁.map f.indexEquiv.symm)
        (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm d₁)))
      (wordConj Q u' (l₂.map f.indexEquiv.symm)
        (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm d₂)))
      (wordTerms (P := Q) u' (weylFamily Q (targetSimpleWords f hb W) u')
        (reindexWordData f L))) :
    CommRel
      (wordConj P (poweredRootFamily f hchar u') l₁
        (weylFamily P W (poweredRootFamily f hchar u') d₁))
      (wordConj P (poweredRootFamily f hchar u') l₂
        (weylFamily P W (poweredRootFamily f hchar u') d₂))
      (wordTerms (P := P) (poweredRootFamily f hchar u')
        (weylFamily P W (poweredRootFamily f hchar u')) L) := by
  intro B _ s x y
  let Z := Over.mk s
  let q := f.rootFactor (f.indexEquiv.symm d₁)
  have hterm (t : List J × J × R × ℕ × ℕ) (ht : t ∈ L) :
      termPoint Z x y
          (wordConj P (poweredRootFamily f hchar u') t.1
            (weylFamily P W (poweredRootFamily f hchar u') t.2.1), t.2.2) =
        termPoint Z (x ^ q) (y ^ q)
          (wordConj Q u' (t.1.map f.indexEquiv.symm)
            (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm t.2.1)),
            t.2.2) := by
    have hc : (baseScalar Z t.2.2.1) ^ q = baseScalar Z t.2.2.1 := by
      obtain ⟨n, hn⟩ := hcoeff t ht
      rw [hn, map_intCast]
      exact map_intCast
        (sectionPowerRingHom (rootPower f hchar (f.indexEquiv.symm d₁)) q
          (rootPoint_rootPower f hchar _) Z) n
    unfold termPoint
    rw [wordConj_weylFamily_powered_eq f hchar hb W u', rootPoint_rootMap, hL t ht]
    congr 1
    dsimp only [q] at hc ⊢
    simp only [mul_pow, hc, ← pow_mul, Nat.mul_comm]
  simp only [wordConj_weylFamily_powered_eq f hchar hb W u', rootPoint_rootMap, h₂]
  rw [h B s (x ^ q) (y ^ q)]
  simp only [wordTerms, reindexWordData, List.map_map]
  apply congrArg (fun l : List (Over.mk s ⟶ H.X) => l.prod)
  exact List.map_congr_left fun t ht => (hterm t ht).symm

/-- A convenient form when every term starts from one of the two input roots. -/
theorem wordCommRel_of_equalFactors_pair
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (a c : J) (hfac : f.rootFactor (f.indexEquiv.symm a) =
      f.rootFactor (f.indexEquiv.symm c))
    (l₁ l₂ : List J) (d₁ d₂ : J)
    (hd₁ : d₁ = a ∨ d₁ = c) (hd₂ : d₂ = a ∨ d₂ = c)
    (L : List (List J × J × R × ℕ × ℕ))
    (hL : ∀ t ∈ L, t.2.1 = a ∨ t.2.1 = c)
    (hcoeff : ∀ t ∈ L, ∃ n : ℤ, t.2.2.1 = (n : R))
    (h : CommRel
      (wordConj Q u' (l₁.map f.indexEquiv.symm)
        (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm d₁)))
      (wordConj Q u' (l₂.map f.indexEquiv.symm)
        (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm d₂)))
      (wordTerms (P := Q) u' (weylFamily Q (targetSimpleWords f hb W) u')
        (reindexWordData f L))) :
    CommRel
      (wordConj P (poweredRootFamily f hchar u') l₁
        (weylFamily P W (poweredRootFamily f hchar u') d₁))
      (wordConj P (poweredRootFamily f hchar u') l₂
        (weylFamily P W (poweredRootFamily f hchar u') d₂))
      (wordTerms (P := P) (poweredRootFamily f hchar u')
        (weylFamily P W (poweredRootFamily f hchar u')) L) := by
  have heq {x y : J} (hx : x = a ∨ x = c) (hy : y = a ∨ y = c) :
      f.rootFactor (f.indexEquiv.symm x) = f.rootFactor (f.indexEquiv.symm y) := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hfac
    · exact hfac.symm
    · rfl
  exact wordCommRel_of_equalFactors f hchar hb W u' l₁ l₂ d₁ d₂ L
    (heq hd₂ hd₁) (fun t ht => heq (hL t ht) hd₁) hcoeff h

section Standard

variable [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom]
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

omit [IsLocalRing R] in
/-- The standard A2 relation holds for powered actual maps when the Cartan entries agree. -/
theorem a2_wordCommRel_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (hP : P.pairingIn ℤ a c = -1)
    (hQ₁ : Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) = -1)
    (hQ₂ : Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) = -1) :
    CommRel (weylFamily P W (poweredRootFamily f hchar u') a)
      (weylFamily P W (poweredRootFamily f hchar u') c)
      (wordTerms (P := P) (poweredRootFamily f hchar u')
        (weylFamily P W (poweredRootFamily f hchar u')) [([a], c, -1, 1, 1)]) := by
  have hfac : f.rootFactor (f.indexEquiv.symm a) = f.rootFactor (f.indexEquiv.symm c) := by
    have h := f.rootFactor_mul_pairingIn (f.indexEquiv.symm a) (f.indexEquiv.symm c)
    simp only [Equiv.apply_symm_apply, hP, hQ₁] at h
    omega
  exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [] a c
    (Or.inl rfl) (Or.inr rfl) [([a], c, -1, 1, 1)]
    (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact Or.inr rfl)
    (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact ⟨-1, by simp⟩)
    (hd.a2_commRel (hb a ha) (hb c hc)
      (fun h => hac (f.indexEquiv.symm.injective h)) hQ₁ hQ₂)

/-- Both standard B2 word relations transfer when the Cartan entries are unchanged. -/
theorem b2_wordRelations_equalFactors_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (hP : P.pairingIn ℤ a c = -1)
    (hQ₁ : Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) = -1)
    (hQ₂ : Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) = -2) :
    PoweredB2WordRelations f hchar W u' a c := by
  have hfac : f.rootFactor (f.indexEquiv.symm a) = f.rootFactor (f.indexEquiv.symm c) := by
    have h := f.rootFactor_mul_pairingIn (f.indexEquiv.symm a) (f.indexEquiv.symm c)
    simp only [Equiv.apply_symm_apply, hP, hQ₁] at h
    omega
  obtain ⟨h0, h1⟩ := hd.b2_commRels (hb a ha) (hb c hc)
    (fun h => hac (f.indexEquiv.symm.injective h)) hQ₁ hQ₂
  constructor
  · exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [] a c
      (Or.inl rfl) (Or.inr rfl) [([c], a, 1, 1, 1), ([a], c, 1, 2, 1)]
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp)
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact ⟨1, by simp⟩) h0
  · exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [c] a a
      (Or.inl rfl) (Or.inl rfl) [([a], c, 2, 1, 1)]
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact Or.inr rfl)
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact ⟨2, by simp⟩) h1

/-- All five standard G2 word relations transfer when the Cartan entries are unchanged. -/
theorem g2_wordRelations_equalFactors_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (hP : P.pairingIn ℤ a c = -1)
    (hQ₁ : Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) = -1)
    (hQ₂ : Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) = -3) :
    PoweredG2WordRelations f hchar W u' a c := by
  have hfac : f.rootFactor (f.indexEquiv.symm a) = f.rootFactor (f.indexEquiv.symm c) := by
    have h := f.rootFactor_mul_pairingIn (f.indexEquiv.symm a) (f.indexEquiv.symm c)
    simp only [Equiv.apply_symm_apply, hP, hQ₁] at h
    omega
  obtain ⟨h0, h1, h2, h3, h4⟩ := hd.g2_commRels (hb a ha) (hb c hc)
    (fun h => hac (f.indexEquiv.symm.injective h)) hQ₁ hQ₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [] a c
      (Or.inl rfl) (Or.inr rfl)
      [([c], a, 1, 1, 1), ([a, c], a, 1, 2, 1),
        ([a], c, -1, 3, 1), ([c, a], c, -1, 3, 2)] _ _ h0
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> simp
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨-1, by simp⟩
      · exact ⟨-1, by simp⟩
  · apply wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [c] a a
      (Or.inl rfl) (Or.inl rfl)
      [([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)] _ _ h1
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> simp
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨2, by simp⟩
      · exact ⟨-3, by simp⟩
      · exact ⟨-3, by simp⟩
  · exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [a, c] a a
      (Or.inl rfl) (Or.inl rfl) [([a], c, -3, 1, 1)]
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact Or.inr rfl)
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact ⟨-3, by simp⟩) h2
  · exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [] [a] c c
      (Or.inr rfl) (Or.inr rfl) [([c, a], c, -1, 1, 1)]
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact Or.inr rfl)
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact ⟨-1, by simp⟩) h3
  · exact wordCommRel_of_equalFactors_pair f hchar hb W u' a c hfac [c] [a, c] a a
      (Or.inl rfl) (Or.inl rfl) [([c, a], c, -3, 1, 1)]
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact Or.inr rfl)
      (by intro t ht; obtain rfl := List.mem_singleton.mp ht; exact ⟨-3, by simp⟩) h4

end Standard

end Langlands.GroupScheme.AffineRootDatumIsogeny
