import Langlands.GroupScheme.Reductive.AffineSplitIsogenyB2Relations
import Langlands.GroupScheme.Reductive.G2PowerCommutatorTransport

/-! # The exceptional G2 relations for actual powered Weyl families -/

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

/-- The five standard source G2 word relations for the actual powered maps. -/
def PoweredG2WordRelations (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) (a c : J) : Prop :=
  let v := poweredRootFamily f hchar u'
  let w := weylFamily P W v
  CommRel (w a) (w c) (wordTerms (P := P) v w
      [([c], a, 1, 1, 1), ([a, c], a, 1, 2, 1),
        ([a], c, -1, 3, 1), ([c, a], c, -1, 3, 2)]) ∧
    CommRel (w a) (wordConj P v [c] (w a)) (wordTerms (P := P) v w
      [([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)]) ∧
    CommRel (w a) (wordConj P v [a, c] (w a))
      (wordTerms (P := P) v w [([a], c, -3, 1, 1)]) ∧
    CommRel (w c) (wordConj P v [a] (w c))
      (wordTerms (P := P) v w [([c, a], c, -1, 1, 1)]) ∧
    CommRel (wordConj P v [c] (w a)) (wordConj P v [a, c] (w a))
      (wordTerms (P := P) v w [([c, a], c, -3, 1, 1)])

section NormalTarget

variable [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom]
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

omit [Finite J'] [Q.IsReduced] in
/-- In one genuine normalized group, word conjugates commute whenever their roots have
no root in their positive cone. No comparison with a second group is needed. -/
theorem pointsCommute_wordConj_of_noCone
    {W' : ∀ α', SimpleWord Q b' α'} {u' : J' → (Ga R ⟶ H)}
    (hd : IsNormalSimpleData i' Q b' W' u')
    (l₁ l₂ : List J') (hl₁ : ∀ a ∈ l₁, a ∈ b'.support)
    (hl₂ : ∀ a ∈ l₂, a ∈ b'.support) (d₁ d₂ : J')
    (hno : Q.root (Langlands.LinearAlgebra.wordPerm Q l₁ d₁) ≠
      -Q.root (Langlands.LinearAlgebra.wordPerm Q l₂ d₂))
    (hcone : ∀ (α : J') (s t : ℕ), 1 ≤ s → 1 ≤ t →
      (s : ℤ) • Q.root (Langlands.LinearAlgebra.wordPerm Q l₁ d₁) +
        (t : ℤ) • Q.root (Langlands.LinearAlgebra.wordPerm Q l₂ d₂) ≠ Q.root α) :
    PointsCommute (wordConj Q u' l₁ (weylFamily Q W' u' d₁))
      (wordConj Q u' l₂ (weylFamily Q W' u' d₂)) := by
  have hparam (l : List J') (hl : ∀ a ∈ l, a ∈ b'.support) (d : J') :
      IsRootParametrization i' (Q.root (Langlands.LinearAlgebra.wordPerm Q l d))
        (wordConj Q u' l (weylFamily Q W' u' d)) := by
    rw [Langlands.LinearAlgebra.root_wordPerm]
    exact isRootParametrization_wordConj l (fun a ha => hd.weyl a (hl a ha))
      (hd.isRootParametrization d)
  obtain ⟨κ₁, hκ₁, _⟩ := (hparam l₁ hl₁ d₁).existsUnique_unit_of_rootDatum hd.rootDatum
    (Langlands.LinearAlgebra.wordPerm Q l₁ d₁)
    (hd.isRootParametrization (Langlands.LinearAlgebra.wordPerm Q l₁ d₁))
  obtain ⟨κ₂, hκ₂, _⟩ := (hparam l₂ hl₂ d₂).existsUnique_unit_of_rootDatum hd.rootDatum
    (Langlands.LinearAlgebra.wordPerm Q l₂ d₂)
    (hd.isRootParametrization (Langlands.LinearAlgebra.wordPerm Q l₂ d₂))
  exact (hd.pointsCommute hno hcone).of_scaleHom (κ₁ : R) (κ₂ : R) hκ₁ hκ₂

/-- A normalized genuine target G2 pair with exchanged lengths satisfies all five source
G2 relations after the root powers prescribed by the isogeny. -/
theorem poweredG2WordRelations_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (hP : P.pairingIn ℤ a c = -1)
    (hQ₁ : Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) = -1)
    (hQ₂ : Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) = -3) :
    PoweredG2WordRelations f hchar W u' a c := by
  classical
  let A := f.indexEquiv.symm a
  let C := f.indexEquiv.symm c
  let w := weylFamily Q (targetSimpleWords f hb W) u'
  let p₁ := wordConj Q u' [A] (w C)
  let p₂ := wordConj Q u' [C, A] (w C)
  let p₃ := wordConj Q u' [C] (w A)
  let p₄ := wordConj Q u' [A, C] (w A)
  have hA : A ∈ b'.support := hb a ha
  have hC : C ∈ b'.support := hb c hc
  have hCA : C ≠ A := fun h => hac (f.indexEquiv.symm.injective h.symm)
  have hratio : f.rootFactor A = 3 * f.rootFactor C := by
    change f.rootFactor (f.indexEquiv.symm a) = 3 * f.rootFactor (f.indexEquiv.symm c)
    have h := f.rootFactor_mul_pairingIn A C
    simp only [A, C, Equiv.apply_symm_apply, hP, hQ₂] at h
    omega
  have hp : p = 3 :=
    f.characteristicExponent_eq_of_rootFactor_ratio Nat.prime_three C A hratio
  have h₃ : (3 : R) = 0 := by
    have hq := f.rootFactor_pos C
    have hne : f.rootFactor A ≠ 1 := by omega
    simpa only [hp, Nat.cast_ofNat] using hchar A hne
  have hodd : Odd (f.rootFactor C) := by
    obtain ⟨n, hn⟩ := f.rootFactor_pow C
    rw [hn, hp]
    exact (by decide : Odd (3 : ℕ)).pow
  have hFq := rootPoint_rootPower f hchar C
  have hF3q : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (rootPower f hchar A) Z x =
        VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (3 * f.rootFactor C)) := by
    intro Z x
    rw [rootPoint_rootPower, hratio]
  obtain ⟨h0, h1, _, h3, h4⟩ := hd.g2_commRels hC hA hCA hQ₁ hQ₂
  have hli : LinearIndependent ℤ ![Q.root C, Q.root A] :=
    b'.linearIndependent_pair_of_ne (i := ⟨C, hC⟩) (j := ⟨A, hA⟩)
      (fun h => hCA (congrArg Subtype.val h))
  have hroots := g2_roots hQ₁ hQ₂
  have hrootA : Q.root A = (0 : ℤ) • Q.root C + (1 : ℤ) • Q.root A := by simp
  have hroot3 : Q.root (Langlands.LinearAlgebra.wordPerm Q [C] A) =
      (3 : ℤ) • Q.root C + (1 : ℤ) • Q.root A := by
    change Q.root (Q.reflectionPerm C A) = (3 : ℤ) • Q.root C + (1 : ℤ) • Q.root A
    rw [one_smul]
    exact hroots.2.2.1
  have hroot4 : Q.root (Langlands.LinearAlgebra.wordPerm Q [A, C] A) =
      (3 : ℤ) • Q.root C + (2 : ℤ) • Q.root A := hroots.2.2.2
  have hcone34 := noOpp_cone_of_coeffs hli hroot3 hroot4
    (fun α m n h => Langlands.LinearAlgebra.g2_coeffs hC hA hCA hQ₁ hQ₂ h)
    (by norm_num) (by intro s t hs ht h; omega)
  have hconeA4 := noOpp_cone_of_coeffs hli hrootA hroot4
    (fun α m n h => Langlands.LinearAlgebra.g2_coeffs hC hA hCA hQ₁ hQ₂ h)
    (by norm_num) (by intro s t hs ht h; omega)
  have h34 : PointsCommute p₃ p₄ :=
    pointsCommute_wordConj_of_noCone hd [C] [A, C]
      (by simp [hC]) (by simp [hA, hC]) A A hcone34.1 hcone34.2
  have hA4 : PointsCommute (w A) p₄ :=
    pointsCommute_wordConj_of_noCone hd [] [A, C]
      (by simp) (by simp [hA, hC]) A A hconeA4.1 hconeA4.2
  have hprincipal := g2_unequal_power_commRel (w A) (w C) p₁ p₂ p₃ p₄
    h0 h4 h34 h₃ (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C)
    hodd hFq hF3q
  have hmixed1 := g2_mixed_long_power_commRel (w A) p₁ p₂ p₃ p₄ h3 h₃
    (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C) hF3q
  have hmixed2 := g2_mixed_zero_power_commRel (w A) p₄ p₁ hA4 h₃
    (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C) hF3q
  have hmixed3 := g2_mixed_short_power_commRel (w C) p₁ p₂ p₃ p₄ h1 h₃
    (rootPower f hchar C) (f.rootFactor C) hFq
  have hmixed4 := g2_mixed_zero_power_commRel p₃ p₄ p₂ h34 h₃
    (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C) hF3q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [wordTerms, List.map_cons, List.map_nil,
      weylFamily_powered_eq f hchar hb W u', wordConj_rootMap]
  · exact hprincipal
  · exact hmixed1
  · exact hmixed2
  · exact hmixed3
  · exact hmixed4

end NormalTarget

end Langlands.GroupScheme.AffineRootDatumIsogeny
