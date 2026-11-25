import Langlands.LocalFactor.Ramification.ArtinExponent
import Langlands.Representation.Finite.CharacterCompletenessProof

/-!
# The Artin and Swan characters

For a finite group `G` acting on a local ring `R` with lower groups `G_i`, Serre's Artin function is
`a_G(g) = −[G:G_0] i_G(g)` for `g ≠ 1` and `a_G(1) = [G:G_0] Σ_{h≠1} i_G(h)`, with `i_G = lowerDepth`
(`artinClassFunction`), and the Swan function is the same with `i_G − 1` in place of `i_G`
(`swanClassFunction`). They are integer-valued class functions, and the Artin and Swan expressions
of a complex representation are their pairings with its character:
`a(ρ) = |G|⁻¹ Σ_g χ_ρ(g) a_G(g)` (`artinConductor_eq_sum_character_mul`) and likewise for Swan.

For the automorphism group of a finite extension of p-adic fields these pairings are natural
numbers for every representation (`Padic.exists_nat_artinConductor`), so by completeness of the
irreducible characters (`FiniteRep.CharacterCompleteness.exists_character_eq`) the Artin and Swan
functions are characters of representations: the Artin representation and the Swan representation,
defined up to isomorphism (`Padic.artinRepClass`, `Padic.swanRepClass`). The Artin exponent of `V` is
the dimension of `Hom_G(A, V)` with `A` the Artin representation, and likewise for Swan.
-/

noncomputable section

namespace Langlands.Ramification

open Module

universe uR uG uV uK uL

section Generic

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R]

namespace ArtinCharacter

/-- The class function `g ↦ −[G:G_0] d(g)` for `g ≠ 1` and `1 ↦ [G:G_0] Σ_h d(h)` of a weight `d`. -/
def weighted [Fintype G] [DecidableEq G] (d : G → ℕ) (g : G) : ℤ :=
  if g = 1 then (((lowerGroup R G 0).index * ∑ h, d h : ℕ) : ℤ)
  else -(((lowerGroup R G 0).index * d g : ℕ) : ℤ)

variable {R G}

theorem weighted_eq [Fintype G] [DecidableEq G] {d : G → ℕ} (hd : d 1 = 0) (g : G) :
    (weighted R G d g : ℂ) =
      ((lowerGroup R G 0).index : ℂ) * ((if g = 1 then (∑ h, (d h : ℂ)) else 0) - d g) := by
  unfold weighted
  by_cases hg : g = 1
  · subst hg
    simp [hd]
  · simp [hg]

/-- The pairing of a function with the weighted class function. -/
theorem sum_mul_weighted [Fintype G] [DecidableEq G] {d : G → ℕ} (hd : d 1 = 0) (f : G → ℂ) :
    ∑ g, f g * (weighted R G d g : ℂ) =
      ((lowerGroup R G 0).index : ℂ) * ∑ g, (d g : ℂ) * (f 1 - f g) := by
  simp only [weighted_eq hd, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun g _ => by ring)
    (Finset.sum_congr rfl fun g _ => by ring)

theorem weighted_conj [Fintype G] [DecidableEq G] {d : G → ℕ}
    (hd : ∀ g h : G, d (h * g * h⁻¹) = d g) (g h : G) :
    weighted R G d (h * g * h⁻¹) = weighted R G d g := by
  unfold weighted
  by_cases hg : g = 1
  · subst hg
    simp
  · have hg' : h * g * h⁻¹ ≠ 1 := fun e =>
      hg (by simpa [mul_assoc] using congrArg (fun x => h⁻¹ * x * h) e)
    rw [ite_eq_right hg', ite_eq_right hg, hd g h]

theorem weighted_inv [Fintype G] [DecidableEq G] {d : G → ℕ} (hd : ∀ g : G, d g⁻¹ = d g)
    (g : G) : weighted R G d g⁻¹ = weighted R G d g := by
  unfold weighted
  by_cases hg : g = 1
  · subst hg
    simp
  · rw [ite_eq_right (inv_ne_one.mpr hg), ite_eq_right hg, hd g]

end ArtinCharacter

open ArtinCharacter

variable {R G} in
/-- The depth is a class function. -/
theorem lowerDepth_conj (g h : G) : lowerDepth R G (h * g * h⁻¹) = lowerDepth R G g := by
  unfold lowerDepth
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  constructor
  · intro hi
    have := (lowerGroup_normal R G i).conj_mem _ hi h⁻¹
    simpa [mul_assoc] using this
  · intro hi
    exact (lowerGroup_normal R G i).conj_mem _ hi h

variable {R G} in
theorem lowerDepth_inv (g : G) : lowerDepth R G g⁻¹ = lowerDepth R G g := by
  unfold lowerDepth
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i => Subgroup.inv_mem_iff _)

variable {R G} in
/-- Outside inertia the depth is `0`. -/
theorem lowerDepth_eq_zero_of_not_mem {g : G} (hg : g ∉ lowerGroup R G 0) :
    lowerDepth R G g = 0 := by
  unfold lowerDepth
  have : IsEmpty {i : ℕ // g ∈ lowerGroup R G i} :=
    ⟨fun i => hg (lowerGroup_antitone R G (Nat.zero_le _) i.2)⟩
  exact Nat.card_of_isEmpty

variable {R G} in
/-- In inertia, away from `1`, the depth is at least `1`. -/
theorem one_le_lowerDepth [IsNoetherianRing R] [FaithfulSMul G R] [Finite G] {g : G}
    (hg : g ∈ lowerGroup R G 0) (h1 : g ≠ 1) : 1 ≤ lowerDepth R G g := by
  classical
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  have hb' : ∀ i ≥ b + 1, lowerGroup R G i = ⊥ := fun i hi => hb i (by omega)
  rw [← lowerCount_eq_lowerDepth hb' h1, LocalFactor.SpectralConductor.lowerCount]
  exact Finset.card_pos.mpr
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos b), hg⟩⟩

/-- **Serre's Artin function** `a_G`: `a_G(g) = −[G:G_0] i_G(g)` for `g ≠ 1`, and
`a_G(1) = [G:G_0] Σ_h i_G(h)`. -/
def artinClassFunction [Fintype G] [DecidableEq G] : G → ℤ :=
  weighted R G (lowerDepth R G)

/-- **The Swan function**: `−[G:G_0] (i_G(g) − 1)` for `g ≠ 1` (`0` outside `G_0`), and the
opposite of the sum of these at `1`. -/
def swanClassFunction [Fintype G] [DecidableEq G] : G → ℤ :=
  weighted R G (fun g => lowerDepth R G g - 1)

section Properties

variable [Fintype G] [DecidableEq G]

/-- The Artin function is a class function. -/
theorem artinClassFunction_conj (g h : G) :
    artinClassFunction R G (h * g * h⁻¹) = artinClassFunction R G g :=
  weighted_conj (fun g h => lowerDepth_conj g h) g h

/-- The Swan function is a class function. -/
theorem swanClassFunction_conj (g h : G) :
    swanClassFunction R G (h * g * h⁻¹) = swanClassFunction R G g :=
  weighted_conj (fun g h => by simp only [lowerDepth_conj]) g h

theorem artinClassFunction_inv (g : G) : artinClassFunction R G g⁻¹ = artinClassFunction R G g :=
  weighted_inv (fun g => lowerDepth_inv g) g

theorem swanClassFunction_inv (g : G) : swanClassFunction R G g⁻¹ = swanClassFunction R G g :=
  weighted_inv (fun g => by simp only [lowerDepth_inv]) g

/-- **The Artin functional is the pairing with the Artin function**:
`artinFunctional f = |G|⁻¹ Σ_g f(g) a_G(g)`. -/
theorem artinFunctional_eq_sum_mul_artinClassFunction (f : G → ℂ) :
    artinFunctional R G f = (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (artinClassFunction R G g : ℂ) := by
  rw [artinFunctional_apply, artinClassFunction, sum_mul_weighted lowerDepth_one,
    ← (lowerGroup R G 0).index_mul_card]
  have hi : ((lowerGroup R G 0).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hc : (Nat.card (lowerGroup R G 0) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  push_cast
  field_simp

variable [IsNoetherianRing R] [FaithfulSMul G R]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The Artin expression is the pairing with the Artin function**:
`a(ρ) = |G|⁻¹ Σ_g χ_ρ(g) a_G(g)`. -/
theorem artinConductor_eq_sum_character_mul (ρ : Representation ℂ G V) :
    ((artinConductor R G ρ : ℚ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * (artinClassFunction R G g : ℂ) := by
  rw [← artinFunctional_character, artinFunctional_eq_sum_mul_artinClassFunction]

/-- **The Swan expression is the pairing with the Swan function**:
`sw(ρ) = |G|⁻¹ Σ_g χ_ρ(g) sw_G(g)`. -/
theorem swanConductor_eq_sum_character_mul (ρ : Representation ℂ G V) :
    ((swanConductor R G ρ : ℚ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * (swanClassFunction R G g : ℂ) := by
  classical
  have hc : (Nat.card (lowerGroup R G 0) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hi : ((lowerGroup R G 0).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  -- the Artin expression and the tame term as sums over `G`
  have hartin : ((artinConductor R G ρ : ℚ) : ℂ) =
      (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
        ∑ g, (lowerDepth R G g : ℂ) * (ρ.character 1 - ρ.character g) := by
    rw [← artinFunctional_character, artinFunctional_apply]
  have htame : ((fixedCodimension G ρ (lowerGroup R G 0) : ℚ) : ℂ) =
      (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ * ∑ g, (if g ∈ lowerGroup R G 0 then (1 : ℂ) else 0) *
        (ρ.character 1 - ρ.character g) := by
    have h := LocalFactor.SpectralConductor.weightedCodimension_eq ρ (lowerGroup R G 0)
      (lowerGroup R G 0)
    have hn : (Nat.card (lowerGroup R G 0) : ℚ) / Nat.card (lowerGroup R G 0) = 1 :=
      div_self (by exact_mod_cast Nat.card_pos.ne')
    rw [hn, one_mul] at h
    rw [h, Representation.char_one]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp [Representation.character]
  have hswan := artinConductor_eq_tame_add_swan R G ρ
  have hsw : ((swanConductor R G ρ : ℚ) : ℂ) =
      (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
        ∑ g, ((lowerDepth R G g - 1 : ℕ) : ℂ) * (ρ.character 1 - ρ.character g) := by
    have h : ((swanConductor R G ρ : ℚ) : ℂ) = ((artinConductor R G ρ : ℚ) : ℂ) -
        ((fixedCodimension G ρ (lowerGroup R G 0) : ℚ) : ℂ) := by
      rw [hswan]
      push_cast
      ring
    rw [h, hartin, htame, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h1 : g = 1
    · subst h1
      simp
    by_cases h0 : g ∈ lowerGroup R G 0
    · rw [ite_eq_left h0, Nat.cast_sub (one_le_lowerDepth h0 h1)]
      ring
    · rw [ite_eq_right h0, lowerDepth_eq_zero_of_not_mem h0]
      simp
  rw [hsw, swanClassFunction, sum_mul_weighted (by simp), ← (lowerGroup R G 0).index_mul_card]
  push_cast
  field_simp

end Properties

end Generic

namespace Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- The Artin function of the integer-ring action of `Aut(F/K)`. -/
def artinClassFunction : (F.Carrier ≃ₐ[K] F.Carrier) → ℤ := by
  classical
  letI := integerAction T K
  haveI := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  letI := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.artinClassFunction T.Integers (F.Carrier ≃ₐ[K] F.Carrier)

/-- The Swan function of the integer-ring action of `Aut(F/K)`. -/
def swanClassFunction : (F.Carrier ≃ₐ[K] F.Carrier) → ℤ := by
  classical
  letI := integerAction T K
  haveI := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  letI := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.swanClassFunction T.Integers (F.Carrier ≃ₐ[K] F.Carrier)

theorem artinClassFunction_conj (g h : F.Carrier ≃ₐ[K] F.Carrier) :
    artinClassFunction T K (h * g * h⁻¹) = artinClassFunction T K g := by
  classical
  let := integerAction T K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.artinClassFunction_conj T.Integers _ g h

theorem swanClassFunction_conj (g h : F.Carrier ≃ₐ[K] F.Carrier) :
    swanClassFunction T K (h * g * h⁻¹) = swanClassFunction T K g := by
  classical
  let := integerAction T K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.swanClassFunction_conj T.Integers _ g h

theorem artinClassFunction_inv (g : F.Carrier ≃ₐ[K] F.Carrier) :
    artinClassFunction T K g⁻¹ = artinClassFunction T K g := by
  classical
  let := integerAction T K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.artinClassFunction_inv T.Integers _ g

theorem swanClassFunction_inv (g : F.Carrier ≃ₐ[K] F.Carrier) :
    swanClassFunction T K g⁻¹ = swanClassFunction T K g := by
  classical
  let := integerAction T K
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact Ramification.swanClassFunction_inv T.Integers _ g

section Pairing

variable [Fintype (F.Carrier ≃ₐ[K] F.Carrier)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The Artin conductor is the pairing with the Artin function**:
`a(ρ) = |G|⁻¹ Σ_g χ_ρ(g) a_G(g)`. -/
theorem artinConductor_eq_sum_character_mul
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ((artinConductor T K ρ : ℚ) : ℂ) = (Nat.card (F.Carrier ≃ₐ[K] F.Carrier) : ℂ)⁻¹ *
      ∑ g, ρ.character g * (artinClassFunction T K g : ℂ) := by
  classical
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h := Ramification.artinConductor_eq_sum_character_mul T.Integers
    (F.Carrier ≃ₐ[K] F.Carrier) ρ
  unfold artinClassFunction
  convert h using 4
  · rfl
  · congr!

/-- **The Swan conductor is the pairing with the Swan function**. -/
theorem swanConductor_eq_sum_character_mul
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ((swanConductor T K ρ : ℚ) : ℂ) = (Nat.card (F.Carrier ≃ₐ[K] F.Carrier) : ℂ)⁻¹ *
      ∑ g, ρ.character g * (swanClassFunction T K g : ℂ) := by
  classical
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h := Ramification.swanConductor_eq_sum_character_mul T.Integers
    (F.Carrier ≃ₐ[K] F.Carrier) ρ
  unfold swanClassFunction
  convert h using 4
  · rfl
  · congr!

/-- The pairing `|G|⁻¹ Σ_g a_G(g⁻¹) χ_ρ(g)` of the Artin function with a character is the Artin
conductor. -/
theorem artinConductor_eq_pairing (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ((artinConductor T K ρ : ℚ) : ℂ) = (Fintype.card (F.Carrier ≃ₐ[K] F.Carrier) : ℂ)⁻¹ *
      ∑ g, (artinClassFunction T K g⁻¹ : ℂ) * ρ.character g := by
  rw [artinConductor_eq_sum_character_mul, Nat.card_eq_fintype_card]
  congr 1
  exact Finset.sum_congr rfl fun g _ => by rw [artinClassFunction_inv, mul_comm]

/-- The pairing `|G|⁻¹ Σ_g sw_G(g⁻¹) χ_ρ(g)` of the Swan function with a character is the Swan
conductor. -/
theorem swanConductor_eq_pairing (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ((swanConductor T K ρ : ℚ) : ℂ) = (Fintype.card (F.Carrier ≃ₐ[K] F.Carrier) : ℂ)⁻¹ *
      ∑ g, (swanClassFunction T K g⁻¹ : ℂ) * ρ.character g := by
  rw [swanConductor_eq_sum_character_mul, Nat.card_eq_fintype_card]
  congr 1
  exact Finset.sum_congr rfl fun g _ => by rw [swanClassFunction_inv, mul_comm]

end Pairing

/-- **The Artin function is a character** (Serre, *Local Fields*, VI §2, Theorem 1): it is the
character of a complex representation of `Aut(F/K)`. -/
theorem exists_repClass_character_eq_artinClassFunction :
    ∃ c : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier),
      FiniteRep.character c = fun g => (artinClassFunction T K g : ℂ) := by
  classical
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  refine FiniteRep.CharacterCompleteness.exists_character_eq _
    (fun g h => by simp only [artinClassFunction_conj]) fun a => ?_
  obtain ⟨n, hn⟩ := exists_nat_artinConductor T K (FiniteRep.VirtualCharacter.rep a).ρ
  refine ⟨n, ?_⟩
  rw [FiniteRep.CharacterCompleteness.pairing_apply, FiniteRep.VirtualCharacter.character_val]
  have h := artinConductor_eq_pairing T K (FiniteRep.VirtualCharacter.rep a).ρ
  rw [hn] at h
  rw [show ((n : ℕ) : ℂ) = (((n : ℚ)) : ℂ) by push_cast; rfl, h]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
  simp only [Equiv.inv_apply, inv_inv, mul_comm]
  rfl

/-- **The Swan function is a character**: it is the character of a complex representation of
`Aut(F/K)`. -/
theorem exists_repClass_character_eq_swanClassFunction :
    ∃ c : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier),
      FiniteRep.character c = fun g => (swanClassFunction T K g : ℂ) := by
  classical
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  refine FiniteRep.CharacterCompleteness.exists_character_eq _
    (fun g h => by simp only [swanClassFunction_conj]) fun a => ?_
  obtain ⟨n, hn⟩ := exists_nat_swanConductor T K (FiniteRep.VirtualCharacter.rep a).ρ
  refine ⟨n, ?_⟩
  rw [FiniteRep.CharacterCompleteness.pairing_apply, FiniteRep.VirtualCharacter.character_val]
  have h := swanConductor_eq_pairing T K (FiniteRep.VirtualCharacter.rep a).ρ
  rw [hn] at h
  rw [show ((n : ℕ) : ℂ) = (((n : ℚ)) : ℂ) by push_cast; rfl, h]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
  simp only [Equiv.inv_apply, inv_inv, mul_comm]
  rfl

/-- **The Artin representation** of `Aut(F/K)`, up to isomorphism: the class whose character is
the Artin function. -/
def artinRepClass : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier) :=
  (exists_repClass_character_eq_artinClassFunction T K).choose

/-- **The Swan representation** of `Aut(F/K)`, up to isomorphism. -/
def swanRepClass : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier) :=
  (exists_repClass_character_eq_swanClassFunction T K).choose

theorem character_artinRepClass :
    FiniteRep.character (artinRepClass T K) = fun g => (artinClassFunction T K g : ℂ) :=
  (exists_repClass_character_eq_artinClassFunction T K).choose_spec

theorem character_swanRepClass :
    FiniteRep.character (swanRepClass T K) = fun g => (swanClassFunction T K g : ℂ) :=
  (exists_repClass_character_eq_swanClassFunction T K).choose_spec

/-- The Artin representation is the only class with the Artin function as character. -/
theorem eq_artinRepClass {c : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier)}
    (hc : FiniteRep.character c = fun g => (artinClassFunction T K g : ℂ)) :
    c = artinRepClass T K := by
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact FiniteRep.VirtualCharacter.eq_of_character_eq (hc.trans (character_artinRepClass T K).symm)

/-- The Swan representation is the only class with the Swan function as character. -/
theorem eq_swanRepClass {c : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier)}
    (hc : FiniteRep.character c = fun g => (swanClassFunction T K g : ℂ)) :
    c = swanRepClass T K := by
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  exact FiniteRep.VirtualCharacter.eq_of_character_eq (hc.trans (character_swanRepClass T K).symm)

section Exponent

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The Artin exponent is a multiplicity**: `a(ρ) = dim Hom_G(A, ρ)`, with `A` a
representative of the Artin representation. -/
theorem artinExponent_eq_finrank_intertwiningMap
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinExponent T K ρ =
      finrank ℂ (Representation.IntertwiningMap (Quotient.out (artinRepClass T K)).ρ ρ) := by
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  have hA : (Quotient.out (artinRepClass T K)).character =
      fun g => (artinClassFunction T K g : ℂ) := by
    rw [← FiniteRep.character_classOf, ← character_artinRepClass T K]
    exact congrArg FiniteRep.character (Quotient.out_eq _)
  have h := FiniteCharacter.card_inv_mul_sum_eq_finrank (Quotient.out (artinRepClass T K)).ρ ρ
  have hc : ((artinExponent T K ρ : ℚ) : ℂ) = ((artinConductor T K ρ : ℚ) : ℂ) := by
    rw [artinExponent_cast]
  rw [artinConductor_eq_pairing] at hc
  have h' : ((artinExponent T K ρ : ℕ) : ℂ) =
      (finrank ℂ (Representation.IntertwiningMap (Quotient.out (artinRepClass T K)).ρ ρ) : ℂ) := by
    rw [← h]
    push_cast at hc
    rw [hc]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    change _ = (Quotient.out (artinRepClass T K)).character g⁻¹ * _
    rw [hA]
  exact_mod_cast h'

/-- **The Swan exponent is a multiplicity**: `sw(ρ) = dim Hom_G(Sw, ρ)`. -/
theorem swanExponent_eq_finrank_intertwiningMap
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    swanExponent T K ρ =
      finrank ℂ (Representation.IntertwiningMap (Quotient.out (swanRepClass T K)).ρ ρ) := by
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  have hA : (Quotient.out (swanRepClass T K)).character =
      fun g => (swanClassFunction T K g : ℂ) := by
    rw [← FiniteRep.character_classOf, ← character_swanRepClass T K]
    exact congrArg FiniteRep.character (Quotient.out_eq _)
  have h := FiniteCharacter.card_inv_mul_sum_eq_finrank (Quotient.out (swanRepClass T K)).ρ ρ
  have hc : ((swanExponent T K ρ : ℚ) : ℂ) = ((swanConductor T K ρ : ℚ) : ℂ) := by
    rw [swanExponent_cast]
  rw [swanConductor_eq_pairing] at hc
  have h' : ((swanExponent T K ρ : ℕ) : ℂ) =
      (finrank ℂ (Representation.IntertwiningMap (Quotient.out (swanRepClass T K)).ρ ρ) : ℂ) := by
    rw [← h]
    push_cast at hc
    rw [hc]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    change _ = (Quotient.out (swanRepClass T K)).character g⁻¹ * _
    rw [hA]
  exact_mod_cast h'

end Exponent

end Padic

end Langlands.Ramification
