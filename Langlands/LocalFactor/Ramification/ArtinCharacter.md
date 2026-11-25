# The Artin and Swan characters

This module defines Serre's Artin function and the Swan function of a finite group acting on a
local ring, proves that the Artin and Swan expressions of a representation are their pairings
with its character, and proves that for the automorphism group of a finite extension of p-adic
fields both functions are characters of representations (the Artin and the Swan representation,
up to isomorphism), whose multiplicities in a representation are its Artin and Swan exponents.

## Definitions

Name space `Langlands.Ramification`. `R` a commutative local ring with an action of a finite group
`G` by ring automorphisms, `G_i = lowerGroup R G i`, `i_G = lowerDepth R G` (the number of `i` with
`g ∈ G_i`; Serre's `i_G(g)` for `g ≠ 1`, `0` at `g = 1`, `ConductorFunctional`), `[G:G_0]` the
index of `G_0`.

```lean
def ArtinCharacter.weighted [Fintype G] [DecidableEq G] (d : G → ℕ) (g : G) : ℤ :=
  if g = 1 then (((lowerGroup R G 0).index * ∑ h, d h : ℕ) : ℤ)
  else -(((lowerGroup R G 0).index * d g : ℕ) : ℤ)
def artinClassFunction [Fintype G] [DecidableEq G] : G → ℤ :=
  ArtinCharacter.weighted R G (lowerDepth R G)
def swanClassFunction [Fintype G] [DecidableEq G] : G → ℤ :=
  ArtinCharacter.weighted R G (fun g => lowerDepth R G g - 1)
```

So `a_G(g) = −[G:G_0] i_G(g)` and `sw_G(g) = −[G:G_0] (i_G(g) − 1)` for `g ≠ 1` (both `0` outside
`G_0`, where `i_G = 0` and the truncated `i_G − 1` is `0`), and the values at `1` make the sums over
`G` vanish.

Name space `Langlands.Ramification.Padic`, for `F : PadicField.{uL} p`, `T : F.TopologicalData`,
`K` a field in a scalar tower `Padic p → K → F.Carrier`, `G = F.Carrier ≃ₐ[K] F.Carrier` with its
action on the integers (`integerAction T K`):

```lean
def artinClassFunction : (F.Carrier ≃ₐ[K] F.Carrier) → ℤ   -- the generic one for this action
def swanClassFunction : (F.Carrier ≃ₐ[K] F.Carrier) → ℤ
def artinRepClass : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier)
def swanRepClass : FiniteRep.RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier)
```

`artinRepClass T K` is the class (in `FiniteRep.RepClass`, isomorphism classes of finite-dimensional
complex representations) whose character is the Artin function; it exists by
`exists_repClass_character_eq_artinClassFunction` and is unique by `eq_artinRepClass`. Likewise
`swanRepClass`.

## Theorems

Generic (`Langlands.Ramification`; `[Fintype G] [DecidableEq G]`, and for the conductors
`[IsNoetherianRing R] [FaithfulSMul G R]`, `V` a finite-dimensional complex vector space):

```lean
theorem lowerDepth_conj (g h : G) : lowerDepth R G (h * g * h⁻¹) = lowerDepth R G g
theorem lowerDepth_inv (g : G) : lowerDepth R G g⁻¹ = lowerDepth R G g
theorem lowerDepth_eq_zero_of_not_mem {g : G} (hg : g ∉ lowerGroup R G 0) : lowerDepth R G g = 0
theorem one_le_lowerDepth [IsNoetherianRing R] [FaithfulSMul G R] [Finite G] {g : G}
    (hg : g ∈ lowerGroup R G 0) (h1 : g ≠ 1) : 1 ≤ lowerDepth R G g
theorem artinClassFunction_conj (g h : G) :
    artinClassFunction R G (h * g * h⁻¹) = artinClassFunction R G g
theorem swanClassFunction_conj (g h : G) :
    swanClassFunction R G (h * g * h⁻¹) = swanClassFunction R G g
theorem artinClassFunction_inv (g : G) : artinClassFunction R G g⁻¹ = artinClassFunction R G g
theorem swanClassFunction_inv (g : G) : swanClassFunction R G g⁻¹ = swanClassFunction R G g
theorem artinFunctional_eq_sum_mul_artinClassFunction (f : G → ℂ) :
    artinFunctional R G f = (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (artinClassFunction R G g : ℂ)
theorem artinConductor_eq_sum_character_mul (ρ : Representation ℂ G V) :
    ((artinConductor R G ρ : ℚ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * (artinClassFunction R G g : ℂ)
theorem swanConductor_eq_sum_character_mul (ρ : Representation ℂ G V) :
    ((swanConductor R G ρ : ℚ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * (swanClassFunction R G g : ℂ)
```

and the helpers `ArtinCharacter.weighted_eq`, `sum_mul_weighted`
(`Σ_g f(g) w_d(g) = [G:G_0] Σ_g d(g) (f(1) − f(g))` when `d(1) = 0`), `weighted_conj`,
`weighted_inv`.

p-adic (`Langlands.Ramification.Padic`; `G = F.Carrier ≃ₐ[K] F.Carrier`, no Galois hypothesis):

```lean
theorem artinClassFunction_conj (g h : G) :
    artinClassFunction T K (h * g * h⁻¹) = artinClassFunction T K g      -- and Swan, and `_inv`
theorem artinConductor_eq_sum_character_mul [Fintype G] (ρ : Representation ℂ G V) :
    ((artinConductor T K ρ : ℚ) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * (artinClassFunction T K g : ℂ)   -- and Swan
theorem artinConductor_eq_pairing [Fintype G] (ρ : Representation ℂ G V) :
    ((artinConductor T K ρ : ℚ) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, (artinClassFunction T K g⁻¹ : ℂ) * ρ.character g  -- and Swan
theorem exists_repClass_character_eq_artinClassFunction :
    ∃ c : FiniteRep.RepClass ℂ G, FiniteRep.character c = fun g => (artinClassFunction T K g : ℂ)
theorem exists_repClass_character_eq_swanClassFunction :
    ∃ c : FiniteRep.RepClass ℂ G, FiniteRep.character c = fun g => (swanClassFunction T K g : ℂ)
theorem character_artinRepClass :
    FiniteRep.character (artinRepClass T K) = fun g => (artinClassFunction T K g : ℂ)  -- and Swan
theorem eq_artinRepClass {c : FiniteRep.RepClass ℂ G}
    (hc : FiniteRep.character c = fun g => (artinClassFunction T K g : ℂ)) :
    c = artinRepClass T K                                                          -- and Swan
theorem artinExponent_eq_finrank_intertwiningMap (ρ : Representation ℂ G V) :
    artinExponent T K ρ =
      finrank ℂ (Representation.IntertwiningMap (Quotient.out (artinRepClass T K)).ρ ρ)
theorem swanExponent_eq_finrank_intertwiningMap (ρ : Representation ℂ G V) :
    swanExponent T K ρ =
      finrank ℂ (Representation.IntertwiningMap (Quotient.out (swanRepClass T K)).ρ ρ)
```

## Proofs

- **Pairing formulas.** With `w_d` the weighted function of a weight `d` with `d(1) = 0`,
  `w_d(g) = [G:G_0]((Σ_h d(h))·[g = 1] − d(g))`, so
  `Σ_g f(g) w_d(g) = [G:G_0] Σ_g d(g)(f(1) − f(g))`. Since `|G| = [G:G_0]·|G_0|`, the Artin
  functional `|G_0|⁻¹ Σ_g i_G(g)(f(1) − f(g))` (`ConductorFunctional`) is `|G|⁻¹ Σ_g f(g) a_G(g)`,
  and `artinFunctional_character` gives the Artin formula. For Swan: the Swan expression is the
  Artin expression minus the tame term `codim V^{G_0} = |G_0|⁻¹ Σ_{g ∈ G_0}(χ(1) − χ(g))`
  (`SpectralConductor.weightedCodimension_eq`), so it is `|G_0|⁻¹ Σ_g (i_G(g) − [g ∈ G_0])(χ(1) − χ(g))`,
  and `i_G(g) − [g ∈ G_0] = i_G(g) − 1` in `ℕ` for `g ≠ 1` (`one_le_lowerDepth`,
  `lowerDepth_eq_zero_of_not_mem`).
- **Class functions.** The lower groups are normal and closed under inverses, so `i_G` is invariant
  under conjugation and inversion.
- **Characters.** For an irreducible class `a` with representative `ρ_a`, the pairing
  `|G|⁻¹ Σ_g χ_a(g⁻¹) a_G(g)` equals `|G|⁻¹ Σ_g χ_a(g) a_G(g)` (reindex, `a_G(g⁻¹) = a_G(g)`), which is
  the Artin conductor of `ρ_a`, a natural number (`Padic.exists_nat_artinConductor`,
  `ArtinExponent`). By completeness of the irreducible characters
  (`FiniteRep.CharacterCompleteness.exists_character_eq`), the class function `a_G` is the
  character of a class. Uniqueness: characters determine classes
  (`FiniteRep.VirtualCharacter.eq_of_character_eq`). Swan the same with
  `Padic.exists_nat_swanConductor`.
- **Multiplicities.** `dim Hom_G(A, V) = |G|⁻¹ Σ_g χ_A(g⁻¹) χ_V(g)`
  (`FiniteCharacter.card_inv_mul_sum_eq_finrank`), and `χ_A = a_G`; this is the Artin conductor of
  `V`, which is the Artin exponent.

## Literature

- Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter VI, §2 (PDF page = printed page + 7):
  the function `a_G(s) = −f i_G(s)` (`s ≠ 1`), `a_G(1) = f Σ_{s≠1} i_G(s)`, `f` the residue
  degree, and Theorem 1 (`a_G` is the character of a representation), printed p. 99; Proposition 2
  and Corollaries 1, 1′ (the conductor as the weighted codimension sum), pp. 100–101;
  "Terminology" (the Artin representation, defined only up to isomorphism), p. 103. The Library's
  `[G:G_0]` is Serre's `f` when `G` is the Galois group of `F/K`; for a non-Galois `F/K` the
  Library's statements are about `Aut(F/K)`, a case Serre does not consider.
- Serre, *Linear Representations of Finite Groups*, GTM 42, Springer, 1977, §19.1 "Artin and Swan
  representations", printed pp. 159–160 (PDF page = printed page + 6 there): `a_G`, the theorem that
  it is a character, `sw_G = a_G − u_G` with `sw_G(s) = 1 − i_G(s)` for `s ≠ 1`, and that `sw_G` is a
  character, under the assumption that `E` and `F` have the same residue field (`G = G_0`). The
  Library's Swan function reduces to Serre's when `G = G_0`; in general it is
  `−[G:G_0](i_G − 1)` on `G_0 ∖ {1}` and `0` off `G_0`, whose pairing is the Library's Swan expression
  (the positive-index tail of the Artin sum, Serre's `g·sw_G = Σ_{i≥1} g_i Ind(u_{G_i})` on p. 160).
- Deligne, *Les constantes des équations fonctionnelles des fonctions L*, LNM 349 (1973), §4.5,
  printed p. 537, (4.5.1): `sw_{I/J}(σ) = 1 − i_{I/J}(σ)` for `σ ≠ e` on the inertia quotient, and
  the Swan representation as a representation with this character; (4.5.4), p. 538:
  `a(V) = dim Hom_{I/J}(A_{I/J}, V)`, which is the form of `artinExponent_eq_finrank_intertwiningMap`.
