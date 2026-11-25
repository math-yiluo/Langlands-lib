# The Artin conductor as a linear functional of the character

Module `Langlands.LocalFactor.Ramification.ConductorFunctional`, namespaces
`Langlands.Ramification` and `Langlands.Ramification.Padic`.

For a finite group `G` acting faithfully by ring automorphisms on a Noetherian local ring `R`,
with lower groups `G_i = lowerGroup R G i` (the kernel of the action on `R/𝔪^{i+1}`), this
module defines the depth `i_G(g)` of an element and the Artin functional, a `ℂ`-linear form on
complex functions on `G`, and proves that on the character of a finite-dimensional complex
representation `ρ` the functional is the Library's Artin expression `artinConductor R G ρ`.
The conductor is therefore a function of the character, additive on virtual characters. The
module also proves non-negativity of the Artin and Swan expressions, and for the p-adic
conductors the decomposition `a = codim V^{G_0} + sw` and the dependence on the character only.

## Statements

Generic part, for `(R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
[MulSemiringAction G R]`:

```lean
def Langlands.Ramification.lowerDepth (g : G) : ℕ :=
  Nat.card {i : ℕ // g ∈ lowerGroup R G i}

theorem Langlands.Ramification.lowerDepth_one : lowerDepth R G 1 = 0

theorem Langlands.Ramification.lowerCount_eq_lowerDepth {b : ℕ}
    (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) {g : G} (hg : g ≠ 1) :
    LocalFactor.SpectralConductor.lowerCount R G b g = lowerDepth R G g

def Langlands.Ramification.artinFunctional [Fintype G] : (G → ℂ) →ₗ[ℂ] ℂ
-- f ↦ (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ * ∑ g : G, (lowerDepth R G g : ℂ) * (f 1 - f g)

theorem Langlands.Ramification.artinFunctional_apply [Fintype G] (f : G → ℂ) :
    artinFunctional R G f = (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
      ∑ g : G, (lowerDepth R G g : ℂ) * (f 1 - f g)

theorem Langlands.Ramification.artinFunctional_const [Fintype G] (c : ℂ) :
    artinFunctional R G (fun _ => c) = 0

theorem Langlands.Ramification.artinFunctional_character [Fintype G]
    [IsNoetherianRing R] [FaithfulSMul G R]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    artinFunctional R G ρ.character = ((artinConductor R G ρ : ℚ) : ℂ)

theorem Langlands.Ramification.artinConductor_nonneg
    [IsNoetherianRing R] [FaithfulSMul G R] [Finite G]
    {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : 0 ≤ artinConductor R G ρ

theorem Langlands.Ramification.swanConductor_nonneg  -- same binders
    (ρ : Representation k G V) : 0 ≤ swanConductor R G ρ
```

`lowerDepth R G g` is Serre's `i_G(g)` for `g ≠ 1` (the number of `i ≥ 0` with `g ∈ G_i`); at
`g = 1` the set of indices is infinite and `Nat.card` gives `0`, which is harmless because the
functional weights `f 1 − f 1 = 0` there. No finiteness hypothesis enters the definition.

p-adic part, for `{p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
(K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
[IsScalarTower (Padic p) K F.Carrier]`, and a field `k` with a finite-dimensional
representation `ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V`:

```lean
theorem Langlands.Ramification.Padic.artinConductor_nonneg (ρ) : 0 ≤ artinConductor T K ρ
theorem Langlands.Ramification.Padic.swanConductor_nonneg (ρ) : 0 ≤ swanConductor T K ρ
theorem Langlands.Ramification.Padic.artinConductor_eq_tame_add_swan (ρ) :
    artinConductor T K ρ =
      (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ) + swanConductor T K ρ

theorem Langlands.Ramification.Padic.artinConductor_eq_of_character_eq
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V}
    {σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W}
    (h : ρ.character = σ.character) : artinConductor T K ρ = artinConductor T K σ
```

None of these uses the Galois hypothesis.

## Proof outline

The Library's class-function formula `LocalFactor.SpectralConductor.artinConductor_eq_classSum`
(module `Langlands.LocalFactor.SpectralConductorClassFunction`) gives, for any bound `b` past
which the lower groups vanish,
`a(ρ) = |G_0|⁻¹ Σ_g m_b(g) (dim V − tr ρ(g))`, where `m_b(g)` is the number of `i < b` with
`g ∈ G_i` (`lowerCount`). For `g ≠ 1`, `g ∉ G_i` for `i ≥ b`, so `m_b(g) = i_G(g)`
(`lowerCount_eq_lowerDepth`, by `Nat.card_congr` between the filtered range and the subtype).
For `g = 1` both summands vanish. Since `dim V = χ_ρ(1)` (`Representation.char_one`) and
`tr ρ(g) = χ_ρ(g)`, the right side is the Artin functional of `χ_ρ`. A bound `b` exists by
`exists_lowerGroup_eq_bot` (Krull intersection, faithfulness and finiteness).

Non-negativity: the expressions are finite sums of the non-negative terms `conductorTerm`
(`conductorTerm_nonneg`).

The p-adic statements install the integer action `Padic.integerAction T K` with the published
instance facts `HerbrandBridge.integerAction_faithful` (module
`Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`),
`LocalFactor.SpectralConductor.integerRing_noetherian'` and
`LocalFactor.SpectralConductor.automorphismGroup_finite'` (module
`Langlands.LocalFactor.SpectralConductorFunctional`), the same three that
`FiniteExactSequenceProof` uses, and apply the generic statements; the
p-adic definitions unfold to the generic ones for that action, and the instance arguments are
proofs of propositions. The tame decomposition is the generic
`Ramification.artinConductor_eq_tame_add_swan` with `lowerGroup _ _ 0 = inertia T K`
(`Padic.lowerRamificationGroup_zero`). Dependence on the character only: the Artin functional of
equal characters is equal, and `ℚ → ℂ` is injective.

## Declarations, in order

1. `lowerDepth`, `lowerDepth_one` (the index set at `1` is infinite).
2. `lowerCount_eq_lowerDepth` — the comparison with the truncated count of
   `SpectralConductorClassFunction`. The Library has two further copies of the truncated count,
   `SpectralConductor.galoisLowerCount` and `NonabelianSystem.DeligneHenniart.TopLayer.lowerDepth`;
   `lowerDepth` here is the untruncated notion they can be compared with.
3. `artinFunctional`, `artinFunctional_apply`, `artinFunctional_const`,
   `artinFunctional_character`.
4. `artinConductor_nonneg`, `swanConductor_nonneg`.
5. `Padic.artinConductor_nonneg`, `Padic.swanConductor_nonneg`,
   `Padic.artinConductor_eq_tame_add_swan`, `Padic.artinConductor_eq_of_character_eq`.

## Sources

Serre, *Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`), printed
pages 99–101: the Artin character `a_G(s) = −f·i_G(s)` for `s ≠ 1`, Proposition 2 (the weighted
codimension formula) and Corollary 1′ (the conductor of a representation as that sum). The
functional here is the pairing `f ↦ (f, a_G)` of Serre's §2 written with `|G_0|⁻¹` in place
of `f/|G|` and without the value at `1`, which the constant functions do not see. Deligne,
*Les constantes des équations fonctionnelles des fonctions L* (1973), §4.5, equation (4.5.4),
printed page 538 (literature ID `deligne-1973-local-constants`): Artin is Swan plus the
codimension of the inertia invariants.
