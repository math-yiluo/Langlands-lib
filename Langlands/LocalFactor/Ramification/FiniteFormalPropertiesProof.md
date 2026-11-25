# The formal properties of the finite-Galois Artin and Swan conductors

This module proves the five sister statements of
`Langlands.LocalFactor.Ramification.FiniteStatement` that concern direct sums, duals,
unramified twists, vanishing and the tame formula, and with them the conjunction
`Langlands.Ramification.Padic.FiniteGaloisConductorStatement`:

| Statement | Theorem |
| --- | --- |
| `FiniteGaloisConductorDirectSumStatement` | `finiteGaloisConductorDirectSum` |
| `FiniteGaloisConductorDualStatement` | `finiteGaloisConductorDual` |
| `FiniteGaloisConductorUnramifiedTwistStatement` | `finiteGaloisConductorUnramifiedTwist` |
| `FiniteGaloisConductorVanishingStatement` | `finiteGaloisConductorVanishing` |
| `FiniteGaloisTameArtinStatement` | `finiteGaloisTameArtin` |
| `FiniteGaloisConductorStatement` | `finiteGaloisConductor` |

All in the name space `Langlands.Ramification.Padic`. The other two components of the
conjunction are proved elsewhere: integrality by `finiteGaloisConductorIntegrality`
(`FiniteIntegralityProof`) and additivity in short exact sequences by
`finiteGaloisConductorExactSequence` (`FiniteExactSequenceProof`).

## Statements proved

Throughout, `p` is a prime, `F : PadicField.{uL} p` with data `T : F.TopologicalData`, `K` a field
in a scalar tower `Padic p → K → F.Carrier` (universe `uK`), `G = F.Carrier ≃ₐ[K] F.Carrier`,
`a_K = Padic.artinConductor T K`, `sw_K = Padic.swanConductor T K`: the rational sums
`Σ_{i≥0} |G_i|/|G_0| · codim V^{G_i}` and `Σ_{i≥1} |G_i|/|G_0| · codim V^{G_i}` over the lower
groups `G_i = lowerRamificationGroup T K i` of the action on the integers. `V`, `W` are
finite-dimensional complex vector spaces in universes `uV`, `uW`. Each statement carries the
hypothesis `[IsGalois K F.Carrier]`; no proof uses it.

```lean
theorem finiteGaloisConductorDirectSum {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    FiniteGaloisConductorDirectSumStatement T K (V := V) (W := W)
```

that is, `a_K(ρ ⊕ σ) = a_K(ρ) + a_K(σ)` and `sw_K(ρ ⊕ σ) = sw_K(ρ) + sw_K(σ)` for Mathlib's
`ρ.prod σ` on `V × W`.

```lean
theorem finiteGaloisConductorDual {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorDualStatement T K (V := V)
```

that is, `a_K(ρ^*) = a_K(ρ)` and `sw_K(ρ^*) = sw_K(ρ)` for Mathlib's `ρ.dual` on
`Module.Dual ℂ V`.

```lean
theorem finiteGaloisConductorUnramifiedTwist {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorUnramifiedTwistStatement T K (V := V)
```

that is, for `χ : G →* ℂˣ` with `χ g = 1` on `inertia T K`, the Library's twist
`Langlands.twist χ ρ` has the conductors of `ρ`.

```lean
theorem finiteGaloisConductorVanishing {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorVanishingStatement T K (V := V)
```

that is, `a_K(ρ) = 0` iff every element of `inertia T K` fixes every vector, and `sw_K(ρ) = 0`
iff every element of `lowerRamificationGroup T K 1` does.

```lean
theorem finiteGaloisTameArtin {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisTameArtinStatement T K (V := V)
```

that is, if `lowerRamificationGroup T K 1` acts trivially then
`a_K(ρ) = fixedCodimension G ρ (inertia T K)`.

```lean
theorem finiteGaloisConductor : FiniteGaloisConductorStatement.{uK, uL, uU, uV, uW}
```

The level parameters of each theorem are those of its statement, in the same order, and the
binders of each theorem are the statement's, in the same order.

## Proof outline

Everything is proved for a finite group `G` acting faithfully on a Noetherian local ring `R`,
summand by summand: the `i`th summand of both expressions is
`conductorTerm R G ρ i = |G_i|/|G_0| · fixedCodimension G ρ G_i`.

- **Direct sum.** `0 → V → V × W → W → 0` with Mathlib's intertwiners `inl` and `snd` is a short
  exact sequence; the Library's additivity `artinConductor_eq_add`, `swanConductor_eq_add`
  (`FiniteExactSequenceProof`) applies.
- **Dual.** For a subgroup `H` of a finite group, `dim V^H = |H|⁻¹ Σ_{h∈H} tr ρ(h)` (the
  Library's `SpectralConductor.finrank_fixedVectors`). The character of the dual is
  `h ↦ tr ρ(h⁻¹)` (Mathlib's `Representation.char_dual`) and `h ↦ h⁻¹` permutes `H`, so
  `dim (V^*)^H = dim V^H`; with `dim V^* = dim V` every codimension, hence every summand, is
  unchanged.
- **Twist.** Every `G_i` lies in `G_0` (the filtration is decreasing). On `G_0` the twist acts as
  `ρ`, so it has the same `G_i`-fixed vectors (`fixedVectors_twist_eq_of_le_ker`,
  `Representation/Twist/AdmissibilityProof`): every summand is unchanged.
- **Vanishing.** The weight `|G_i|/|G_0|` is positive, so a summand vanishes iff
  `codim V^{G_i} = 0`, iff `G_i` acts trivially. The Artin expression is the tame summand
  `codim V^{G_0}` plus the non-negative Swan expression; it vanishes iff `G_0` acts trivially,
  and then so does every `G_i ⊆ G_0`. The Swan expression is a finite sum of non-negative
  summands containing the summand `i = 1`; it vanishes iff `G_1` acts trivially, and then so does
  every `G_{i+1} ⊆ G_1`.
- **Tame.** If `G_1` acts trivially the Swan expression is `0`, and the Library's decomposition
  `artinConductor_eq_tame_add_swan` leaves the tame summand.

For the p-adic expressions the proofs install the integer action `Padic.integerAction T K` and
the published instance facts `HerbrandBridge.integerAction_faithful`,
`SpectralConductor.integerRing_noetherian'`, `SpectralConductor.automorphismGroup_finite'`, as
`FiniteExactSequenceProof` does, and use `lowerRamificationGroup_zero` (`G_0 = inertia T K`).

## Declarations, in order

Name space `Langlands.Ramification` (generic). `R` a commutative local ring with an action of the
group `G` by ring automorphisms; where the expressions occur, `R` Noetherian, the action faithful
and `G` finite.

- `fixedCodimension_eq_zero_iff (G) (ρ : Representation k G V) (H : Subgroup G) :
  fixedCodimension G ρ H = 0 ↔ ∀ g ∈ H, ∀ v : V, ρ g v = v` (any field `k`, `V`
  finite-dimensional). Proof: `dim V ≤ dim V^H` makes `V^H = ⊤` (`Submodule.eq_top_of_finrank_eq`).
- `fixedCodimension_dual (G) [Finite G] (ρ : Representation ℂ G V) (H : Subgroup G) :
  fixedCodimension G ρ.dual H = fixedCodimension G ρ H`.
- `conductorTerm_twist (R G) (ρ : Representation k G V) (χ : G →* kˣ)
  (hχ : ∀ g ∈ lowerGroup R G 0, χ g = 1) (i : ℕ) :
  conductorTerm R G (Langlands.twist χ ρ) i = conductorTerm R G ρ i`.
- `conductorTerm_eq_zero_iff (R G) [Finite G] (ρ : Representation k G V) (i : ℕ) :
  conductorTerm R G ρ i = 0 ↔ ∀ g ∈ lowerGroup R G i, ∀ v : V, ρ g v = v`.
- `conductorTerm_dual (R G) [Finite G] (ρ : Representation ℂ G V) (i : ℕ) :
  conductorTerm R G ρ.dual i = conductorTerm R G ρ i`.
- `artinConductor_dual`, `swanConductor_dual (R G) (ρ : Representation ℂ G V) :
  artinConductor R G ρ.dual = artinConductor R G ρ` (resp. `swanConductor`).
- `artinConductor_prod`, `swanConductor_prod (R G) (ρ : Representation k G V)
  (σ : Representation k G W) : artinConductor R G (ρ.prod σ) = artinConductor R G ρ +
  artinConductor R G σ` (resp. `swanConductor`), `k` of characteristic zero.
- `artinConductor_twist`, `swanConductor_twist (R G) (ρ) (χ : G →* kˣ)
  (hχ : ∀ g ∈ lowerGroup R G 0, χ g = 1) :
  artinConductor R G (Langlands.twist χ ρ) = artinConductor R G ρ` (resp. `swanConductor`).
- `artinConductor_eq_zero_iff (R G) (ρ : Representation k G V) :
  artinConductor R G ρ = 0 ↔ ∀ g ∈ lowerGroup R G 0, ∀ v : V, ρ g v = v`.
- `swanConductor_eq_zero_iff (R G) (ρ : Representation k G V) :
  swanConductor R G ρ = 0 ↔ ∀ g ∈ lowerGroup R G 1, ∀ v : V, ρ g v = v`.
- `artinConductor_eq_fixedCodimension_of_lowerGroup_one (R G) (ρ : Representation k G V)
  (h : ∀ g ∈ lowerGroup R G 1, ∀ v : V, ρ g v = v) :
  artinConductor R G ρ = fixedCodimension G ρ (lowerGroup R G 0)`.

Name space `Langlands.Ramification.Padic`, with the variables of the statements above (no Galois
hypothesis), `ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V`, `σ` on `W`:

- `artinConductor_prod T K ρ σ`, `swanConductor_prod T K ρ σ`;
- `artinConductor_dual T K ρ`, `swanConductor_dual T K ρ`;
- `artinConductor_twist T K ρ χ (hχ : ∀ g ∈ inertia T K, χ g = 1)`, `swanConductor_twist`;
- `artinConductor_eq_zero_iff T K ρ :
  artinConductor T K ρ = 0 ↔ ∀ g ∈ inertia T K, ∀ v : V, ρ g v = v`;
- `swanConductor_eq_zero_iff T K ρ :
  swanConductor T K ρ = 0 ↔ ∀ g ∈ lowerRamificationGroup T K 1, ∀ v : V, ρ g v = v`;
- `artinConductor_eq_fixedCodimension_of_lowerRamificationGroup_one T K ρ h :
  artinConductor T K ρ = (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ)`;
- the six theorems of the table above.

## Literature

Jean-Pierre Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979
(`/srv/central-library/Serre--Local Fields--1979.pdf`; PDF page = printed page + 7 in
Chapter VI), Chapter VI, §2:

- printed p. 99: the Artin function `a_G` and `f(φ) = (φ, a_G)`; the remark
  `a_G(s⁻¹) = a_G(s)`. Since `f` is linear in the character, it is additive on direct sums, and
  since `a_G(s⁻¹) = a_G(s)` and the character of the dual is `χ(s⁻¹)`, `f(χ̄) = f(χ)`. Serre states
  neither as a numbered result; the Library proves both summand by summand.
- printed pp. 100–101, Proposition 2 and Corollaries 1 and 1′: `f(χ) = Σ_i (g_i/g_0) codim V^{G_i}`,
  the Library's definition of the Artin expression. The vanishing and tame statements are read
  off this sum; Serre does not state them as such.

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular
Functions of One Variable II*, Lecture Notes in Mathematics 349, Springer, 1973, 501–597
(`/srv/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`;
PDF page = printed page − 500), §4.5, printed pp. 537–538, formula (4.5.4):
`a(V) = sw(V) + dim V − dim V^I`. The Swan expression is the Library's positive-index tail of the
Artin sum, which is the same decomposition; the vanishing and tame statements for Swan are read
off it.
