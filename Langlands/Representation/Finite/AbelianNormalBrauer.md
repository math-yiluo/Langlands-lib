# Brauer induction relative to an abelian normal subgroup

Lean module: `Langlands.Representation.Finite.AbelianNormalBrauer`.

## Source

P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981), §2, Proposition 2.2,
printed p. 101 (PDF p. 13). Part (ii) says the following. Let `G` be a finite group, `A`
an abelian normal subgroup and `V` a representation with `V^A = 0`. Then in `R(G)` one
can write `V = Σ nᵢ Ind_{Hᵢ}^G (χᵢ)` with integers `nᵢ`, subgroups `Hᵢ ⊇ A`, and
characters `χᵢ` of `Hᵢ` that are nontrivial on `A`.

The module formalizes part (ii) for complex representations, in the genuine split
representation group `VirtualRep ℂ G`. Part (i) is not formalized separately.

## Definitions

- `abelianNormalBrauerGenerators G A : Set (VirtualRep ℂ G)` is the set of classes
  `ofClass (induce S (classOf (oneDimensional χ)))`. Here `S` is a subgroup with
  `A ≤ S`, and `χ : S →* ℂˣ` is a rank-one character with `χ a ≠ 1` for some `a ∈ A`.
  The inclusion `A → S` is `Subgroup.inclusion`. These are actual induced
  representations, not character-level objects.
- `abelianNormalBrauerSpan G A` is the integral span of these classes.
- `AbelianNormalBrauerStatement G : Prop` says the following. Take a normal subgroup `A`
  whose elements commute pairwise, and a finite-dimensional complex representation `V`
  whose only vector fixed by all of `A` is `0`. Then `ofClass (classOf V)` lies in
  `abelianNormalBrauerSpan G A`. This is exactly DH81 2.2(ii) above: the hypothesis
  `V^A = 0` and the integral combination of inductions from subgroups containing `A`,
  by characters nontrivial on `A`.

## Main theorem

`Langlands.FiniteRep.abelianNormalBrauer (G) [Group G] [Fintype G] :
AbelianNormalBrauerStatement G`. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof (as implemented)

The proof works at the level of characters and then uses the faithfulness of
`virtualCharacter` (`VirtualCharacter.faithfulness`). The isotypic decomposition
(2.1.1) and the reduction to the central case in DH81 are replaced by direct character
computations. The main steps live in the namespace `AbelianNormalBrauer`.

1. **Characters of `A`.** Characters of `A` are identified with additive characters of
   `Additive A` (`charEquiv`), which gives a finite type (`charFintype`) and dual
   orthogonality (`sum_char_apply`). A nontrivial character has sum zero
   (`sum_char_eq_zero`).
2. **Projections.** For a character `ε` of `A`, put
   `proj A ε f g = |A|⁻¹ Σ_{a ∈ A} ε(a⁻¹) f(a g)`. The projections sum to the identity
   (`sum_proj`). `G` acts on characters by `(x • ε)(a) = ε(x⁻¹ a x)` (`charAction`). For
   class functions, `proj ε f (x⁻¹ g x) = proj (x • ε) f g` (`proj_conj`).
3. **Operator identities.** Let `E_ε = |A|⁻¹ Σ ε(a⁻¹) ρ(a)` (`isoOp`). Then
   `proj ε χ_V g = tr(E_ε ρ(g))` (`proj_character`). The `E_ε` are orthogonal
   idempotents (`isoOp_idem`, `isoOp_mul_isoOp_of_ne`), and
   `E_ε ρ(g) = ρ(g) E_{g⁻¹•ε}` (`isoOp_mul_rho`). Two consequences follow:
   - (b) `proj ε χ_V g = 0` unless `g` fixes `ε` (`proj_character_eq_zero`).
   - (c) If `V^A = 0`, then `E_1 = 0`, so `proj 1 χ_V = 0` (`proj_one_character`).
4. **Orbits.** Let `Z(r)` be the stabilizer of `r`. Counting the fibres of `x ↦ x • r`
   (`sum_smul_eq`), together with (b) and `proj_conj`, gives the following identity
   (`ind_proj_stabilizer`). The induction from `Z(r)` of the restriction of
   `proj r χ_V` equals `Σ_{ε ∈ G·r} proj ε χ_V`. Summing over the orbit quotient,
   `χ_V = Σ_{orbits} Ind_{Z(r)}^G (proj r χ_V)` (`character_eq_sum_orbits`).
5. **Lemma C (projection of an induced character).** Let `H` be finite, `A ⊴ H`, and
   `η` an `H`-invariant character of `A`. Let `S ≤ H` and `χ : S →* ℂˣ`.
   - If `η` and `χ` differ somewhere on `A ∩ S`, then `proj η (Ind_S χ) = 0`
     (`proj_ind_eq_zero`).
   - Otherwise `proj η (Ind_S χ) = Ind_{A ⊔ S} μ` (`proj_ind_eq`). Here `μ(a s) = η(a) χ(s)`
     (`supChar`). `μ` is well defined because `η = χ` on `A ∩ S`, and multiplicative
     because `η` is invariant.

   The proof writes the projection as `|A|⁻¹|S|⁻¹ Σ_x Φ(x⁻¹ g x)` (`proj_ind`), where
   `Φ(y) = Σ_a η(a⁻¹) χ̃(a y)` and `χ̃` is `χ` extended by zero. On `A ⊔ S`, `Φ` is
   `pairing · μ`, and off `A ⊔ S` it vanishes. Here
   `pairing = Σ_{c ∈ A ∩ S} η(c)⁻¹ χ(c)`, which is `|A ∩ S|` or `0`. The constants
   combine through `|A ⊔ S| · |A ∩ S| = |A| · |S|` (`card_sup_mul`, which uses
   `Subgroup.relIndex_sup_left`).
6. **Assembly.** Let `r ≠ 1` and `H = Z(r)`. Then `A ≤ H` because `A` is abelian
   (`le_stabilizer`). The restriction of `proj r χ_V` to `H` is the projection, inside
   `H`, of `χ_{V|H}` (`proj_subgroupOf`). The character `χ_{V|H}` lies in the lattice of
   induced rank-one characters of `H`, by the Library's Brauer theorem
   (`BrauerLattice.characterLattice`).

   Apply Lemma C to each generator. Every nonzero term is `Ind_{A ⊔ S}^H μ` with `μ = r`
   on `A`, so `μ` is nontrivial on `A`. Transitivity of induction
   (`DegreeZeroBrauer.ind_ind`) turns it into the character of a generator of
   `abelianNormalBrauerSpan G A` (`ind_proj_mem`, `ind_generator_mem`). The orbit of the
   trivial character contributes `0` by (c) (`ind_stabilizer_mem`).

   Hence `χ_V` lies in `charSpan A`, the image of the span under `virtualCharacter`.
   Faithfulness then gives the statement.

## Provenance

The statement is DH81 Proposition 2.2(ii) (cited above). The helper definitions
(`proj`, `isoOp`, `conjChar`/`charAction`, `pairing`, `supFun`/`supChar`, `charSpan`,
`toAddChar`/`ofAddChar`/`charEquiv`/`charFintype`) are internal devices of this proof.
They are not taken from the source. The module imports published Library results by Lean
name: induction and its character formula (`DegreeZeroBrauer.ind`, `ind_apply`,
`ind_character`, `ind_ind`), the Brauer character lattice, and character faithfulness.
