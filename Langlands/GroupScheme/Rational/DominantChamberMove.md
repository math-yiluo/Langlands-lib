# Moving a cocharacter into the closed dominant chamber

This is derived infrastructure for `StandardParabolicClassificationStatement`.
It supplies the conjugation input of that classification ("every dynamic
parabolic is rationally conjugate to one containing `P(ν)`") for cocharacters
of a fixed maximal split torus `i`. The route goes through the relative Weyl
group and does not use `MinimalParabolicConjugacyStatement`. Let `ν` be a
generic cocharacter. For every cocharacter `ξ` of the torus, some normalizing
rational point `n` moves `ξ` into the closed dominant chamber of `ν`, and then
`P(groupHom ν ≫ i) ≤ P((groupHom ξ ≫ i) ≫ Int(n))`.

The unit is conditional. In its first part it assumes that the actual relative
roots realize the published root system (`HasRelativeRootSystem i`) and that the
torus is split. The parabolic consequence also assumes one direction of the
root-sign criterion for dynamic parabolics. The statement-level theorem takes
the published, still unproved statements `RelativeRootSystemStatement.{u}` and
`RelativeRootSignInclusionsStatement.{u}` as explicit premises. The unit proves
no published `…Statement`.

Moving an arbitrary cocharacter `ζ` of `G` to a cocharacter of `i` is the
separate unit `Rational/ParabolicCocharacterConjugacy`; this unit does not
import it.

## Setting and premises

The field `k : Type u` is arbitrary. In the section `Chamber`, `G` is a group
scheme over `Spec k`, `T` is any commutative group scheme and
`i : T.toGrp ⟶ G` is any homomorphism. Each declaration assumes only the
instances it uses:

- the first three lemmas assume `[Mono i.hom.hom.left]`;
- `positiveRootSum`, `positiveRootSum_eq_sum` and `corootFunctional_mk` assume
  `[IsAffineHom G.X.hom]`;
- the remaining declarations of the section assume both.

No smoothness, reductivity or maximality is assumed in that section. The
cocharacter action of a normalizing point `n` is
`cocharacterAut (normalizingAut i n)`, that is, postcomposition with the torus
automorphism through which `n` normalizes `i`. Its character action is the
published `weylAction i n`.

In the last theorem, `G` satisfies `IsConnectedReductive G`, `i` is a maximal
split torus (`IsMaximalSplitTorus i`), and `IsAffineHom G.X.hom` is
`hG.isAffineHom`, as in `StandardParabolicClassificationStatement`.

All inclusions of subgroup functors hold on every test scheme.

## Declarations

- `normalizingAut_mul`: the torus automorphism of `n * m` is
  `normalizingAut i m ≪≫ normalizingAut i n`. This follows from uniqueness of
  the normalizing automorphism (`IsNormalizingPoint.unique`).
  `cocharacterAut_normalizingAut_mul` gives the corresponding composite action
  on cocharacters.
- `latticePairing_cocharacterAut_normalizingAut`: the action on cocharacters is
  contragredient to the Weyl action on characters:
  `⟨χ, n • ζ⟩ = ⟨weylAction i n⁻¹ χ, ζ⟩`. This comes from the published
  `latticePairing_characterAut_cocharacterAut`.
- `positiveRootSum i ν` (definition): the finitary sum
  `∑ᶠ α ∈ positiveRelativeRoots i ν, α` of the positive relative roots, the
  classical `2ρ`. When the set of positive roots is finite,
  `positiveRootSum_eq_sum` rewrites it as a `Finset` sum.
- `corootFunctional_mk`: the published `corootFunctional i ζ`, evaluated on the
  rationalization of a character `χ` in the root span, is `⟨χ, ζ⟩`.
- `latticePairing_weylAction_of_reflection`: suppose `m` represents a class
  acting on `relativeRootSpan i` by the reflection `Module.reflection hc` in
  `1 ⊗ α`, with linear form `c` and `c(1 ⊗ α) = 2`. Then for every character
  `χ` whose rationalization lies in the span, and every cocharacter `ζ`,
  `⟨weylAction i m χ, ζ⟩ = ⟨χ, ζ⟩ - c(1 ⊗ χ) · ⟨α, ζ⟩` in `ℚ`.
- `HasRelativeRootSystem.exists_normalizerPoint_dominant` (premises
  `HasRelativeRootSystem i` and `IsSplitTorus T.toGrp`): for all cocharacters
  `ν` and `ξ`, there is a normalizing point `n` such that
  `0 ≤ latticePairing T α (cocharacterAut (normalizingAut i n) ξ)` for every
  `α ∈ positiveRelativeRoots i ν`. Genericity of `ν` is not needed here.
- `HasRelativeRootSystem.exists_normalizerPoint_parabolic_le` (the same
  premises, `IsGenericCocharacter i ν`, and the "if" direction `hsign` of the
  root-sign criterion with source `ν`): for every `ξ` there is a normalizing
  point `n` with
  `P(groupHom ν ≫ i) ≤ P((groupHom ξ ≫ i) ≫ (G.innerIso n).hom)`.
- `exists_normalizerPoint_parabolic_le_of_statements`: the same conclusion for
  every connected reductive `G`, maximal split torus `i` and generic `ν`, from
  `RelativeRootSystemStatement.{u}` and
  `RelativeRootSignInclusionsStatement.{u}`. It uses only the parabolic
  component of the second statement. The split torus and the monomorphism
  instance come from `hi.isSplitSubtorus`.

## Proof of the chamber move

Let `A` be the finite set of positive roots of `ν`. It is finite by
`HasRelativeRootSystem.finite_positiveRelativeRoots`. Let `ρ = positiveRootSum i ν`
be its sum, and let `F n = ⟨ρ, n • ξ⟩ ∈ ℤ`.

1. *The values of `F` form a finite set.* By contragredience,
   `F n = ∑_{β ∈ A} ⟨weylAction i n⁻¹ β, ξ⟩`, and `weylAction i n⁻¹` maps
   relative roots to relative roots. So every value of `F` has the form
   `∑_{β ∈ A} ⟨g β, ξ⟩` for a function `g : A → relativeRoots i`. These
   functions form a finite type, because the roots are finite
   (`HasRelativeRootSystem.finite_relativeRoots`). Hence there is `n₀`
   maximizing `F`.
2. *Suppose `n₀ • ξ` pairs negatively with some positive root `α`.* The
   published `HasRelativeRootSystem.exists_isRelativeReflection` gives a class
   acting on the root span by a reflection `Module.reflection hc` in `1 ⊗ α`.
   Choose a representative `m`.
3. *The coefficient `c(1 ⊗ ρ)` is positive.* Applying the reflection formula to
   `α` itself gives `⟨m α, ν⟩ = -⟨α, ν⟩ < 0`. Since `weylAction i m` is
   injective, `∑_{β ∈ A} ⟨m β, ν⟩` is the sum of `⟨γ, ν⟩` over the image
   `B = m(A)`. Split `B` into its part inside `A` and its part outside `A`.
   - The part inside `A` contributes at most `∑_{β ∈ A} ⟨β, ν⟩`, since every
     term over `A` is positive.
   - Every root outside `A` pairs nonpositively with `ν`, and `m α` lies
     outside `A` with a negative pairing. So the part outside `A` contributes
     a negative amount.

   Hence `⟨m ρ, ν⟩ < ⟨ρ, ν⟩`. By the reflection formula,
   `⟨m ρ, ν⟩ = ⟨ρ, ν⟩ - c(1 ⊗ ρ) ⟨α, ν⟩`. Since `⟨α, ν⟩ > 0`, it follows that
   `c(1 ⊗ ρ) > 0`.
4. *Contradiction.* Write `η = n₀ • ξ`. By `cocharacterAut_normalizingAut_mul`
   and contragredience, `F(m⁻¹ * n₀) = ⟨m ρ, η⟩`. By the reflection formula
   this equals `F n₀ - c(1 ⊗ ρ) ⟨α, η⟩`, which is greater than `F n₀` because
   `⟨α, η⟩ < 0`. This contradicts the maximality of `F n₀`.

For the parabolic consequence, let `n` be as in the chamber move. The
published `groupHom_cocharacterAut_comp` identifies
`groupHom (n • ξ) ≫ i` with `(groupHom ξ ≫ i) ≫ (G.innerIso n).hom`. A
relative root `α` with `0 ≤ ⟨α, ν⟩` has `⟨α, ν⟩ > 0`, because `ν` is generic,
so `α` is positive and `0 ≤ ⟨α, n • ξ⟩`. The "if" direction of the root-sign
criterion then gives the inclusion.

## Provenance

The unit is derived. Milne, *Algebraic Groups* (2017), 25.22 (printed p. 550,
PDF p. 566), states the corresponding classical facts for a maximal split torus
`S`: any two minimal parabolic subgroups are `G(k)`-conjugate; the minimal
parabolics containing `S` are indexed by the Weyl chambers of the relative root
system; and the relative Weyl group permutes them simply transitively. Appendix
C.22 (printed p. 612, PDF p. 628) records that the Weyl group of a root system
acts simply transitively on its Weyl chambers. Milne states C.22 for reduced
root systems, the convention of C.18. The Lean argument below needs neither
reducedness nor genericity of `ν`.

The Lean statement is the closed-chamber consequence used for parabolics:
every cocharacter is moved into the closure of the chamber of `ν`. The proof is
the classical argument that maximizes the pairing with the sum of the positive
roots. That argument is internal here. It uses only the published existence of
a reflection for each root, root finiteness, and the integral pairing. It does
not use simple roots, chamber topology, or the simple transitivity of the
action.

Milne's official errata contain no correction to 25.22 or to C.22, and they
have no entry for Appendix C at all. The errata used are the registered snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` of
https://jmilne.org/math/Books/iag2errata.html, accessed 2026-11-02. Two nearby
entries do not affect these citations:

- The entry "p.545 et seq." corrects 25.6(b), the final sentence of 25.24
  (also on p. 550) and 25.27: there the parabolic subgroup should be minimal.
- The entry for p. 549 says that the classical proofs that the relative root
  system of 25.16 is a root system are incomplete, and points to CGP, C.2.15.
  That fact is the premise `RelativeRootSystemStatement` here, not something
  this unit proves.
