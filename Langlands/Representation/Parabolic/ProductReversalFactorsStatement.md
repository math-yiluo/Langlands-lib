# Composition-factor commutativity of two-factor normalized products

Author: Worker 757.

This pair defines one proposition,
`Langlands.Parabolic.TwoBlockProductReversalFactors.{uF, uV}`. It states
Zelevinsky (1980), Theorem 1.9, for two smooth factors of finite length. The
declaration is a `Prop`-valued `def`. This contribution does not prove it: the
theorem is unproved here, and its proof is a separate task.

## Exact statement

For every prime natural number `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p` and every compatible realization
`T : F.TopologicalData`, install the topology `T.topology`. For all natural
numbers `a` and `b` with `ha : 0 < a` and `hb : 0 < b`, and all smooth complex
representations

- `π₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)` and
- `π₂ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)`,

the hypotheses are exactly `π₁.HasFiniteLength` and `π₂.HasFiniteLength`.
With `T.generalLinearTopologicalGroup (a + b)` installed, the statement sets

- `B := BlockShape.binary a b ha hb`, the two-block shape `(a, b)` of
  `GL_(a+b)`;
- `A : ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)`,
  defined by `fun i => Fin.cases π₁ (fun _ => π₂) i`, so block `0` is `π₁`
  and block `1` is `π₂`;
- `σ := B.adjacentSwap 0 Nat.one_lt_two`, the transposition of the two block
  labels. The proof term `Nat.one_lt_two` checks `0 + 1 < B.length`, since
  `B.length` is `2` by definition.

The conclusion is

```
HaveSameJordanHolderFactors
  (Rep.of (T.normalizedProductInduced B fun i => (A i).representation))
  (Rep.of (T.normalizedProductInduced (B.permute σ)
    fun i => (A (σ i)).representation))
```

The first argument is the actual product `π₁ × π₂`. The second is the actual
product `π₂ × π₁`; the next section explains its block order.

`SmoothRep.HasFiniteLength` is finite length of the carrier as a module over
the group algebra `ℂ[GL_m(F)]`. It is not finite dimension over `ℂ`. The
factors may be reducible, zero, isomorphic, or of equal rank. There is no
irreducibility, admissibility, genericity, unitarity, cuspidality or segment
premise, and no finite-length premise on the products.

Admissibility is not an explicit hypothesis, but omitting it does not enlarge
the scope: in the literature, every smooth complex representation of finite
length of these groups is admissible. Irreducible smooth representations are
admissible (BZ77 Theorem 2.5, printed p.447, recalled in Ze80 §1.5, printed
p.171), and for an exact sequence `0 → U → V → W → 0` and a compact open
subgroup `K` the sequence `0 → U^K → V^K → W^K` is exact, so admissibility
passes to finite extensions. This fact is not proved or used here.

Positivity of `a` and `b` is required by `BlockShape.binary`, whose blocks
have positive sizes. Ze80 also allows `G_0 = {e}`, which this statement
excludes. A finite-length representation of `G_0` is a space `ℂ^d` with
trivial action. Only the one-dimensional trivial representation (`d = 1`) is
the unit of `ℛ` (Ze80 §1.7(c), printed p.173). For general `d`, both `ρ × π`
and `π × ρ` are the direct sum of `d` copies of `π`, so the rank-zero case is
elementary.

`HaveSameJordanHolderFactors` is the published predicate of
`Langlands.Representation.Filtration.ObjectDefinitions`. It asserts actual
finite composition series of both representations, of a common length, with a
permutation of factor indices and a `Representation.Equiv` between each pair of
matched simple quotients. So the conclusion includes finite length of both
products and preserves multiplicities. It is not an isomorphism of the
products, an identity in a Grothendieck group, or an equality of cuspidal
supports. No surrogate product and no factor matching is supplied as data.

## Products, normalization and block order

`T.normalizedProductInduced B σ`, from
`Langlands.Representation.Induction.BlockFactors`, is normalized parabolic
induction from the standard upper block-triangular parabolic of shape `B`. It
inflates the external tensor product of the block representations to that
parabolic, twists it by the positive square root of the Library's block modulus
(`T.parabolicHalfModulus B`, the `δ_P^(1/2)` normalization), and lets `GL_n`
act on the actual space of smooth covariant functions by right translation.
This is Ze80's product `ρ₁ × ρ₂ = i_(n),(k,l)(ρ₁ ⊗ ρ₂)` (§1.7, with §1.8 for
factors of any length), with Ze80's normalized functor `i` from BZ77 §2.3 and
its upper block-triangular parabolic (Ze80 §1.3). The Library construction
uses the explicit block modulus
`δ_P(m) = ∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i)` of `Group/GL/BlockModulus`
in place of the Haar module; the Markdown of
`Langlands.Representation.Induction.Parabolic` records their equality as a
separate obligation, and this statement does not assume it.

`BlockShape.permute` (`Langlands.Representation.CuspidalSupport.BlockPermutation`)
has the convention that block `i` of `B.permute e` is block `e i` of `B`, so
`(B.permute σ).size i = B.size (σ i)` by definition. `BlockShape.adjacentSwap`
(`Langlands.Group.GL.AdjacentMergeShape`) is `Equiv.swap 0 1` here. Hence:

| Product | Shape (block sizes) | Block 0 | Block 1 |
| --- | --- | --- | --- |
| first, `π₁ × π₂` | `B`: `(a, b)` | `A 0 = π₁` | `A 1 = π₂` |
| second, `π₂ × π₁` | `B.permute σ`: `(b, a)` | `A (σ 0) = π₂` | `A (σ 1) = π₁` |

Both products are representations of the same group `GL_(a+b)(F)`, because
`B.permute σ` is again a `BlockShape (a + b)`. No rank cast or transport along
`a + b = b + a` occurs. `BlockShape.binary b a hb ha` would live over `b + a`
and is not used. The entries of the table hold by `rfl`.

This is the shape convention of task 1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9,
which owns the irreducible two-factor case for any `B` with `B.length = 2`.
By the published `normalizedProductInductionFunctor_obj`, which holds by `rfl`,
the conclusion is definitionally
`HaveSameJordanHolderFactors (Rep.of ((T.normalizedProductInductionFunctor B).obj A).representation) (Rep.of ((T.normalizedProductInductionFunctor (B.permute σ)).obj fun i => A (σ i)).representation)`,
the functor form of that task, specialized to `B = BlockShape.binary a b ha hb`.

## Universes and quantifier form

The field universe `uF` and the carrier universe `uV` are independent. Both
factors use the same carrier universe `uV`. This is forced by the Library API:
`T.normalizedProductInduced` takes a family of carriers
`V : Fin B.length → Type uV` in a single universe, and the tensor product of
the blocks is formed over that family. With factor carriers in two independent
universes `uV` and `uW`, the published construction cannot form `π₁ × π₂` at
all; the carriers would first have to be lifted to a common universe, for
example by the published `SmoothRep.universeLift`
(`Langlands.Representation.Category.UniverseLift`), and this proposition at
the common universe then applies to the lifted factors. The published
`normalizedProductInducedUniverseLiftEquiv`
(`Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport`)
identifies products along such lifts when all factors already share a
universe. The irreducible case of task 1b2016bd and the published
`Langlands.Classification.IrreducibleProductFiniteLength` also use one factor
universe. Both product carriers lie in `Type (max uF uV)`.

The proposition is closed over `p`, `F` and `T`, as are the neighbouring
`Langlands.Parabolic.NormalizedInductionFactorMatchingTheorem` and
`Langlands.Parabolic.InverseTransposeProductStatement`. A proof gives the
result for every prime, every `p`-adic field and every compatible topological
realization at once.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups. II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
165–210. Registered source ID `zelevinsky-1980-induced-ii`; PDF SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, verified
by Worker 757 on 2026-10-28. Worker 757 read printed pp.169–174 (zero-based PDF
pages 5–10; Theorem 1.9 is on zero-based page 10). There is no errata note for
this source in the Library notes.

- §1.1 (printed p.170): `G_n = GL(n, F)`, the standard block subgroups, and the
  normalized functors `i_(α,β)` of BZ77 §2.3; Proposition 1.1(a) (exactness),
  (c) (transitivity) and (d) (`i` commutes with contragredients).
- §1.5 (printed p.171): irreducible representations are admissible, citing
  BZ77 2.5.
- §1.7 (printed pp.172–173): `ℛ(G_n)` is the Grothendieck group of finite-length
  representations, `ℛ = ⊕ ℛ(G_n)`, and the multiplication
  `m(ρ₁ ⊗ ρ₂) = i_(n),(k,l)(ρ₁ ⊗ ρ₂)` written `ρ₁ × ρ₂`. By §1.7(c)
  (printed p.173), the unit `1 ∈ ℛ(G_0)` is the trivial representation of
  `G_0 = {e}`.
- §1.8 (printed p.174): the notation `ρ₁ × ⋯ × ρ_r` is also used for factors
  that need not have finite length.
- Theorem 1.9 (printed p.174): "The ring ℛ is commutative. In other words if
  `π₁ ∈ Alg G_k`, `π₂ ∈ Alg G_l` are of finite length then `π₁ × π₂` and
  `π₂ × π₁` have the same composition factors [i.e.
  `JH⁰(π₁ × π₂) = JH⁰(π₂ × π₁)`]."

`JH⁰(π)` is the multiset of composition factors of a finite-length `π` (Ze80,
notation for multisets, printed p.169), so it counts multiplicities, as
`HaveSameJordanHolderFactors` does. This statement is the second,
representation-level form of the theorem ("in other words"), with `k = a` and
`l = b`. It uses no Grothendieck ring.

The proof of Theorem 1.9 uses the matrix `s_n` with entries
`(s_n)_ij = (−1)^i δ_(i, n+1−j)` and the automorphism `s(g) = s_n ᵗg⁻¹ s_n⁻¹`
of `G_n`. Its Lemma (a) is `s(π₁ × π₂) ≅ s(π₂) × s(π₁)` for all
`π₁ ∈ Alg G_k`, `π₂ ∈ Alg G_l`. Its Lemma (b) says that for `π` of finite
length, `s(π)` has finite length and `JH⁰(s(π)) = JH⁰(π̃)`, where `π̃` is the
contragredient. Lemma (b) is reduced to irreducible `π`, where it is the
theorem of Gelfand and Kazhdan (Ze80 references [8] and [2], 7.3). The
theorem then follows from the chain
`JH⁰(π₁ × π₂) = JH⁰(s(π₁ × π₂)~) = JH⁰((s(π₂) × s(π₁))~) = JH⁰(s(π₂)~ × s(π₁)~) = JH⁰(π₂ × π₁)`,
which uses (b), (a), 1.1(d) and (b) again.

BZ77 is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Registered
source ID `bernstein-zelevinsky-1977-induced-i`; PDF SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, verified by
Worker 757 on 2026-10-28. It is cited for normalized induction (§2.3) and for
Theorem 2.5 (printed p.447, zero-based PDF page 7): every irreducible
representation embeds in a representation induced from a cuspidal one, "in
particular, ω is admissible".

## Planned proof (not part of this contribution)

The exact proof successor proves exactly this proposition. The irreducible
two-factor case is owned by task 1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9
(statement `Langlands.Classification.TwoFactorProductConstituentCommutativity`).
The planned route derives the finite-length case from the published proof of
that statement and does not repeat the Gelfand–Kazhdan route:

1. Take composition series of `π₁` and `π₂`. Using exactness of normalized
   induction, tensor factor matching and the published
   `Langlands.Parabolic.NormalizedInductionFactorMatchingTheorem`, show that
   `π₁ × π₂` has the same Jordan–Hölder factors as the direct sum of the
   products `σ × τ` over the factors `σ` of `π₁` and `τ` of `π₂`, with
   multiplicity. Do the same for `π₂ × π₁` and the products `τ × σ`.
2. Match summands by the irreducible case. Finite length of the products of
   irreducible factors is the statement
   `Langlands.Classification.IrreducibleProductFiniteLength`, whose proof is
   task 0717fd42-d711-4f42-8269-f6ae4c8da1e9.
3. Combine with additivity and transitivity of `HaveSameJordanHolderFactors`
   (`Filtration/JordanHolderComparisonProof`, `Filtration/LengthTwoMatching`).

Only if task 1b2016bd is withdrawn or abandoned, or its current revision stops
owning the analytic irreducible case, does the successor follow Ze80's
involution route itself. That route uses
`Langlands.Parabolic.InverseTransposeProductStatement` (proof task
fc1a5e69-5e8e-4fcd-ad69-c3d3d1384e91) for Lemma (a) and
`GelfandKazhdanContragredientStatement` (proof task
2206daa6-e219-4ed6-9ad1-4f4d47efed93) for Lemma (b).

## Independence

This is the general finite-length form of Theorem 1.9 and a lower input for
segment and classification work. Its proof must not use any segment,
multisegment or classification conclusion. The excluded results include
`SegmentSocleProductIrreducibility`, `SegmentHeadProductIrreducibility`,
`OrderedMultisegmentSocleExistence`, `SquareIntegrableLanglandsClassification`
and `GenericSegmentProductUniqueness`, together with their tasks, proof
successors and transitive proof dependencies. The full list of excluded tasks is
in task bd34fb90-1c0d-4f74-aed4-ef6af4d9e5af and is carried to the proof
successor unweakened.
