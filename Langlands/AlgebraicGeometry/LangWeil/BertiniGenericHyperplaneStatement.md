# Bertini's irreducibility theorem for the generic hyperplane section

Author: Worker 69.

This module states Bertini's irreducibility theorem for the generic hyperplane section of an
affine scheme of finite type over a field. It is the geometric input of the induction step
(hyperplane slicing) in the Library's Lang–Weil route to Conrad's Lemma 4.6. The module
contains no proof.

## The statement

`BertiniGenericHyperplaneStatement` says: let `k` be a field, `A` a commutative `k`-algebra
(both types in a universe `u`), `n : ℕ` and `g : Fin n → A`. Assume

- `g₀, …, g_{n−1}` generate `A` as a `k`-algebra (`Algebra.adjoin k (Set.range g) = ⊤`), so
  `X = Spec A` is of finite type over `k` and `g` embeds it in affine `n`-space;
- `X` is geometrically irreducible over `k`: Mathlib's `GeometricallyIrreducible` holds for the
  morphism `Spec A ⟶ Spec k` induced by `algebraMap k A`;
- `2 ≤ ringKrullDim A`.

Let `L` be the fraction field of the polynomial ring `k[a_*, a_0, …, a_{n−1}]`
(`FractionRing (MvPolynomial (Option (Fin n)) k)`, the variable `a_*` indexed by `none` and `aᵢ`
by `some i`), and let

`h = a_* ⊗ 1 + ∑ᵢ aᵢ ⊗ gᵢ ∈ L ⊗[k] A`.

Then the morphism `Spec ((L ⊗[k] A) ⧸ (h)) ⟶ Spec L` induced by the `L`-algebra structure of
the quotient is geometrically irreducible. In words: the section of `X_L` by the generic affine
hyperplane `a_* + ∑ᵢ aᵢ xᵢ = 0` of affine `n`-space is geometrically irreducible over `L`.

## Relation to the sources

Stacks Project, Section 37.32 "Bertini theorems" (Tag 0G4C), Lemma 37.32.3 (Tag 0G4F), after
Jouanolou, *Théorèmes de Bertini et applications*, Théorème 6.3 4) (registered source
`stacks-bertini-theorems-0g4c-0fd4-2026-11-09`, HTML snapshots of Tags 0G4C and 0FD4). In
Situation 33.47.2 (Tag 0G47) one has a scheme `X` over `k`, an invertible module `𝓛`, a
`k`-vector space `V` with basis `v_1, …, v_r` and a linear map `ψ : V → Γ(X, 𝓛)`; the universal
divisor `H_univ ⊂ 𝐀^r_k ×_k X` is the zero scheme of `∑ xᵢ ψ(vᵢ)`, and its fibre over a
`k'`-point `v` is the zero scheme `H_v` of `ψ(v)`. A property holds "for general `v`" if it holds
for every `k'`-point of some nonempty open `U ⊂ 𝐀^r_k`, for all field extensions `k'/k`.
Lemma 37.32.3 assumes (1) `X` of finite type over `k`, (2) `X` geometrically irreducible,
(3) there are `v_1, v_2, v_3 ∈ V` and an irreducible component `Z` of `H_{v_2} ∩ H_{v_3}` with
`Z ⊄ H_{v_1}` and `codim(Z, X) = 2`, and (4) every irreducible component of `⋂_v H_v` has
codimension at least `2`. It concludes that for general `v ∈ V ⊗_k k'` the scheme `H_v` is
geometrically irreducible over `k'`. Its proof shows that the generic fibre of
`H_univ → 𝐀^r_k` is geometrically irreducible and then applies Lemma 37.27.5 (Tag 0559).

Provenance: derived. The statement is the generic-fibre form of Lemma 37.32.3 in the case
`X = Spec A`, `𝓛 = 𝒪_X`, `V = k^{n+1}` with `ψ(e_*) = 1` and `ψ(eᵢ) = gᵢ`:

- the universal divisor is `Spec (A[a_*, a_0, …, a_{n−1}] ⧸ (a_* + ∑ aᵢ gᵢ))` over
  `𝐀^{n+1}_k = Spec k[a_*, a_0, …]`, and its fibre over the generic point of `𝐀^{n+1}_k`, whose
  residue field is `L`, is `Spec ((L ⊗[k] A) ⧸ (h))`;
- the generic point is an `L`-point of every nonempty open of `𝐀^{n+1}_k`, so the conclusion of
  Lemma 37.32.3 applied to it gives the statement;
- condition (4) holds because `ψ(e_*) = 1` has empty zero scheme;
- conditions (1) and (2) are the first two hypotheses; condition (3) is where
  `2 ≤ ringKrullDim A` enters. Over an infinite field, a general element `v_2` of `V` has a
  nonempty zero scheme of pure codimension `1`, and a general `v_3` vanishes identically on no
  component of it, which gives `Z`; take `v_1 = e_*`. A finite field `k` is reduced to the field
  `k(t)` as in the last paragraph of the proof of Lemma 37.32.1 (Tag 0G4D): geometric
  irreducibility after the base change `L ⊆ L(t)` implies it over `L`.

The statement concerns irreducibility only. Smoothness or reducedness of hyperplane sections
(Stacks, Lemma 33.47.3) is not claimed, and neither is the dimension of the section.

## Use in the Library's route

In `FamilyLangWeilSlicingStatement`, a family of `(d + 2)`-dimensional fibres is sliced by the
universal hyperplane. This statement, applied over the generic point of the base, together with
the Library's generic spreading of geometric irreducibility (Stacks 0559,
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.finiteTypeGeometricallyIrreducibleGenericSpreading`),
shows that the slices are geometrically irreducible outside a proper closed subset of the
parameter space.

## Status

Open. A proof is to be supplied through its own focused proof task, for example by formalizing
Stacks Lemmas 37.32.1–37.32.3.
