# One geometric expansion for a finite sum of functions

Module `Langlands.TraceFormula.SimpleTraceGeometricExpansionSum`, namespace
`Langlands.TraceFormula`.

The simple trace formula gives, for one test function, a finite family of rational representatives
and an expansion of the trace into terms `vol((Γ ∩ C) \ C) · O_γ(φ)`. The family is not specified,
so the expansions of two functions come with two unrelated families. This module merges the
expansions of finitely many functions into one expansion of their sum, in a general topological
group, using the transport of the orbital terms along conjugation
(`TwistedOrbitalTermInvariance`).

## Setting

`G` is a topological group with its Borel σ-algebra, `Γ` a subgroup, `μG` a left-invariant measure
on `G`, and `P : G → Prop` a property of representatives (for `GL_n`, regular ellipticity at a
finite place). The measure block is the Library's
`SimpleTraceGeometricExpansion Γ (MonoidHom.id G) μG φ t r` (`SingleOrbitSimpleTrace`): for all
measurable structures with `BorelSpace` on the coset spaces, all right-invariant `μC j` finite on
compacts and positive on open sets, and all compatible `νC j`, `νD j`, the volumes are finite, the
orbit functions of `φ` are integrable, and `t = ∑ j, vol_j · O_{r j}(φ)`.

## Statements

- `IsTwistedConjugate.refl Γ θ x : IsTwistedConjugate Γ θ x x`.
- `twistedOrbitFunction_finsetSum θ γ s φ`: the orbit function of `fun x => ∑ k ∈ s, φ k x` is
  `fun q => ∑ k ∈ s, twistedOrbitFunction θ γ (φ k) q`.
- `twistedOrbitFunction_eq_zero θ γ h : twistedOrbitFunction θ γ φ = 0` when
  `h : ∀ x, φ (x⁻¹ * γ * θ x) = 0`.
- `exists_classRepresentatives s`: for an equivalence relation `s` on a finite type `ι`,

  `∃ (m : ℕ) (rep : Fin m → ι) (c : ι → Fin m), (∀ i, s (rep (c i)) i) ∧ (∀ j, c (rep j) = j) ∧
    ∀ i i', s i i' → c i = c i'`.

- `exists_simpleTraceGeometricExpansion_sum Γ μG P φ t h`: for `φ : Fin N → G → ℂ`, `t : Fin N → ℂ`
  and

  ```
  h : ∀ k, ∃ (m : ℕ) (r : Fin m → Γ),
    (∀ j l, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) (r l : G) → j = l) ∧
    (∀ j, P (r j : G)) ∧
    (∀ q ∈ Γ, (∃ x : G, φ k (x⁻¹ * q * x) ≠ 0) →
      ∃ j, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) q) ∧
    SimpleTraceGeometricExpansion Γ (MonoidHom.id G) μG (φ k) (t k) r
  ```

  the same holds for `fun x => ∑ k, φ k x` and `∑ k, t k`:

  ```
  ∃ (m : ℕ) (r : Fin m → Γ),
    (∀ j l, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) (r l : G) → j = l) ∧
    (∀ j, P (r j : G)) ∧
    (∀ q ∈ Γ, (∃ x : G, (∑ k, φ k (x⁻¹ * q * x)) ≠ 0) →
      ∃ j, IsTwistedConjugate Γ (MonoidHom.id G) (r j : G) q) ∧
    SimpleTraceGeometricExpansion Γ (MonoidHom.id G) μG (fun x => ∑ k, φ k x) (∑ k, t k) r
  ```

  No topological hypothesis beyond a topological group is needed, and no discreteness of `Γ`: the
  proof uses only the transport of admissible measures along conjugation, not their uniqueness.

## Proof

The representatives `r k j` of all pieces are indexed by `Σ k, Fin (m k)`, and conjugacy under `Γ`
is an equivalence relation on this finite type (`IsTwistedConjugate.refl`, `.symm`, `.trans`).
`exists_classRepresentatives` (a choice of `Quotient.out` in each class, numbered through
`Fintype.equivFin`) keeps one index `rep j'` in each class; the new family is `r' j' = r (rep j')`.
It is pairwise non-conjugate by construction, satisfies `P`, and covers: a nonzero value of the sum
is a nonzero value of some piece, whose own family has a representative in the class, and that
representative is conjugate to the kept one.

For the measures, let admissible triples at the kept representatives be given. For every piece `k`
and every `j`, the triple at the kept representative `r' (c ⟨k, j⟩)` of the class of `r k j` is
transported to `r k j` (`exists_isCompatible_of_isTwistedConjugate`, with the Borel structures),
with the same volume, the same integrability of the orbit functions and the same orbital
integrals. The expansion of piece `k` applied to these triples gives the finiteness of the volumes
and the integrability, and

`t k = ∑ j, vol_{c⟨k,j⟩} · O_{r'(c⟨k,j⟩)}(φ k) = ∑ j', vol_{j'} · O_{r' j'}(φ k)`,

since `j ↦ c ⟨k, j⟩` is injective (the family of piece `k` is pairwise non-conjugate) and the
orbit function of `φ k` vanishes at a kept representative whose class the family of piece `k` misses
(its covering clause). Exchanging the two finite sums and using that the orbital integral of a
finite sum of integrable orbit functions is the sum of the orbital integrals gives
`∑ k, t k = ∑ j', vol_{j'} · O_{r' j'}(∑ k, φ k)`.

## Declarations, in order

- `IsTwistedConjugate.refl`
- `twistedOrbitFunction_finsetSum`, `twistedOrbitFunction_eq_zero`
- `exists_classRepresentatives`
- `exists_simpleTraceGeometricExpansion_sum`

## Literature

Getz–Hahn, *An introduction to automorphic representations* (2024), §18.4, Corollary 18.4.1 (printed
p. 485): the geometric side of the simple trace formula is a sum over conjugacy classes, which
presupposes that each term depends only on the class; Arthur–Clozel, *Simple algebras, base change,
and the advanced theory of the trace formula* (1989), Chapter 1, §4, (4.4) and (4.5) (printed
pp. 43–44), with sums over (twisted) conjugacy classes. Neither source writes out the merging of
two expansions; it is the linearity of the geometric side in the test function, which the
indexing by classes makes evident there.
