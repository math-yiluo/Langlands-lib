# Statement: closed subgroups of diagonalizable groups are diagonalizable

`Langlands.GroupScheme.Diagonalizable.ClosedSubgroupPresentationStatement.{u}`
says that every closed subgroup of a finitely generated diagonalizable group
over a field has a diagonalizable presentation. The declaration is a
Prop-valued definition. It is a statement, not a proof.

## The assertion

Fix an arbitrary universe `u` and quantify over:

- every field `k : Type u`;
- every `Λ : Type u` with `AddCommGroup Λ` and `AddGroup.FG Λ`;
- every group scheme `H : GroupScheme (Spec (CommRingCat.of k))`;
- every homomorphism
  `i : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`.

The only hypothesis is `IsClosedSubgroup i`, which says the underlying
morphism of schemes of `i` is a closed immersion. The conclusion is that
there exist `Λ' : Type u`, an `AddCommGroup Λ'` structure, a proof of
`AddGroup.FG Λ'`, and an element of

```text
Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp).
```

The isomorphism lives in `GroupScheme (Spec (CommRingCat.of k))`, which is
`Grp (Over (Spec (CommRingCat.of k)))`. It is therefore an isomorphism of
group schemes over `k`, not just of schemes. The existential carries the
character type, its group structure and its finite-generation proof.

`Diagonalizable.groupScheme R Λ` is the existing group scheme `D(Λ)`. It
is the spectrum of the group algebra `AddMonoidAlgebra R Λ`, and its points
over a test scheme `T` are the homomorphisms `Λ → Γ(T, 𝒪_T)ˣ`.
`IsClosedSubgroup` is the existing definition in
`Langlands.GroupScheme.Reductive.Basic`. This statement adds no new
definitions.

## Source and translation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field*, corrected reprint (2022), registered as
`milne-2022-algebraic-groups`. The relevant results are Definition 12.7 and
Theorems 12.8 and 12.9(a),(c), printed pp.233–234 (zero-based PDF
indices 243–244). The official 2022 errata change only Example 12.10 on
p.234, which this statement does not use. The 2017 errata entries for
Chapter 12 concern other results.

- Definition 12.7: an algebraic group `G` is diagonalizable when the
  group-like elements of `O(G)` span it.
- Theorem 12.8: `G` is diagonalizable if and only if `G ≅ D(M)` for some
  commutative group `M`.
- Theorem 12.9(a): `M ↦ D(M)` is a contravariant equivalence from finitely
  generated commutative groups to diagonalizable algebraic groups, with
  quasi-inverse `G ↦ X(G)`.
- Theorem 12.9(c): algebraic subgroups of diagonalizable algebraic groups
  are diagonalizable. The proof notes that `O(G) → O(H)` is a surjective
  Hopf-algebra map, which sends the spanning group-like elements of `O(G)`
  to group-like elements spanning `O(H)`.

The translation works as follows.

- **Algebraic subgroup.** In Milne (Definition 1.3), an algebraic subgroup
  of `G` is an algebraic group that is a `k`-subscheme of `G` and whose
  inclusion is a homomorphism. By Proposition 1.41 it is a closed
  subscheme. Here such a subgroup is a pair `(H, i)` with
  `IsClosedSubgroup i`.
- **Group algebra.** Milne writes the character group `M` multiplicatively
  and describes `D(M)` as represented by `k[M]` (Remark 12.6 gives the
  additive notation). The Library's `D(Λ)` uses an additive `Λ` and the
  group algebra `AddMonoidAlgebra k Λ`.
- **Assembling the conclusion.** The ambient group `D(Λ)` is diagonalizable
  by Definition 12.7. Theorem 12.9(c) makes `H` diagonalizable. Theorem 12.8
  then gives a commutative group `Λ'` with `H ≅ D(Λ')`.
- **Finite generation.** Theorem 12.9(a) places diagonalizable algebraic
  groups in correspondence with finitely generated commutative groups, so
  `Λ'` can be taken finitely generated. The proof of 12.9(c) gives a direct
  explanation. The group-like elements of `O(H)` are the images of `Λ`:
  distinct group-like elements are linearly independent (Milne,
  Proposition 4.23, which the proof of Theorem 12.8 cites as Lemma 4.23),
  so every group-like element in their span is one of them. Hence `Λ'` is a
  quotient of `Λ`. This also shows that `Λ'` can be chosen in the same
  universe `u` as `Λ`.

## Scope

The statement keeps the full source generality.

- **No premises on the subgroup.** It assumes no smoothness, connectedness
  or reducedness of `H`, no algebraic closure of `k`, and no prior
  diagonalizable presentation of `H`.
- **Finite nonreduced subgroups.** These are included, for example
  `μ_p = D(ℤ/pℤ)` inside `𝔾_m = D(ℤ)` in characteristic `p`.
- **Torsion.** `Λ'` may have torsion, including `p`-torsion.
- **No affineness or finite-type premise.** None is placed on `H`. Because
  `Λ` is finitely generated, `D(Λ)` is affine and of finite type over `k`,
  and the closed immersion `i` passes both properties to `H`. So `H` is an
  algebraic group in Milne's sense.

The statement asserts only that a presentation exists. It does not say how
the isomorphism interacts with `i`. In particular, it does not claim that
the composite `D(Λ') ≅ H ⟶ D(Λ)` comes from a surjection `Λ → Λ'`. It also
claims no uniqueness of `Λ'`, and it does not use Theorem 12.9(b) or the
quotient part of 12.9(c).

## Provenance

This is a direct formal statement of Milne's results. Combining
Theorems 12.8 and 12.9(a),(c) into one existential presentation, with the
character group finitely generated and in the same universe, is the only
packaging choice. It is made so that the closed fppf image of a
homomorphism into a split torus can be presented as `D(Λ')` for a finitely
generated `Λ'`, which is the form the diagonalizable extension-splitting
statements consume.
