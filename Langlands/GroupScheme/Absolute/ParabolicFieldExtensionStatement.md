# Parabolic subgroups under arbitrary field extension

`Langlands.GroupScheme.ParabolicFieldExtensionStatement` is a proposition
target. This module defines the proposition and supplies no proof of it.

For all fields `k K : Type u`, an instance `Algebra k K`, an actual group
scheme `G` over `Spec (CommRingCat.of k)` satisfying
`IsConnectedReductive G`, an actual group scheme `P` over the same base,
and a homomorphism `i : P ⟶ G`, it asserts that
`IsParabolicSubgroup i` implies `IsParabolicSubgroup i_K`. Here

```lean
i_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i
```

The displayed equality specifies notation in this documentation. This
functor is the actual scheme-pullback functor lifted to group objects.
Its map has source `P_K` and target `G_K`, with their induced group laws.
The assertion concerns that homomorphism, including its closed-immersion
and smoothness conditions. It is not an assertion about images of
rational points.

The extension is arbitrary: the declaration has no characteristic,
perfection, algebraicity, separability, degree or splitness assumption.
It does not require a proper subgroup or a positive-dimensional group.
In particular `P = G` and the trivial group are included.

## Original sources and errata

- J. S. Milne, *Algebraic Groups* (2017), registered source
  `milne-2017-algebraic-groups`: Definition 17.6, printed p.353
  (one-based PDF p.369), defines a Borel subgroup over an algebraically
  closed field as a maximal connected solvable subgroup variety.
  Definition 17.15 and Theorem 17.16, printed p.356 (PDF p.372), define
  parabolicity by completeness of the quotient and characterize it by
  containing a Borel subgroup. The Borel criterion is used after passing
  to an algebraically closed field.
- Milne §17.66, printed p.375 (PDF p.391), states that the geometric Borel
  notion is preserved and reflected by arbitrary field extension, and
  agrees with Definition 17.6 over an algebraically closed field. Together
  with Theorem 17.16, this gives the derived parabolic extension assertion
  stated here.
- Milne Propositions 6.20(b) and 6.21, printed p.130 (PDF p.146),
  Definition 6.26, printed p.131 (PDF p.147), and Proposition 6.30 and
  Corollary 6.31, printed p.132 (PDF p.148), relate derived subgroups to
  the abstract groups of geometric points and show invariance of
  algebraic solvability under field extension.
- B. Conrad, *Reductive group schemes* (2014), registered source
  `conrad-2014-reductive-group-schemes`: the discussion following
  Definition 3.1.1, printed/PDF p.81, records geometric connectedness of
  connected finite-type group schemes. This supplies the connectedness
  needed when applying the Borel criterion after extending the field.
- Milne's official errata, registered source
  `milne-2017-algebraic-groups-errata-2026-11-02`, retained HTML snapshot
  dated 2026-11-02, was consulted. Its list has no correction to the
  cited passages.

## Correspondence with the existing predicates

The declaration imports `Langlands.GroupScheme.Absolute.Borel` and retains
`IsParabolicSubgroup` unchanged. Its input consists of a closed immersion
`i`, smoothness of `P`, and a Borel factorization over
`k̄ = AlgebraicClosure k`: there are `j : B ⟶ G_k̄` and `f : B ⟶ P_k̄`
with `IsBorelSubgroup j` and `f ≫ i_k̄ = j`. Thus the geometric Borel
criterion is built into the existing predicate. No quotient construction
is introduced by this statement.

Over the algebraically closed field `k̄`, the existing
`IsBorelSubgroup` requires a smooth connected solvable closed subgroup
maximal among such subgroups. The ambient group is smooth affine of
finite type, and its closed subgroup candidates are affine of finite
type. Consequently this is the setting of Milne Definition 17.6. The
Library's maximality predicate over an arbitrary, nonclosed field only
tests subgroups defined over that field; this documentation makes no
identification of that predicate with the geometric Borel notion over
such a field. The present parabolic predicate uses it over a chosen
algebraic closure.

`IsSolvableGroupScheme B` itself tests solvability of the abstract group
of points after base change to the chosen algebraic closure of the field
of definition of `B`. For a smooth affine group the derived-series
results in Milne 6.20–6.31 identify this with algebraic solvability.
When that field is already algebraically closed, its further algebraic
closure is isomorphic to it over the field. A proof using the cited
Borel result must account for this further closure and the induced
isomorphisms of groups of points; the statement does not assume this
comparison.

For the extension `k → K`, choose, as part of a proof, a compatible
`k`-embedding `k̄ → K̄`, where `K̄ = AlgebraicClosure K`.
Base-changing `j` and `f` along it preserves the factorization.
Milne §17.66, applied between these algebraically closed fields, preserves
the Borel property, including maximality. Pullback-composition
isomorphisms identify the resulting ambient and subgroup schemes with
the base changes of `G_K` and `P_K` to `K̄`. Transport along these
isomorphisms gives the factorization required by the conclusion.
Closed immersions and smoothness are preserved by base change. This
explains the derived assertion's correspondence to the existing
predicate; these transports and invariance results remain proof
obligations.

No closure comparison, geometric maximality, extension conclusion or
structural theorem is supplied as an extra premise. This module neither
states nor uses the dynamic description of parabolics by cocharacters.
