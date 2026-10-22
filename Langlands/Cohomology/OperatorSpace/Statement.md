# Cohomology of spaces with operators

Author: Worker 3.

This module defines eight propositions and their conjunction
`Langlands.Cohomology.OperatorSpaceCohomologyStatements`. They are the
statements of Grothendieck's Tohoku 1957, Chapter V, sections 5.1-5.2, that
compare the cohomology of equivariant sheaves with ordinary sheaf cohomology
and group cohomology. Three of them are compactly supported analogs, taken from
Berkovich's equivariant manuscript, Corollary 1.5.2(i). They are
theorem-statement definitions, not proofs. Injectivity, flasqueness and every
comparison isomorphism are conclusions; none is supplied as data or as a
hypothesis of another component.

## Objects

All components quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` acts on `X` by
`MulAction`, and each element acts continuously (`ContinuousConstSMul`), so
each acts by a homeomorphism. `G` carries no topology. This is Grothendieck's
setting of a group of operators on a space. The objects are the published
ones:

- `Langlands.Sheaf.Equivariant.TopologicalSheaf G X (ModuleCat R)` is the
  category of equivariant sheaves of `R`-modules: presheaves on the transport
  category of opens whose restriction to ordinary inclusions is a sheaf. Its
  abelian structure and enough injectives are the published instances of
  `Langlands.Sheaf.Equivariant.Abelian`.
- `toSheaf G X (ModuleCat R)` forgets the group transport, giving an ordinary
  module sheaf on `TopCat.of X`.
- `sectionRepresentation R G X` takes global sections with their `G`-action,
  as an object of Mathlib's `Rep R G`.
- `CompactSections.functor R G X` takes compactly supported global sections
  with their `G`-action, as an object of `Rep R G`.
- `TopologicalDerivedSections.ordinaryCohomology (TopCat.of X) R n` and
  `compactCohomology (TopCat.of X) R n` are Mathlib right derived functors of
  ordinary and compactly supported global sections on ordinary module sheaves.
  `ordinaryCohomologyZeroIso` and `compactCohomologyZeroIso` are their
  published degree-zero identifications.
- `Rep.invariantsFunctor R G`, `groupCohomology`, `groupCohomology.functor`
  and `groupCohomology.H0Iso` are Mathlib's invariants, group cohomology and
  its degree-zero identification with invariants.

Equivariant derived functors are Mathlib's `Functor.rightDerived` on the
equivariant sheaf category. The additivity instances for the two section
functors are published in `Langlands.Cohomology.EquivariantSections`.

Degree zero is fixed by Mathlib's `Functor.toRightDerivedZero`, the natural
map from a functor to its zeroth right derived functor. It needs no
left-exactness instance. The equivariant section functors have no published
finite-limit instance, so `rightDerivedZeroIsoSelf` is not available for them.
For the ordinary section functors, the inverse of the published zero
identification is by definition `toRightDerivedZero`.

## The eight propositions

| Declaration | Hypotheses and asserted conclusion |
| --- | --- |
| `EquivariantInjectiveSectionsStatement` | If `A` is injective in the equivariant sheaf category, then `sectionRepresentation R G X` sends it to an injective object of `Rep R G`. |
| `EquivariantInjectiveFlasqueStatement` | If `A` is injective in the equivariant sheaf category, then its underlying ordinary sheaf is flasque (Mathlib's `TopCat.Sheaf.IsFlasque`). |
| `EquivariantSectionsDerivedStatement` | There are natural isomorphisms `e n` between the composite of `(sectionRepresentation R G X).rightDerived n` with the forgetful functor to `ModuleCat R` and the composite of `toSheaf` with `ordinaryCohomology n`. In degree zero, `forget₂` of `toRightDerivedZero` followed by `e 0` is the inverse of the ordinary zero identification. |
| `EquivariantCompactSectionsDerivedStatement` | The same for `CompactSections.functor R G X` and `compactCohomology n`, with `compactCohomologyZeroIso` in degree zero. |
| `EquivariantAcyclicGroupCohomologyStatement` | For every `A` whose underlying sheaf has `ordinaryCohomology (q + 1)` zero for all `q`, there are isomorphisms from the `n`-th right derived functor of `sectionRepresentation ⋙ invariantsFunctor` at `A` to `groupCohomology` of the section representation of `A`. They are natural in maps `A ⟶ B` between such objects. In degree zero, `toRightDerivedZero` followed by the isomorphism is the inverse of `groupCohomology.H0Iso`. |
| `FiniteEquivariantSectionsInvariantsStatement` | For finite `G` with `IsUnit (Nat.card G : R)`, there are natural isomorphisms from `(sectionRepresentation ⋙ invariantsFunctor).rightDerived n` to `(sectionRepresentation).rightDerived n ⋙ invariantsFunctor`. In degree zero, `toRightDerivedZero` of the composite followed by `e 0` is the invariants of `toRightDerivedZero` of `sectionRepresentation`. |
| `FiniteEquivariantCompactSectionsInvariantsStatement` | The same for `CompactSections.functor R G X`. |
| `FiniteEquivariantCompactAcyclicGroupCohomologyStatement` | For finite `G`, the analog of `EquivariantAcyclicGroupCohomologyStatement` with compact supports: the hypothesis is vanishing of `compactCohomology (q + 1)` of the underlying sheaf, and the target is `groupCohomology` of the compactly supported section representation. No invertibility of the order is assumed. |

`OperatorSpaceCohomologyStatements` is the conjunction of the eight, in this
order.

Together with the third statement, the sixth identifies the derived functors
of invariant sections with the invariants of ordinary sheaf cohomology,
carrying the action given by derived functoriality. The fifth and eighth are
stated objectwise because the acyclicity hypothesis selects a class of objects,
not a subcategory with its own derived functors.

## Original-source correspondence

Grothendieck, *Sur quelques points d'algèbre homologique*, Tohoku Math. J. 9
(1957), Chapter V. Pages are printed pages; PDF pages are given in brackets.
Pages 198 and 202 were read visually; pages 195-201 were read in the text
layer.

| Location | Statement | Lean component |
| --- | --- | --- |
| §5.1, pp.195-196 [77-78] | `G` operates on `X`; `G`-sheaves, `G`-homomorphisms and the additive category of abelian `G`-sheaves. `G` need not act faithfully. | The published equivariant sheaf category. |
| Prop. 5.1.3, Corollary, p.198 [80] | If `A` is an injective abelian `G`-sheaf, then `Γ(A)` is an injective `G`-module. | `EquivariantInjectiveSectionsStatement` |
| pp.200-201 [82-83], before and after Thm. 5.2.1 | The derived functors of `Γ_X`, viewed as a functor to `G`-modules, are the `H^q(X, A)`, since every `G`-sheaf embeds in a flasque `G`-sheaf. They are universal cohomological functors reducing to `Γ` in degree 0. | `EquivariantSectionsDerivedStatement` |
| p.202 [84], first paragraph | An injective object of `C^X(G)` is a flasque sheaf. | `EquivariantInjectiveFlasqueStatement` |
| Thm. 5.2.1 and Prop. 5.2.4, pp.200, 202 [82, 84] | If `H^q(X; A) = 0` for `q > 0`, then `H^n(X; G, A) = H^n(G, Γ(A))`. Here `H^n(X; G, A)` is defined by (5.2.3) as `R^n Γ^G_X(A)`. | `EquivariantAcyclicGroupCohomologyStatement` |
| Prop. 5.2.3, Corollary, p.202 [84] | For `G` finite of order `m`, with multiplication by `m` an automorphism of `A`: `H^n(X, A)^G ≅ H^n(X; G, A)`. | `FiniteEquivariantSectionsInvariantsStatement`, with the third component |

Grothendieck works with abelian `G`-sheaves, that is, `R = ℤ`, and remarks on
p.202 (Remarque 1) that the derived functors are unchanged for `G`-modules
over a `G`-ring sheaf. The Lean components use modules over a constant
commutative ring with trivial `G`-action. This is a stated generalization. The
same arguments apply. For example, `sectionRepresentation` has an exact left
adjoint, the constant equivariant sheaf on a representation, so it preserves
injectives.

The finite-group component asserts only the second isomorphism of the
Corollary to Prop. 5.2.3. That isomorphism needs only the finiteness of `G`
and the invertibility of `m`: then `H^p(G, M) = 0` for `p > 0` on every
module where `m` acts invertibly. Hence the second spectral sequence of
Thm. 5.2.1, with initial term `H^p(G, H^q(X, A))`, degenerates. The Lean
hypothesis `IsUnit (Nat.card G : R)` makes `m` invertible on every
`R`-module. This specializes Grothendieck's hypothesis on `A` to a hypothesis
on the coefficient ring; his example of vector spaces over a field of
characteristic prime to `m` is of this kind. The separatedness of `X` and the
vanishing of the sheaves `H^q(G, A)` serve the first isomorphism, with
`H^n(Y, A^G)` on the orbit space `Y`. That isomorphism is not stated here,
since the orbit space and the sheaf of invariants are not published objects.
The spectral sequences of Thm. 5.2.1 themselves are not stated.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript, §1.5, PDF pp.11-12 (text layer):

- In §1.4, p.7, Berkovich first treats a discrete group `G`, for which an
  equivariant sheaf is a sheaf with compatible isomorphisms
  `τ(g) : F ≅ g^*F`. This is the case formalized here. Berkovich's spaces are
  analytic spaces with étale sites. The Lean components use an ordinary
  topological space and its sheaves of modules, as the published equivariant
  category does.
- Corollary 1.5.2(i) gives isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`.
  For a discrete group, the trivial subgroup is open. Then `Γ_{c,X{G}}` is
  compactly supported sections with their `G`-action, and the corollary says
  that its derived functors have the compactly supported cohomology of the
  underlying sheaf as underlying groups. This is
  `EquivariantCompactSectionsDerivedStatement`.
- Corollary 1.5.2(i) also prints a spectral sequence
  `H^p(G, H^q_c(X, b^*F)) ⇒ H^(p+q)_c(X(G), F)`. For a finite group it gives,
  when `H^q_c(X, F) = 0` for `q > 0`, the isomorphism of
  `FiniteEquivariantCompactAcyclicGroupCohomologyStatement`. The finiteness
  hypothesis is needed, and is not in the printed corollary. Let `G = ℤ` act
  by translation on the discrete space `X = ℤ`, and let `F` have stalk
  `M ≠ 0` at every point, permuted by `G`. Every invariant global section is
  constant along the orbit `X`, so it has compact support only if it is zero.
  Hence `Γ_{c,X(G)} = 0` and all `H^n_c(X(G), F)` vanish. But
  `H^0_c(X, F) = ⊕_{n ∈ ℤ} M` with the shift action, and
  `H^1(ℤ, ⊕_{n ∈ ℤ} M)` is the coinvariants, isomorphic to `M` by the sum
  map. Since `X` is discrete, `H^q_c(X, F) = 0` for `q > 0`, so the spectral
  sequence would force `H^1(ℤ, ⊕ M) = 0`. For a finite group, the
  compactly supported sections of an injective equivariant sheaf are a
  summand of a module induced from the trivial group, which has no higher
  cohomology. This is why the finite-group statement holds.
- `FiniteEquivariantCompactSectionsInvariantsStatement` is the compactly
  supported form of the Tohoku Corollary. It is a derived statement with the
  same proof: invariants are exact when the order is invertible.

The compactly supported components are needed for the cohomology of the
Harris and Berkovich analytic spaces, which carries group actions through
Berkovich's equivariant topos. The analytic étale setting itself is not
formalized here.

## Scope

No topology is placed on `G`, so smooth actions of locally profinite groups
and Berkovich's limit `X{G}` over open subgroups are not covered. No
statement concerns the orbit space `X/G`, the sheaves `H^q(G, A)` on it, or
the third spectral sequence of Tohoku (5.2.10). Exactness of `toSheaf` and its
preservation of injectives, which are stronger than the flasqueness component,
are not asserted. The components assert natural isomorphisms of derived
functors; compatibility with the connecting morphisms is not asserted.

## Registered sources

- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`,
  Tohoku 1957, SHA-256
  `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  Chapter V, §§5.1-5.2, pp.195-203 (PDF pp.77-85). Pages 198 and 202 were
  read visually; pages 195-201 were read in the text layer.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  Berkovich's equivariant manuscript, folder digest
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  §1.4, p.7, and §1.5 through Corollary 1.5.2, PDF pp.10-12, read in the text
  layer.

## Formal dependencies and checks

Project imports, all published by Worker 13 or Worker 61 and byte-identical
to Library commit `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`:

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.Sheaf.Equivariant.Abelian` | `5563a66fd43002b53d67a9ec67c4779421e2469b41ced6ab3d0db9130694dca2` | `ffed98c41011abb6cb078c9a98d08dbadf5ca1d99c36a52a475a65d4cc3906d4` |
| `Langlands.Cohomology.EquivariantSections` | `cae0603b98a431090323db9c16832b4ad881dd5c8cd0fa85519a814a4f90ade9` | `4589d4e9294bdfdcf64ffd90806fd875039ab5fe9c615c72b6b0d795998e03ea` |
| `Langlands.Cohomology.TopologicalDerivedSections` | `f2c3e8f0d296eb10d666bb649c121362cf184069db96aa3c27d4b50f21b243c9` | `b3e584b5f40b826f896f9bc0219a67f55c25073f45458b35eb92851ad5b1d7f8` |

The Mathlib imports provide flasque sheaves, `Rep.invariantsFunctor`, group
cohomology with its functoriality and `H0Iso`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Development check `0fa70f02-9348-4c6c-a742-737a6f90d45b` built this module
with no errors or warnings. Workspace check
`b1ae2d13-6a5b-44f3-b34a-ea6231828453` rebuilt the same Lean sources with
Lake and inspected the conjunction as a `Prop`-valued definition. Check `ce815ce5-0084-490d-830d-7f2596b4ec7e`
printed all eight components and the conjunction with universe annotations,
and the output was read. Every definition has the single universe parameter
`u`, and the conjunction depends only on `propext`, `Classical.choice` and
`Quot.sound`. The prints show:

- the injectivity and flasqueness statements use Mathlib's `Injective` in the
  equivariant sheaf category and in `Rep R G`, and
  `TopCat.Sheaf.IsFlasque` of `toSheaf`;
- the derived comparisons assert existence of a family of `Iso`s of functors,
  with the degree-zero equation on `Functor.toRightDerivedZero` and the
  inverse of the published zero identification;
- the acyclic comparisons assume vanishing of `ordinaryCohomology (q + 1)`
  resp. `compactCohomology (q + 1)` at `toSheaf` of the object, and conclude
  with `groupCohomology` of the section representation, naturality via
  `groupCohomology.functor`, and the inverse of `groupCohomology.H0Iso` in
  degree zero;
- the finite-group components carry `[Finite G]`, and the invariant
  comparisons also assume `IsUnit (Nat.card G : R)`.

Compilation and inspection establish well-formed statements; they do not prove
any of the eight assertions.
