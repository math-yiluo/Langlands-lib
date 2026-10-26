# Renard A.VI.2(2–3): subobjects, quotients, intersections and sums

This module states the two assertions in David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, Appendix
A.VI.2(2–3), printed page 262 / PDF page 268. The orders and equivalence classes
come from A.I.2, printed page 248 / PDF page 254. The abelian-category context is
A.VI.1, printed page 261 / PDF page 267.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 254 and 267–268 were read directly; pages 254 and 268 were also
visually checked. The retained author-page book section labels its separate
errata as applying to the 2010 edition. The appendix corrections on PDF pages
18–19 of the registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read; they contain no correction to these two assertions.

## Scope and declarations

All three definitions return `Prop`. Each takes arbitrary `C : Type u`,
`Category.{v} C` and `Abelian C`, with independent object and Hom universes.
Their content is quantified over every object of `C`.

- `Langlands.Renard.SubobjectQuotientCorrespondenceStatement` states both inverse
  identities, both order reversal equivalences, and the two representative
  formulas for the actual kernel and cokernel maps.
- `Langlands.Renard.BinarySubobjectLatticeStatement` states the universal order
  properties of the actual `P ⊓ Q` and `P ⊔ Q` for any two subobjects.
- `Langlands.Renard.SubobjectQuotientAndLatticeStatement` is their conjunction
  and the combined proof target.

These are statements awaiting proofs. The file defines the propositions without
assuming their conclusions or providing proof declarations.

## Source orders and the kernel–cokernel correspondence

For `X : C`, `Subobject X` is the collection of equivalence classes of
monomorphisms into `X`. For representatives `i₁ : Y₁ ⟶ X` and
`i₂ : Y₂ ⟶ X`, its order says that `i₁ ≤ i₂` when there is
`a : Y₁ ⟶ Y₂` with `a ≫ i₂ = i₁`. Equivalence identifies representatives
isomorphic over `X`, as in A.I.2.

The source quotient collection is `Subobject (op X)` in the opposite category.
An epimorphism `p : X ⟶ Y` represents the class `Subobject.mk p.op`.
For representatives `p₁ : X ⟶ Y₁` and `p₂ : X ⟶ Y₂`, its ordinary
subobject order says that the class of `p₁` is at most the class of `p₂`
exactly when there is `b : Y₂ ⟶ Y₁` with `p₂ ≫ b = p₁`. This is
precisely Renard's quotient order.

Mathlib's `cokernelOrderHom X` has codomain
`(Subobject (op X))ᵒᵈ`, the order dual of that source quotient collection.
Its monotonicity in the dual expresses reversal in the source order. The third
clause explicitly removes the dual and states

```text
P ≤ Q ↔ ofDual (cokernelOrderHom X Q) ≤ ofDual (cokernelOrderHom X P).
```

Likewise, `kernelOrderHom X` takes a quotient class in the dual order. The
fourth clause states, for arbitrary source quotient classes `K` and `L`,

```text
K ≤ L ↔ kernelOrderHom X (toDual L) ≤ kernelOrderHom X (toDual K).
```

The first two clauses assert that these maps compose to the identity on every
subobject and every quotient class, respectively. The remaining clauses identify
them on all mono and epi representatives:

```text
cokernelOrderHom X (Subobject.mk i)
  = toDual (Subobject.mk (cokernel.π i).op)
kernelOrderHom X (toDual (Subobject.mk p.op))
  = Subobject.mk (kernel.ι p).
```

Here `cokernel.π i : X ⟶ cokernel i` and `kernel.ι p : kernel p ⟶ X`
are the actual categorical cokernel and kernel maps. Thus the source notation
`X/P` means the quotient class of the actual cokernel projection of a mono
representing `P`. The equivalence classes remove dependence on the chosen mono,
epi, or kernel/cokernel representative. All displayed equalities are equalities
of subobject classes, with dual tags where required; they assert no literal
equality of chosen domain or quotient objects.

The imported Mathlib module `Mathlib.CategoryTheory.Abelian.Subobject` builds
`CategoryTheory.Abelian.subobjectIsoSubobjectOp` from these very two maps and
their inverse identities. This is the intended proof route, rather than an
unexplained existence assertion for an order isomorphism.

## The binary intersection and sum constructions

The second statement uses the existing lattice operations on categorical
`Subobject X`. It asserts, for every comparison subobject `R`,

```text
R ≤ P ⊓ Q ↔ R ≤ P ∧ R ≤ Q
P ⊔ Q ≤ R ↔ P ≤ R ∧ Q ≤ R.
```

Consequently the particular existing `P ⊓ Q` and `P ⊔ Q` are the greatest
lower bound and least upper bound required in A.I.2 and asserted to exist in
A.VI.2(3).

The imported definitions are categorical constructions. In
`Mathlib/CategoryTheory/Subobject/Lattice.lean`, `MonoOver.inf` first pulls back
one representative along the other representative and then composes its mono
with the map into `X`. `Subobject.inf` descends this construction to equivalence
classes. The theorem `Subobject.inf_isPullback` identifies the square formed by
the representative arrows of `P`, `Q`, and `P ⊓ Q` and its two canonical
inclusions as an actual pullback. `Subobject.inf_eq_map_pullback` also identifies
the intersection with the pullback followed by composition into `X`.

For representatives `i : Y ⟶ X` and `j : Z ⟶ X`, `MonoOver.sup` takes
the coproduct in the over category and then its image. This is the image mono
of `coprod.desc i j : Y ⨿ Z ⟶ X`. `Subobject.sup` descends it to the
subobject classes. Thus the source sum is the image subobject in `X` of the
coproduct map; the coproduct domain alone does not specify this sum. The
universal order property in the statement is the one implemented by this
construction. These descriptions were checked against the prepared Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, including
`CategoryTheory/Subobject/Limits.lean` for `cokernelOrderHom` and
`kernelOrderHom`.

## Coverage boundary

The source assertions are binary. There are no `WellPowered`, `LocallySmall`,
Grothendieck, finite-length, module, or additional smallness hypotheses.
Arbitrary meets and joins and the later well-powered opposite-category result
are outside these statements. Finite iteration and nullary bounds are also
outside the selected targets.

The passage from Renard's seven category axioms to the Mathlib `Abelian`
structure is a separate obligation. The other assertions of A.VI.2, Noether
isomorphisms, the 3-by-3 lemma, and the source AB4–AB6 conventions remain separate.
