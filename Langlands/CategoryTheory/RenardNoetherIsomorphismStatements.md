# Renard A.VI.2(9): Noether isomorphisms and complementary subobjects

This module states the three assertions of David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, Appendix
A.VI.2(9), printed page 263 / PDF page 269. These are the two Noether isomorphism
theorems and the direct-sum decomposition for complementary subobjects. All of
them are stated on actual categorical subobjects, their actual inclusion maps and
actual cokernels in an arbitrary abelian category.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 267–269 were read: the abelian-category axioms of A.VI.1, the
subobject, quotient, intersection and sum conventions of A.VI.2(2–3), the 3-by-3
lemma A.VI.2(8), and the target A.VI.2(9). PDF page 269 was also checked
visually. The current Library has no `notes/errata` file for this source. The
registered 2010-edition errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were
also checked. Their appendix corrections on PDF pages 18–19 were read, and a
search of their full extracted text finds no entry for the Noether isomorphisms
or A.VI.2(9). That errata list concerns a different edition, so the 2026 text
governs here.

## The source passage

On PDF page 269 the original reads:

> — 9. *Isomorphismes de Noether.* Du lemme des 3 × 3, on peut facilement
> déduire les deux théorèmes d'isomorphismes de Noether :
> (*i*) étant donnés un objet *C* dans 𝒜 et deux sous-objets *A* et *B* de *C*
> avec *A* ⊆ *B*, alors *B*/*A* est un sous-objet de *C*/*A* et
> (*C*/*A*)/(*B*/*A*) est isomorphe à *C*/*B*,
> (*ii*) étant donnés un objet *C* dans 𝒜 et deux sous-objets *A* et *B* de
> *C*, on a *B*/(*A* ∩ *B*) ≃ (*A* + *B*)/*A*.
> En supposant de plus que *A* ∩ *B* = 0, et *A* + *B* = *C*, (*ii*) donne
> *C* ≃ *A* ⊕ *B*.

The source names the abelian category 𝒜 and the ambient object *C*. In the Lean
statements the category is `C` and the ambient object is `X`. The subobjects keep
the names `A` and `B`.

## Conventions used

The following correspondences come from the source and from the imported Mathlib
definitions, at the prepared commit `5ed2965256430c3649e86755f9576b54eca72435`.

- A subobject *A* of the ambient object is an actual `A : Subobject X`, an
  equivalence class of monomorphisms into `X`. Its chosen underlying object is
  `(A : C)` and its chosen representative mono is `A.arrow : (A : C) ⟶ X`.
- The source inclusion *A* ⊆ *B* is the order `A ≤ B` of `Subobject X`. Its
  canonical witness is `Subobject.ofLE A B h : (A : C) ⟶ (B : C)`. This map is
  a monomorphism and satisfies `Subobject.ofLE A B h ≫ B.arrow = A.arrow`
  (`Subobject.ofLE_arrow`).
- A.VI.2(2) writes *X*/*A* for the quotient coker(*A* → *X*). Every displayed
  quotient is therefore the actual cokernel of the indicated inclusion, with its
  projection `cokernel.π`. Thus *X*/*A* is `cokernel A.arrow` and *B*/*A* is
  `cokernel (Subobject.ofLE A B h)`.
- The intersection *A* ∩ *B* and the sum *A* + *B* of A.VI.2(3) are Mathlib's
  `A ⊓ B` and `A ⊔ B` on `Subobject X`. `A ⊓ B` is built from the pullback of the
  two representatives. `A ⊔ B` is the image of
  `coprod.desc A.arrow B.arrow`. These are the same operations used in
  `Langlands.Renard.BinarySubobjectLatticeStatement`.
- The zero subobject is `⊥ : Subobject X`. Its underlying object is a zero object
  (`Subobject.botCoeIsoZero`). The whole object is `⊤ : Subobject X`, the class of
  `𝟙 X`.
- The last line of A.VI.1 (PDF page 267) states that in abelian categories one says
  "somme directe" and writes ⊕ instead of "coproduit" and ∐. The source sum
  *A* ⊕ *B* is therefore the binary coproduct `(A : C) ⨿ (B : C)` of the two
  underlying objects.

## Scope and declarations

All four definitions are in namespace `Langlands.Renard` and return `Prop`. Each
takes an arbitrary `C : Type u` with `[Category.{v} C]` and `[Abelian C]`. The
object universe `u` and the Hom universe `v` are independent. There are no
smallness, `WellPowered`, Grothendieck, module, concreteness or finiteness
hypotheses. Each statement quantifies over every ambient object `X : C` and every
pair of subobjects.

### `NestedQuotientIsoStatement C` (assertion (i))

```text
∀ (X : C) (A B : Subobject X) (h : A ≤ B),
  let j := cokernel.map (Subobject.ofLE A B h) A.arrow (𝟙 (A : C)) B.arrow (by simp);
  Mono j ∧
    ∃ e : cokernel j ≅ cokernel B.arrow,
      cokernel.π A.arrow ≫ cokernel.π j ≫ e.hom = cokernel.π B.arrow
```

Write `i = Subobject.ofLE A B h`. The map `j : cokernel i ⟶ cokernel A.arrow` is
the source map *B*/*A* → *X*/*A*. It is induced on cokernels by the commutative
square with `𝟙 (A : C)` on the left and `B.arrow` on the right. The side
condition `i ≫ B.arrow = 𝟙 _ ≫ A.arrow` is proved inline by `simp` from
`Subobject.ofLE_arrow`. Mathlib defines `cokernel.map` as
`cokernel.desc i (B.arrow ≫ cokernel.π A.arrow) _`. By `cokernel.π_desc`, `j` is
therefore characterized by

```text
cokernel.π i ≫ j = B.arrow ≫ cokernel.π A.arrow.
```

This is the defining normalization of the embedding. Since `cokernel.π i` is an
epimorphism, any other map with this normalization equals `j`. So the explicit
term is exactly the canonical map, and the statement implies the existential
formulation "some mono `j` with this normalization admits the normalized
isomorphism `e`".

The first conjunct, `Mono j`, is the source claim that *B*/*A* is a subobject of
*X*/*A*: the subobject is the class of `j`. The second conjunct is the claim
(*X*/*A*)/(*B*/*A*) ≅ *X*/*B*. Here (*X*/*A*)/(*B*/*A*) is the actual
`cokernel j`, and the isomorphism `e` must satisfy the displayed normalization.
That equation says that the composite of the two successive quotient projections
`X ⟶ X/A ⟶ (X/A)/(B/A)`, followed by `e.hom`, is the quotient projection
`X ⟶ X/B`.

The actual further quotient map *X*/*A* → *X*/*B* is
`q = cokernel.map A.arrow B.arrow i (𝟙 X) (by simp)`. It satisfies
`cokernel.π A.arrow ≫ q = cokernel.π B.arrow`. Since `cokernel.π A.arrow` is an
epimorphism, the normalization of `e` is equivalent to

```text
cokernel.π j ≫ e.hom = q.
```

Thus `e` is exactly the isomorphism induced by the further quotient map, not an
unrelated abstract isomorphism. The normalization also determines `e.hom`
uniquely, because `cokernel.π A.arrow ≫ cokernel.π j` is an epimorphism.

### `SecondIsoStatement C` (assertion (ii))

```text
∀ (X : C) (A B : Subobject X),
  ∃ e : cokernel (Subobject.ofLE (A ⊓ B) B inf_le_right) ≅
      cokernel (Subobject.ofLE A (A ⊔ B) le_sup_left),
    cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫ e.hom =
      Subobject.ofLE B (A ⊔ B) le_sup_right ≫
        cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left)
```

The domain of `e` is *B*/(*A* ∩ *B*), the cokernel of the actual inclusion of
`A ⊓ B` into `B`. The codomain is (*A* + *B*)/*A*, the cokernel of the actual
inclusion of `A` into `A ⊔ B`. The required equation says that `e.hom`, after the
projection from `B`, is the composite of the inclusion `B ⟶ A ⊔ B` and the
projection onto (*A* + *B*)/*A*. This is the canonical map
*B*/(*A* ∩ *B*) → (*A* + *B*)/*A*. The equation determines `e.hom`, since the
projection from `B` is an epimorphism. Hence the statement asserts that this
canonical map is an isomorphism, and is stronger than an abstract isomorphism of
the two quotient objects.

### `ComplementarySubobjectsSumStatement C` (the final assertion)

```text
∀ (X : C) (A B : Subobject X),
  A ⊓ B = ⊥ → A ⊔ B = ⊤ → IsIso (coprod.desc A.arrow B.arrow)
```

The hypotheses are the source conditions *A* ∩ *B* = 0 and *A* + *B* = *C*,
written as equalities in the order of `Subobject X`. The conclusion is that the
actual comparison `coprod.desc A.arrow B.arrow : (A : C) ⨿ (B : C) ⟶ X` is an
isomorphism. The source writes only *C* ≃ *A* ⊕ *B*. Stating that this canonical
map is an isomorphism is the intended realization of that claim, and a stronger
statement than an abstract isomorphism. It is equivalent to the existence of
`e : X ≅ (A : C) ⨿ (B : C)` with `e.inv = coprod.desc A.arrow B.arrow`. The
coproduct is the source direct sum by the A.VI.1 convention quoted above. The
statement does not use biproducts.

### `NoetherIsomorphismsStatement C`

This is the conjunction

```text
NestedQuotientIsoStatement C ∧ SecondIsoStatement C ∧
  ComplementarySubobjectsSumStatement C
```

and is the combined proof target for A.VI.2(9).

## Provenance of the normalizations

The source states only the existence of the subobject *B*/*A* ⊆ *X*/*A* and the
isomorphisms. It does not display the maps. The normalization equations in the
first two statements, and the choice of the comparison map in the third, are
derived specifications of the canonical constructions that the source uses
implicitly. They are not additional numbered assertions of the original. Each of
them pins the map down uniquely, as explained above, so the statements cannot be
satisfied by unrelated isomorphisms.

## Proof route

The source says these assertions follow easily from the 3-by-3 lemma
A.VI.2(8). That lemma is stated separately in
`Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement`. This module
neither imports nor assumes it. These definitions are statements awaiting proof:
the file assumes none of their conclusions and contains no proof declarations.
A later proof may use the 3-by-3 lemma or any other valid route. Its own Markdown
must record which route it takes.

## Coverage boundary

The module covers exactly the three assertions of A.VI.2(9). The following are
separate obligations of the parent coverage task and are not stated here:

- the passage from Renard's seven axioms AB0–AB3* to Mathlib's `Abelian`
  structure;
- the subobject–quotient correspondence and the lattice universal properties of
  A.VI.2(2–3);
- the image and coimage factorization of A.VI.2(4–5);
- the binary product and coproduct comparison of A.VI.2(7);
- the 3-by-3 lemma of A.VI.2(8);
- the infinitary conventions AB4, AB4*, AB5 and A.VI.2(10);
- the general Jordan–Hölder statements of A.VI.3.
