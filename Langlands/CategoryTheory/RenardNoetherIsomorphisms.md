# Proof of Renard A.VI.2(9): Noether isomorphisms and complementary subobjects

This module proves the published statement
`Langlands.Renard.NoetherIsomorphismsStatement C` of
`Langlands.CategoryTheory.RenardNoetherIsomorphismStatements` for every
`C : Type u` with `[Category.{v} C]` and `[Abelian C]`. The object universe `u`
and the Hom universe `v` are independent. The statement is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, Appendix A.VI.2(9), printed page 263 / PDF page 269. Its meaning, the
conventions and the canonical normalizations are explained in the statement's
own Markdown. This module imports the statement by Lean name and does not change
it.

No hypothesis is added. There is no smallness, `WellPowered`, Grothendieck,
module, concreteness or finiteness assumption. The axioms used are only
`propext`, `Classical.choice` and `Quot.sound`.

## Declarations

All declarations are in namespace `Langlands.Renard`.

| Declaration | Type |
| --- | --- |
| `noetherIsomorphisms` | `∀ (C : Type u) [Category.{v} C] [Abelian C], NoetherIsomorphismsStatement C` |
| `nestedQuotientIso` | `∀ (C : Type u) [Category.{v} C] [Abelian C], NestedQuotientIsoStatement C` |
| `secondIso` | `∀ (C : Type u) [Category.{v} C] [Abelian C], SecondIsoStatement C` |
| `complementarySubobjectsSum` | `∀ (C : Type u) [Category.{v} C] [Abelian C], ComplementarySubobjectsSumStatement C` |

`noetherIsomorphisms` is the proof of the aggregate. It is the triple
`⟨nestedQuotientIso C, secondIso C, complementarySubobjectsSum C⟩`. The three
clause theorems are separately reusable.

Three auxiliary lemmas hold in any abelian category `C`, with `C` implicit:

- `exists_lift_of_comp_cokernel_π (m : P ⟶ Y) [Mono m] (g : W ⟶ Y)
  (hg : g ≫ cokernel.π m = 0) : ∃ l : W ⟶ P, l ≫ m = g`.
  A morphism killed by the cokernel projection of a monomorphism factors
  through that monomorphism.
- `mono_cokernel_desc_of_factors (i : K ⟶ Y) [Mono i] (f : Y ⟶ Z)
  (w : i ≫ f = 0) (hf : ∀ {W} (g : W ⟶ Y), g ≫ f = 0 → ∃ l, l ≫ i = g) :
  Mono (cokernel.desc i f w)`.
  If the monomorphism `i` is a kernel of `f`, then the map
  `cokernel i ⟶ Z` induced by `f` is a monomorphism.
- `eq_zero_of_ofLE_sup_comp {A B : Subobject X}
  (k : ((A ⊔ B : Subobject X) : C) ⟶ W)
  (ha : Subobject.ofLE A (A ⊔ B) le_sup_left ≫ k = 0)
  (hb : Subobject.ofLE B (A ⊔ B) le_sup_right ≫ k = 0) : k = 0`.
  A morphism out of the underlying object of `A ⊔ B` that vanishes on `A` and
  on `B` is zero.

## Proof route

Renard says that the assertions follow from the 3-by-3 lemma A.VI.2(8). This
proof does not use the 3-by-3 lemma. It uses Mathlib's exactness API for short
complexes and the lattice structure of `Subobject X`. The 3-by-3 lemma remains a
separate obligation and is neither used nor proved here.

### Auxiliary lemmas

`exists_lift_of_comp_cokernel_π`. The short complex
`m, cokernel.π m` is exact by `ShortComplex.exact_of_g_is_cokernel` applied to
`cokernelIsCokernel m`. Since `m` is a monomorphism, `ShortComplex.Exact.lift`
and `ShortComplex.Exact.lift_f` give the factorization.

`mono_cokernel_desc_of_factors`. The hypothesis `hf` and `Mono i` give
`IsLimit (KernelFork.ofι i w)` through `KernelFork.IsLimit.ofι'`. So the short
complex `i, f` is exact by `ShortComplex.exact_of_f_is_kernel`.
`ShortComplex.Exact.mono_cokernelDesc` then says that
`cokernel.desc i f w` is a monomorphism.

`eq_zero_of_ofLE_sup_comp`. Let `m = kernel.ι k ≫ (A ⊔ B).arrow`, a
monomorphism into `X`. The morphisms `kernel.lift k _ ha` and
`kernel.lift k _ hb` show `A ≤ Subobject.mk m` and `B ≤ Subobject.mk m`
(`Subobject.le_mk_of_comm`). Hence `A ⊔ B ≤ Subobject.mk m` by `sup_le`. Let
`s = Subobject.ofLEMk (A ⊔ B) m _`. By `Subobject.ofLEMk_comp`, `s ≫ m` is
`(A ⊔ B).arrow`. Cancelling the monomorphism `(A ⊔ B).arrow` gives
`s ≫ kernel.ι k = 𝟙`. Therefore `k = s ≫ kernel.ι k ≫ k = 0`.

### Assertion (i): `nestedQuotientIso`

Fix `X`, `A ≤ B` with witness `h`, and write `i = Subobject.ofLE A B h`. The
statement's `j` is introduced as a local definition. Mathlib's `cokernel.map` is
by definition `cokernel.desc i (B.arrow ≫ cokernel.π A.arrow) _`, so
`j = cokernel.desc i (B.arrow ≫ cokernel.π A.arrow) w` holds by `rfl`. Hence
`cokernel.π i ≫ j = B.arrow ≫ cokernel.π A.arrow`.

*`Mono j`.* Apply `mono_cokernel_desc_of_factors` to `i` and
`f = B.arrow ≫ cokernel.π A.arrow`. Let `g : W ⟶ (B : C)` satisfy `g ≫ f = 0`.
Then `g ≫ B.arrow` is killed by `cokernel.π A.arrow`.
`exists_lift_of_comp_cokernel_π` gives `l` with `l ≫ A.arrow = g ≫ B.arrow`.
Since `i ≫ B.arrow = A.arrow` (`Subobject.ofLE_arrow`), cancelling the
monomorphism `B.arrow` gives `l ≫ i = g`. So `i` is a kernel of `f`, and `j` is a
monomorphism.

*The normalized isomorphism.* Let
`q = cokernel.desc A.arrow (cokernel.π B.arrow) _ : cokernel A.arrow ⟶ cokernel B.arrow`.
This is the further quotient map *X*/*A* → *X*/*B*, and
`cokernel.π A.arrow ≫ q = cokernel.π B.arrow`. Precomposing with the
epimorphism `cokernel.π i` shows `j ≫ q = 0`. Let
`r = cokernel.desc B.arrow (cokernel.π A.arrow ≫ cokernel.π j) _ : cokernel B.arrow ⟶ cokernel j`.
It is well defined because `B.arrow ≫ cokernel.π A.arrow = cokernel.π i ≫ j`.
The isomorphism is

```text
e := { hom := cokernel.desc j q _, inv := r, .. } : cokernel j ≅ cokernel B.arrow
```

Both inverse laws are checked after cancelling the epimorphisms `cokernel.π j`,
`cokernel.π A.arrow` and `cokernel.π B.arrow`. The required equation
`cokernel.π A.arrow ≫ cokernel.π j ≫ e.hom = cokernel.π B.arrow` follows from
`cokernel.π_desc` and the equation for `q`. In particular
`cokernel.π j ≫ e.hom = q`, so `e` is the isomorphism induced by the actual
further quotient map, as the statement's Markdown describes.

### Assertion (ii): `secondIso`

Fix `X`, `A` and `B`. Write `i = Subobject.ofLE (A ⊓ B) B inf_le_right`,
`a = Subobject.ofLE A (A ⊔ B) le_sup_left` and
`b = Subobject.ofLE B (A ⊔ B) le_sup_right`. Cancelling `(A ⊔ B).arrow` shows
`i ≫ b = Subobject.ofLE (A ⊓ B) A inf_le_left ≫ a`. So
`i ≫ b ≫ cokernel.π a = 0`. Let

```text
φ := cokernel.desc i (b ≫ cokernel.π a) _ : cokernel i ⟶ cokernel a
```

It satisfies `cokernel.π i ≫ φ = b ≫ cokernel.π a` by `cokernel.π_desc`.

*`Mono φ`.* Apply `mono_cokernel_desc_of_factors`. Let `g : W ⟶ (B : C)` satisfy
`g ≫ b ≫ cokernel.π a = 0`. `exists_lift_of_comp_cokernel_π` applied to the
monomorphism `a` gives `l` with `l ≫ a = g ≫ b`. Composing with `(A ⊔ B).arrow`
gives `l ≫ A.arrow = g ≫ B.arrow`. Thus `g ≫ B.arrow` factors through `A` and
through `B`. By `Subobject.inf_factors` it factors through `A ⊓ B`. Then
`(A ⊓ B).factorThru (g ≫ B.arrow) _ ≫ i = g`, after cancelling `B.arrow`.

*`Epi φ`.* First, `b ≫ cokernel.π a` is an epimorphism, by
`Preadditive.epi_of_cancel_zero`. Let `g` satisfy `(b ≫ cokernel.π a) ≫ g = 0`.
The morphism `cokernel.π a ≫ g` vanishes on `a` by `cokernel.condition`, and on
`b` by hypothesis. By `eq_zero_of_ofLE_sup_comp` it is zero. Cancelling the
epimorphism `cokernel.π a` gives `g = 0`. Since
`cokernel.π i ≫ φ = b ≫ cokernel.π a`, `epi_of_epi` shows that `φ` is an
epimorphism.

An abelian category is balanced, so `φ` is an isomorphism by
`isIso_of_mono_of_epi`. The witness is `e := asIso φ`. Its equation is the
equation for `φ` above.

### Final assertion: `complementarySubobjectsSum`

Fix `X`, `A` and `B` with `A ⊓ B = ⊥` and `A ⊔ B = ⊤`. The proof first shows
that `biprod.desc A.arrow B.arrow : (A : C) ⊞ (B : C) ⟶ X` is an isomorphism.
It then transfers this to the binary coproduct. Biproducts are only an auxiliary
device here. The conclusion is about the actual
`coprod.desc A.arrow B.arrow : (A : C) ⨿ (B : C) ⟶ X`.

*Mono.* Use `Preadditive.mono_of_cancel_zero`. Let `g : W ⟶ (A : C) ⊞ (B : C)`
satisfy `g ≫ biprod.desc A.arrow B.arrow = 0`. Write `x = g ≫ biprod.fst` and
`y = g ≫ biprod.snd`. By `biprod.desc_eq`, `x ≫ A.arrow + y ≫ B.arrow = 0`, so
`x ≫ A.arrow = (-y) ≫ B.arrow`. This morphism factors through `A` and through
`B`, hence through `A ⊓ B = ⊥` (`Subobject.inf_factors`). By
`Subobject.bot_factors_iff_zero` it is zero. Cancelling the monomorphisms
`A.arrow` and `B.arrow` gives `x = 0` and `y = 0`. So `g = 0` by
`biprod.hom_ext`.

*Epi.* Use `Preadditive.epi_of_cancel_zero`. Let `g : X ⟶ R` satisfy
`biprod.desc A.arrow B.arrow ≫ g = 0`. Precomposing with `biprod.inl` and
`biprod.inr` gives `A.arrow ≫ g = 0` and `B.arrow ≫ g = 0`. The morphism
`(A ⊔ B).arrow ≫ g` therefore vanishes on `A` and on `B`, since
`Subobject.ofLE _ _ _ ≫ (A ⊔ B).arrow` is the corresponding `arrow`. By
`eq_zero_of_ofLE_sup_comp` it is zero. Since `A ⊔ B = ⊤`, `(A ⊔ B).arrow` is an
isomorphism (`Subobject.isIso_arrow_iff_eq_top`). Cancelling it gives `g = 0`.

So `biprod.desc A.arrow B.arrow` is an isomorphism (`isIso_of_mono_of_epi`).
Finally,

```text
coprod.desc A.arrow B.arrow =
  (biprod.isoCoprod (A : C) (B : C)).inv ≫ biprod.desc A.arrow B.arrow
```

holds by `ext` and `simp`, using `biprod.isoCoprod_inv`. A composite of
isomorphisms is an isomorphism. The coproduct instance in the statement and the
one used by `biprod.isoCoprod` give the same object, because
`HasColimit` is a proposition.

## Reuse

Everything reused is from Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- the short-complex exactness API: `ShortComplex.exact_of_f_is_kernel`,
  `ShortComplex.exact_of_g_is_cokernel`, `ShortComplex.Exact.lift`,
  `ShortComplex.Exact.lift_f` and `ShortComplex.Exact.mono_cokernelDesc`;
- kernel and cokernel API: `KernelFork.IsLimit.ofι'`, `cokernelIsCokernel`,
  `cokernel.desc`, `cokernel.π_desc` and `cokernel.condition`;
- the subobject API: `Subobject.ofLE_arrow`, `Subobject.le_mk_of_comm`,
  `Subobject.ofLEMk_comp`, `Subobject.inf_factors`,
  `Subobject.factors_comp_arrow`, `Subobject.factorThru`,
  `Subobject.bot_factors_iff_zero` and `Subobject.isIso_arrow_iff_eq_top`;
- the biproduct API: `biprod.desc_eq`, `biprod.hom_ext` and
  `biprod.isoCoprod_inv`;
- `Preadditive.mono_of_cancel_zero`, `Preadditive.epi_of_cancel_zero`,
  `epi_of_epi` and `isIso_of_mono_of_epi`.

No Library declaration other than the target statements is used.

## Scope

The module proves exactly the three assertions of A.VI.2(9) and their
conjunction. The other Appendix A assertions remain separate obligations. In
particular the 3-by-3 lemma A.VI.2(8), stated as
`Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement` in module
`Langlands.CategoryTheory.RenardThreeByThreeStatement`, is not proved here, and
this route does not depend on it.
