# Renard A.VI.2(1, 4–5): balancedness, images, coimages and factorization

Author: Worker 207. The clause list follows the task specification written by
Worker 6 (task `adfa5ad0`). Worker 207 checked the original passage directly
and wrote this Lean/Markdown pair. This unit states the assertions; their proof
is a separate obligation.

## Original and reading boundary

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.VI.2(1), (4) and (5), with the two definitions
between (3) and (4), printed page 262 / PDF page 268. The subobject and quotient
orders come from A.I.2, printed page 248 / PDF page 254. The abelian-category
axioms are in A.VI.1, printed page 261 / PDF page 267.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 254 and 267–268 were read directly; PDF268 was also rendered and
checked visually.

Errata check: the registered author-page snapshot `renard-author-page-2026-10-26`
(SHA256 `143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`)
says its separate errata apply to the 2010 edition, and gives no errata for the
2026 version. The appendix corrections on PDF pages 18–19 of the registered
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) were
read. Their last entries for 2010 page 301 correct the adjunction example that
in the 2026 text directly precedes A.VI, on printed page 261. The next entry is
for 2010 page 305, a later Zorn argument. No entry corrects A.VI.1 or A.VI.2.
The 2026 text governs.

The source passages are:

- (1) A morphism of `𝒜` is an isomorphism if and only if it is both a
  monomorphism and an epimorphism.
- Definition: the *image* of `f : A → B` is the least subobject `C → B` of `B`
  such that `f` factors through `C → B`. Dually, the *coimage* of `f` is the
  least quotient `A → D` of `A` that factors `f`.
- (4) Every morphism `f : A → B` has an image (resp. a coimage), which is
  identified with `ker(coker f)` (resp. `coker(ker f)`).
- (5) (Factorization of morphisms) Every morphism `A → B` in `𝒜` factors,
  uniquely up to isomorphism, as `A → I → B` with `A → I` an epimorphism and
  `I → B` a monomorphism. Moreover `A → I` is the coimage of `A → B` and
  `I → B` is its image.

## Declarations

Module `Langlands.CategoryTheory.RenardImageFactorizationStatements`, namespace
`Langlands.Renard`. All six definitions return `Prop`. The four statements take
arbitrary `C : Type u` with `[Category.{v} C]` and `[Abelian C]`, with
independent object universe `u` and Hom universe `v`, and quantify over every
morphism `f : X ⟶ Y` of `C`. There is no concrete, module, finiteness,
smallness, `WellPowered` or Grothendieck hypothesis.

- `ImageUniversalProperty f e m` and `CoimageUniversalProperty f e m`: the two
  universal properties of a factorization `e ≫ m` of `f` through an object `I`,
  explained below. They only need `[Category.{v} C]`.
- `IsoIffMonoAndEpiStatement C`: source (1).
- `AbelianImageCoimageStatement C`: the definition of image and coimage together
  with source (4).
- `EpiMonoFactorizationStatement C`: source (5).
- `ImageFactorizationStatement C`: the conjunction of the three statements, and
  the single proof target.

The file defines the propositions only; it contains no theorem and does not
assume any conclusion.

## The two universal properties and their directions

A.I.2 orders monomorphisms `f₁ : Y₁ → X`, `f₂ : Y₂ → X` by `f₁ ≤ f₂` when
some `i : Y₁ → Y₂` has `i ≫ f₂ = f₁`. It orders epimorphisms `f₁ : X → Y₁`,
`f₂ : X → Y₂` by `f₁ ≤ f₂` when some `Y₂ → Y₁` has `f₂ ≫ (Y₂ → Y₁) = f₁`.
In the quotient order, a quotient that factors through another is smaller.

For `f : X ⟶ Y`, `e : X ⟶ I` and `m : I ⟶ Y`:

```lean
ImageUniversalProperty f e m :=
  ∀ (J : C) (e' : X ⟶ J) (m' : J ⟶ Y), Mono m' → e' ≫ m' = f →
    ∃! t : I ⟶ J, t ≫ m' = m ∧ e ≫ t = e'

CoimageUniversalProperty f e m :=
  ∀ (J : C) (e' : X ⟶ J) (m' : J ⟶ Y), Epi e' → e' ≫ m' = f →
    ∃! t : J ⟶ I, e' ≫ t = e ∧ t ≫ m = m'
```

*Image.* The map `t : I ⟶ J` with `t ≫ m' = m` says that the subobject `m` is
at most every subobject `m'` through which `f` factors. When `m` is mono, `m` is
therefore the least such subobject, which is Renard's definition of the image.
The extra equation `e ≫ t = e'` makes `t` a map of factorizations. Uniqueness
of `t` follows from `m'` being mono, and is stated explicitly.

*Coimage.* The arrow goes the other way: `t : J ⟶ I` from any epi factorization
`e' ≫ m' = f` to `e`. The equation `e' ≫ t = e` says that the quotient `e`
factors through the quotient `e'`, so `e ≤ e'` in the A.I.2 quotient order.
When `e` is epi, `e` is therefore the least quotient that factors `f`, which is
Renard's definition of the coimage. The extra equation `t ≫ m = m'` makes `t`
a map of factorizations. The statement does not reverse this arrow.

In each property the second equation adds nothing beyond the first. In the
image case, `e ≫ t ≫ m' = e ≫ m = f = e' ≫ m'` and `m'` is mono, so
`e ≫ t = e'`. In the coimage case, `e' ≫ t ≫ m = e ≫ m = f = e' ≫ m'` and
`e'` is epi, so `t ≫ m = m'`. A factorization through a mono `m'` (an epi `e'`)
is determined by `m'` (by `e'`). So for a mono `m` (an epi `e`) these
properties are exactly Renard's least-element conditions in the A.I.2 orders.
They state these conditions on representing maps. Renard's "least subobject"
determines a class up to the A.I.2 equivalence.

## The actual image and coimage: `AbelianImageCoimageStatement`

The statement uses Mathlib's actual constructions from
`Mathlib/CategoryTheory/Abelian/Images.lean` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). These are `abbrev`s:

```lean
Abelian.image f := kernel (cokernel.π f)
Abelian.image.ι f := kernel.ι (cokernel.π f)
Abelian.factorThruImage f := kernel.lift (cokernel.π f) f (cokernel.condition f)
Abelian.coimage f := cokernel (kernel.ι f)
Abelian.coimage.π f := cokernel.π (kernel.ι f)
Abelian.factorThruCoimage f := cokernel.desc (kernel.ι f) f (kernel.condition f)
```

Thus `Abelian.image f` is the actual `ker(coker f)` of source (4) and
`Abelian.coimage f` the actual `coker(ker f)`. The statement's first two clauses
make this visible. They hold definitionally, and they typecheck only because
the domains agree definitionally.

For every `f : X ⟶ Y` the statement asserts, in order:

1. `Abelian.image.ι f = kernel.ι (cokernel.π f)`;
2. `Abelian.coimage.π f = cokernel.π (kernel.ι f)`;
3. `ImageUniversalProperty f (Abelian.factorThruImage f) (Abelian.image.ι f)`:
   `ker(coker f)` is the image in Renard's sense. Written out, for every
   `e : X ⟶ I` and mono `m : I ⟶ Y` with `e ≫ m = f` there is a unique
   `t : Abelian.image f ⟶ I` with `t ≫ m = Abelian.image.ι f` and
   `Abelian.factorThruImage f ≫ t = e`;
4. `(Abelian.imageIsoImage f).hom ≫ Limits.image.ι f = Abelian.image.ι f`;
5. `Abelian.factorThruImage f ≫ (Abelian.imageIsoImage f).hom = Limits.factorThruImage f`;
6. `CoimageUniversalProperty f (Abelian.coimage.π f) (Abelian.factorThruCoimage f)`:
   `coker(ker f)` is the coimage in Renard's sense. Written out, for every epi
   `e : X ⟶ I` and `m : I ⟶ Y` with `e ≫ m = f` there is a unique
   `t : I ⟶ Abelian.coimage f` with `e ≫ t = Abelian.coimage.π f` and
   `t ≫ Abelian.factorThruCoimage f = m`;
7. `Epi (Abelian.factorThruImage f)`, `Mono (Abelian.image.ι f)` and
   `Abelian.factorThruImage f ≫ Abelian.image.ι f = f`;
8. `Epi (Abelian.coimage.π f)`, `Mono (Abelian.factorThruCoimage f)` and
   `Abelian.coimage.π f ≫ Abelian.factorThruCoimage f = f`;
9. `IsIso (Abelian.coimageImageComparison f)`;
10. `Abelian.coimage.π f ≫ Abelian.coimageImageComparison f = Abelian.factorThruImage f`
    and
    `Abelian.coimageImageComparison f ≫ Abelian.image.ι f = Abelian.factorThruCoimage f`.

Clauses 4–5 connect to the general categorical image `Limits.image f`. Here
`Abelian.imageIsoImage f : Abelian.image f ≅ Limits.image f` is the actual
Mathlib isomorphism from `Mathlib/CategoryTheory/Abelian/Basic.lean`. The two
clauses say it preserves the inclusion into `Y` and the factor map from `X`, so
the kernel-of-cokernel model and `Limits.image f` are the same subobject with
the same factorization.

Clauses 9–10 make explicit the identification behind source (5): the actual
comparison `Abelian.coimageImageComparison f : Abelian.coimage f ⟶ Abelian.image f`
(Mathlib's `cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f _) _`) is
an isomorphism compatible with both factor maps. So the coimage factorization and
the image factorization are the same epi–mono factorization.

Source (4) says that the image and coimage exist. Clauses 3 and 6 assert this by
naming a witness of each universal property. Literal equality of objects is not
asserted, except the definitional clauses 1–2. All other identifications are
isomorphisms or maps that preserve the displayed morphisms.

## `EpiMonoFactorizationStatement`

For every `f : X ⟶ Y` the statement asserts three clauses:

1. Existence: some `I`, `e : X ⟶ I` and `m : I ⟶ Y` have `Epi e`, `Mono m` and
   `e ≫ m = f`.
2. Uniqueness up to unique compatible isomorphism: for epi–mono factorizations
   `e ≫ m = f` through `I` and `e' ≫ m' = f` through `J`, there is a unique
   `t : I ≅ J` with `e ≫ t.hom = e'` and `t.hom ≫ m' = m`. This is how the
   statement reads the source's "uniquely up to isomorphism". The isomorphism
   respects both factor maps; an abstract isomorphism `I ≅ J` would not
   suffice. Uniqueness is uniqueness of the whole isomorphism. Since `t.hom`
   determines `t`, it is equivalent to uniqueness of the compatible map
   `t.hom`.
3. Identification: for every epi–mono factorization `e ≫ m = f`, both
   `ImageUniversalProperty f e m` and `CoimageUniversalProperty f e m` hold. This
   is the source's last sentence of (5): `A → I` is the coimage of `f` and
   `I → B` is its image, each in the least-element sense of the definition.

## `IsoIffMonoAndEpiStatement`

For every `f : X ⟶ Y`, `IsIso f ↔ Mono f ∧ Epi f`. This is source (1). In
Mathlib the corresponding lemma is `CategoryTheory.isIso_iff_mono_and_epi`, under
`Balanced C`, which every abelian category satisfies.

## The ambient abelian structure

The statements use Mathlib's `Abelian` class: preadditive with finite products,
kernels and cokernels, and every mono and epi normal. Renard's A.VI.1 uses the
axioms AB0 (zero object), AB1/AB1* (finite products and coproducts), AB2/AB2*
(kernels and cokernels) and AB3/AB3* (every mono is a kernel, every epi is a
cokernel). The Library module `Langlands.CategoryTheory.RenardAbelian` relates
these seven axioms to Mathlib's `Abelian` structure. These statements do not
duplicate it.

## Scope

This unit covers A.VI.2(1), the definitions of image and coimage, (4) and (5).
Out of scope, with separate owners:

- A.VI.2(2–3): `Langlands.CategoryTheory.RenardSubobjectQuotientStatements`
  (task `c5a46e17`);
- A.VI.2(8), the 3-by-3 lemma: `Langlands.CategoryTheory.RenardThreeByThreeStatement`
  (task `95698ee5`);
- A.VI.2(6), the abelian group structure on Hom sets:
  `Langlands.CategoryTheory.RenardAbelian`;
- the product–sum comparison (7), the Noether isomorphism theorems and the
  AB4–AB6 conventions: obligations of the parent whole-book task.

The statements do not depend on any chosen image or coimage object beyond
Mathlib's actual constructions. They add no axiom.
