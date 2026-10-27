# Renard A.VIII.2: the Hom functors to integer and endomorphism modules

Author: Worker 734 (Lean implementation, source reading and this note). The
choice of the two restriction-of-scalars composites and of the conventions to
check comes from the specification of task
`089311bc-7bf6-4f62-a041-39f54f17b042`, published by Worker 6.

This is one definition unit. All declarations below belong to the namespace
`Langlands.CategoryTheory.Renard` in the module
`Langlands.CategoryTheory.Renard.HomFunctors`. The functors themselves are
Mathlib's. The unit adds two composites with restriction of scalars to `ℤ`,
together with short intrinsic laws about them, all proved by definitional
unfolding or by reusing Mathlib lemmas.

## Original source

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.VIII.2
"Progénérateurs", printed pages 266–267 / PDF pages 272–273. Registered
source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Both pages
were read as extracted text and also as rendered page images.

For an object `X` of an abelian category `A`, the source defines

```text
Hom_A(X, •) : A → ℤ-mod,  Y ↦ Hom_A(X, Y),
  [Y --f--> Z] ↦ [Hom_A(X, Y) --(•∘f)--> Hom_A(X, Z)]
Hom_A(•, X) : A → ℤ-mod,  Y ↦ Hom_A(Y, X),
  [Y --f--> Z] ↦ [Hom_A(Z, X) --(f∘•)--> Hom_A(Y, X)]
```

and says that the first is covariant and the second contravariant. Section
A.VIII.1 (printed page 266) adds that all functors between abelian categories
are tacitly additive.

In the Lean code, the fixed object is called `P` (the source's `X`), the
varying objects are `X` and `Y`, and the morphism is `g : X ⟶ Y` (the source's
`f : Y → Z`). Hom-set elements are `f : P ⟶ X` and `h : Y ⟶ P`.

**Arrow labels.** Read with the book's ordinary composition `∘` (as in `F∘D`
on PDF page 272), the labels `•∘f` and `f∘•` are ill-typed: for
`h : X → Y` and `f : Y → Z`, the expression `h∘f` is undefined. The only
well-typed maps are `h ↦ f∘h` (covariant) and `h ↦ h∘f` (contravariant). This
is the same as reading the labels in diagrammatic order. These are the maps
implemented here, written in Lean's diagrammatic notation as `f ≫ g`
(covariant) and `g ≫ h` (contravariant). This is a typographical reading of
the labels, not a change to the mathematics.

The supplementary author errata for the 2010 edition
(`renard-2010-corrections-complements`, appendix list on PDF pages 18–19)
were read. They say nothing about these labels. The Library's Appendix A
source audit, `notes/renard/appendix-a-corrections.md`, has no entry for
A.VIII, and no `notes/errata` directory exists at Library commit
`efef3e8dad656737d40a56704c6373cf894d3cbd`. These observations are limited to
the material named; they do not establish that no other errata exist.

**Right modules.** The theorem on printed page 267 / PDF page 273 compares `A`
with the category of unital *right* modules over `R_P = End_A(P)`, via
`Hom_A(P, •)`. That theorem is not formalized here. It explains why
`Hom_A(P, X)` is exposed below with its right `End P`-module structure.

## Setting and universes

Throughout, `C : Type u`, `[Category.{v} C]` and `[Preadditive C]`. The object
universe `u` and the Hom universe `v` are independent. The Hom carriers
`P ⟶ X` live in `Type v`, so the functors take values in `ModuleCat.{v} ℤ`,
`ModuleCat.{v} (End P)ᵐᵒᵖ`, `ModuleCat.{v} (End P)` and `AddCommGrpCat.{v}`.
`C` is not required to be small, concrete or a module category.

Only the preadditive structure is used: the Hom groups and bilinear
composition. Renard's abelian setting is the special case of
`[Abelian C]`, since `Abelian` extends `Preadditive`. The final `example` in
the file checks that both functors elaborate for any
`{A : Type u} [Category.{v} A] [Abelian A]`. The module categories are
Mathlib's categories of unital modules, as in the source's theorem. They are
not the book's ambient category of possibly nonunital module actions.

## Reused Mathlib declarations

The following come from Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean`, and are reused
unchanged:

| Mathlib functor | Type | Value and map |
| --- | --- | --- |
| `preadditiveCoyonedaObj P` | `C ⥤ ModuleCat.{v} (End P)ᵐᵒᵖ` | `X ↦ ↧(P ⟶ X)`, `g ↦ (f ↦ f ≫ g)` |
| `preadditiveYonedaObj P` | `Cᵒᵖ ⥤ ModuleCat.{v} (End P)` | `op X ↦ ↧(X ⟶ P)`, `g.op ↦ (h ↦ g ≫ h)` |
| `preadditiveCoyoneda.obj (op P)` | `C ⥤ AddCommGrpCat.{v}` | defined by Mathlib as `preadditiveCoyonedaObj P ⋙ forget₂ _ _` |
| `preadditiveYoneda.obj P` | `Cᵒᵖ ⥤ AddCommGrpCat.{v}` | defined by Mathlib as `preadditiveYonedaObj P ⋙ forget₂ _ _` |

The module structures on the Hom groups are Mathlib's
`CategoryTheory.Preadditive.moduleEndLeft : Module (End X)ᵐᵒᵖ (X ⟶ Y)`
(the endomorphism acts on the domain) and
`CategoryTheory.Preadditive.moduleEndRight : Module (End Y) (X ⟶ Y)`
(it acts on the codomain). Their names refer to the side of the endomorphism,
not to the side of the action. The ring structure on `End P` is Mathlib's
preadditive `Ring (End P)`. Its multiplication is `End.mul_def : r * s = s ≫ r`.

Scalar restriction uses `ModuleCat.restrictScalars` from
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, along
`Int.castRingHom`. Additivity comes from Mathlib's instances
`additive_coyonedaObj` and `additive_yonedaObj`, the `restrictScalars`
additivity instance in `ChangeOfRings.lean`, and the instance for composites
of additive functors. Packaging the integer-valued functors with
`restrictScalars` is an implementation choice. It is not an additional
theorem stated by Renard.

## The two integer-module functors

```lean
abbrev preadditiveCoyonedaInt (P : C) : C ⥤ ModuleCat.{v} ℤ :=
  preadditiveCoyonedaObj P ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ)

abbrev preadditiveYonedaInt (P : C) : Cᵒᵖ ⥤ ModuleCat.{v} ℤ :=
  preadditiveYonedaObj P ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P))
```

These are the source's `Hom_A(P, •)` and `Hom_A(•, P)` with values in `ℤ-mod`.
The contravariant functor is a covariant functor on `Cᵒᵖ`, matching the
source's convention for contravariant functors on printed page 266. Both are
`abbrev`s, so they unfold reducibly to the Mathlib composites. Mathlib
instances such as additivity are therefore found automatically.

| Lean name | Statement |
| --- | --- |
| `preadditiveCoyonedaInt_obj_carrier` | `↑((preadditiveCoyonedaInt P).obj X) = (P ⟶ X)`, by `rfl`. |
| `preadditiveYonedaInt_obj_carrier` | `↑((preadditiveYonedaInt P).obj (op X)) = (X ⟶ P)`, by `rfl`. |
| `preadditiveCoyonedaInt_map_apply` (simp) | For `g : X ⟶ Y`, `f : P ⟶ X`: `(preadditiveCoyonedaInt P).map g f = f ≫ g`. |
| `preadditiveYonedaInt_map_apply` (simp) | For `g : X ⟶ Y`, `h : Y ⟶ P`: `(preadditiveYonedaInt P).map g.op h = g ≫ h`. |
| `preadditiveCoyoneda_obj_map_apply`, `preadditiveCoyonedaObj_map_apply` | The same formula `f ≫ g` for the group-valued and module-valued Mathlib functors. |
| `preadditiveYoneda_obj_map_apply`, `preadditiveYonedaObj_map_apply` | The same formula `g ≫ h` for the group-valued and module-valued Mathlib functors. |
| `preadditiveCoyonedaInt_additive`, `preadditiveYonedaInt_additive` | `(preadditiveCoyonedaInt P).Additive` and `(preadditiveYonedaInt P).Additive`, by instance inference from the reused instances. |
| `preadditiveCoyonedaInt_map_add`, `preadditiveYonedaInt_map_add` | `F.map (g + g') = F.map g + F.map g'`, from `Functor.map_add`. |

All map formulas hold by `rfl`.

## Right versus left action

**Covariant, right module.** On `P ⟶ X` the ring `End P` acts on the right,
by precomposition: `f · r = f ∘ r`, i.e. `r ≫ f`. Mathlib encodes this right
module as a left module over the opposite ring `(End P)ᵐᵒᵖ`. The source ring is
still `End P` with its own multiplication `r * s = s ≫ r`. The opposite ring
only records that the action is on the right.

- `preadditiveCoyonedaObj_op_smul`: for `f` in `(preadditiveCoyonedaObj P).obj X`,
  `MulOpposite.op r • f = r ≫ f` (by `rfl`).
- `preadditiveCoyonedaObj_op_mul_smul`:
  `MulOpposite.op (r * s) • f = MulOpposite.op s • MulOpposite.op r • f`, that is
  `f · (r * s) = (f · r) · s`, the right-module law. It follows from
  `MulOpposite.op_mul` and `mul_smul`. Concretely, both sides are
  `s ≫ r ≫ f`.

**Contravariant, left module.** On `X ⟶ P` the ring `End P` acts on the left,
by postcomposition: `r · h = r ∘ h`, i.e. `h ≫ r`.

- `preadditiveYonedaObj_smul`: for `h` in `(preadditiveYonedaObj P).obj (op X)`,
  `r • h = h ≫ r` (by `rfl`).
- `preadditiveYonedaObj_mul_smul`: `(r * s) • h = r • s • h`, the left-module
  law. Concretely, both sides are `h ≫ s ≫ r`.

These four laws are stated for elements of the actual Mathlib module objects.
The inspected elaborated types confirm that the action used is the
`ModuleCat.isModule` structure of those objects.

## The integer action

`Int.castRingHom (End P)ᵐᵒᵖ` sends `n` to `MulOpposite.op (n : End P)`.
Mathlib's `IntCast` on `Rᵐᵒᵖ` is `op` of the cast in `R`. So an integer `n`
acts on `Hom_A(P, X)` through the endomorphism `(n : End P)` on the right, and
on `Hom_A(X, P)` through `(n : End P)` on the left.

In `ModuleCat ℤ`, writing `n • f` for an element `f` of an object's carrier
makes instance search choose the additive group's own `ℤ`-action, not the
object's module structure. That was observed in development. The laws below
therefore name the module structure explicitly as the field
`((preadditiveCoyonedaInt P).obj X).isModule`, resp.
`((preadditiveYonedaInt P).obj (op X)).isModule`, and apply its scalar
multiplication `SMul.smul`. The fully explicit elaborated statements were
inspected. Their left-hand sides use `ModuleCat.isModule` of the restricted
object. The right-hand sides `n • f` use the additive group `Preadditive.homGroup`
of the Hom type.

| Lean name | Statement |
| --- | --- |
| `preadditiveCoyonedaInt_smul_eq_comp` | `((preadditiveCoyonedaInt P).obj X).isModule.smul n f = (n : End P) ≫ f`, by `rfl`. |
| `preadditiveYonedaInt_smul_eq_comp` | `((preadditiveYonedaInt P).obj (op X)).isModule.smul n h = h ≫ (n : End P)`, by `rfl`. |
| `preadditiveCoyonedaInt_smul` | `((preadditiveCoyonedaInt P).obj X).isModule.smul n f = n • f` in `P ⟶ X`. |
| `preadditiveYonedaInt_smul` | `((preadditiveYonedaInt P).obj (op X)).isModule.smul n h = n • h` in `X ⟶ P`. |
| `preadditiveCoyonedaInt_obj_isModule` | `((preadditiveCoyonedaInt P).obj X).isModule = AddCommGroup.toIntModule (P ⟶ X)`. |
| `preadditiveYonedaInt_obj_isModule` | `((preadditiveYonedaInt P).obj (op X)).isModule = AddCommGroup.toIntModule (X ⟶ P)`. |

The right-hand side `n • f` is the integer multiple (`zsmul`) in the additive
group of morphisms, i.e. ordinary repeated addition and negation. The
`_smul` laws reuse Mathlib `int_smul_eq_zsmul`. The `_obj_isModule` laws say
that the restricted `ℤ`-module structure is the canonical `ℤ`-module structure
of the Hom group. They follow from Mathlib's instance
`AddCommMonoid.subsingletonIntModule` by `Subsingleton.elim`.

## Comparison with the additive-group-valued functors

| Lean name | Statement |
| --- | --- |
| `preadditiveCoyonedaInt_comp_forget₂` | `preadditiveCoyonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} = preadditiveCoyoneda.obj (op P)`, by `rfl`. |
| `preadditiveYonedaInt_comp_forget₂` | `preadditiveYonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} = preadditiveYoneda.obj P`, by `rfl`. |
| `preadditiveCoyonedaIntCompForget₂Iso` | The natural isomorphism between the same two functors, built with `NatIso.ofComponents` from identity components `Iso.refl _`. |
| `preadditiveYonedaIntCompForget₂Iso` | The contravariant analogue. |
| `…CompForget₂Iso_hom_app_apply`, `…CompForget₂Iso_inv_app_apply` (simp) | Both components send each morphism `f` (resp. `h`) to itself. |

The functor equalities are definitional. Mathlib defines the group-valued Hom
functors as the module-valued ones followed by `forget₂`, and forgetting after
restricting scalars is definitionally the same forgetful functor. The natural
isomorphisms package the same comparison for use where an equality of
functors is inconvenient. The forgetful functor
`ModuleCat ℤ ⥤ AddCommGrpCat` is moreover an equivalence in Mathlib
(`ModuleCat.forget₂AddCommGroupIsEquivalence`). That equivalence is not used
or restated here.

## Scope

This unit contains only constructions and short intrinsic comparison laws.
None of the following is stated, proved or assumed here. They remain separate
obligations of the parent task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`:

- left exactness of the Hom functors;
- the source definitions of projective and injective objects by exactness of
  Hom, and their comparison with Mathlib's lifting definitions;
- generators, cogenerators and faithfulness criteria;
- the nonzero-Hom criterion for progenerators;
- small projectives, coproduct preservation and the finite-support
  factorization;
- the comparison with finite type;
- two-term presentations by direct sums of copies of `P`;
- the equivalence with right modules over `End P`.

No exactness interface, Grothendieck hypothesis or finite-type predicate is
imported. There are no new axioms and no unfinished proofs. The imports are
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`,
`Mathlib.CategoryTheory.Preadditive.Yoneda.Basic` and
`Mathlib.CategoryTheory.Abelian.Basic`. The last is imported only for the
example checking the abelian specialization.
