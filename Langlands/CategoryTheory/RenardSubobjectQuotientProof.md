# Renard A.VI.2(2–3): proof of the subobject–quotient correspondence and binary lattice laws

This module proves the published statement
`Langlands.Renard.SubobjectQuotientAndLatticeStatement` from
`Langlands.CategoryTheory.RenardSubobjectQuotientStatements`. It imports that
statement module by name and leaves it, its Markdown and its imports unchanged.

## Exported theorem

```text
theorem Langlands.Renard.subobjectQuotientAndLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] :
    SubobjectQuotientAndLatticeStatement C
```

The object universe `u` and the Hom universe `v` are independent. The only
hypothesis on `C` is `Abelian C`. The theorem adds no `WellPowered`,
`LocallySmall`, Grothendieck, module, finite-length, chosen-factorization or
smallness hypothesis. The axioms used are the standard `propext`,
`Classical.choice` and `Quot.sound`.

## Source and what this proof adds

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). It is
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.I.2 (printed p. 248, PDF p. 254) defines subobjects `S_X`, quotients `Q_X`,
their orders, and binary intersection and union as a greatest lower bound and a
least upper bound in `S_X`. A.VI.2 (printed p. 262, PDF p. 268) lists, as
consequences of the axioms of A.VI.1 (printed p. 261, PDF p. 267):

- (2) `coker : S_A → Q_A` and `ker : Q_A → S_A` are mutually inverse and
  reverse the orders;
- (3) any two subobjects have an intersection and a union.

The source states these without proof. The Lean proof below does not follow a
source argument. It reuses the pinned Mathlib order isomorphism
`CategoryTheory.Abelian.subobjectIsoSubobjectOp` and the existing lattice
structure on `Subobject X`. The supplementary 2010-edition errata
(`renard-2010-corrections-complements`, PDF pp. 18–19) do not change these two
assertions.

## The proof

The proof first splits the target into its two components. For each object `X`,
it then supplies the six correspondence clauses.

### The order isomorphism

Fix `X : C` and let

```text
e := Abelian.subobjectIsoSubobjectOp X : Subobject X ≃o (Subobject (op X))ᵒᵈ.
```

Mathlib defines `e` as
`OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) _ _`. The forward
function of `e` is therefore `cokernelOrderHom X` by definition, and the forward
function of `e.symm` is `kernelOrderHom X`. The two inverse identities that
`ofHomInv` needs are proved in Mathlib by the kernel and cokernel universal
properties. Every mono `f` is identified with `kernel.ι (cokernel.π f)` using
`Abelian.monoLift`, and every epi with `cokernel.π (kernel.ι _)` using
`Abelian.epiDesc`. These are the uses of the abelian structure.

### Clauses 1 and 2: the inverse laws

- Clause 1, `kernelOrderHom X (cokernelOrderHom X P) = P`, is
  `e.symm_apply_apply P`.
- Clause 2, `cokernelOrderHom X (kernelOrderHom X (toDual K)) = toDual K` for a
  source quotient class `K : Subobject (op X)`, is
  `e.apply_symm_apply (toDual K)`.

Each holds by definitional unfolding of `e` and `e.symm`.

### Clauses 3 and 4: the two order reversals

The source quotient collection is `Subobject (op X)` with its own subobject
order. For epis `p₁ : X ⟶ Y₁` and `p₂ : X ⟶ Y₂`, the class of `p₁` is at most
the class of `p₂` exactly when `p₂ ≫ b = p₁` for some `b : Y₂ ⟶ Y₁`. This is
Renard's quotient order. The codomain of `cokernelOrderHom X` is the order dual
`(Subobject (op X))ᵒᵈ`. In the dual, `a ≤ b` means `ofDual b ≤ ofDual a` in the
source order.

- Clause 3. `OrderIso.le_iff_le` gives `e P ≤ e Q ↔ P ≤ Q`. In the dual, the
  left side is by definition
  `ofDual (cokernelOrderHom X Q) ≤ ofDual (cokernelOrderHom X P)`. The proof uses
  `(e.le_iff_le (x := P) (y := Q)).symm`. Monotonicity into the order dual is
  thus exactly reversal of the source orders, in both directions.
- Clause 4. The same lemma for `e.symm`, at `x := toDual L` and `y := toDual K`,
  gives
  `kernelOrderHom X (toDual L) ≤ kernelOrderHom X (toDual K) ↔ toDual L ≤ toDual K`.
  The right side is by definition `K ≤ L` in the source quotient order. Its
  symmetric form is the clause.

### Clauses 5 and 6: the representative formulas

Mathlib defines `cokernelOrderHom X` as `Subobject.lift` of
`fun f => Subobject.mk (cokernel.π f).op`, and `kernelOrderHom X` as
`Subobject.lift` of `fun f => Subobject.mk (kernel.ι f.unop)`. `Subobject` is a
quotient type and `Subobject.mk` is its quotient map. So `Subobject.lift F h`
applied to `Subobject.mk f` reduces definitionally to `F f`, which is the content
of `Subobject.lift_mk`. Both clauses are therefore closed by `rfl`:

- Clause 5. For a mono `i : Y ⟶ X`, `cokernelOrderHom X (Subobject.mk i)`
  reduces to `Subobject.mk (cokernel.π i).op`. As an element of the order dual,
  this is `toDual (Subobject.mk (cokernel.π i).op)`.
- Clause 6. For an epi `p : X ⟶ Y`, the class `Subobject.mk p.op` uses the
  `Mono p.op` instance derived from `Epi p`.
  `kernelOrderHom X (toDual (Subobject.mk p.op))` reduces to
  `Subobject.mk (kernel.ι p.op.unop)`, and `p.op.unop` is `p` by definition.

These are equalities of subobject classes. They make no claim that chosen kernel
or cokernel objects are literally equal. `cokernel.π i` and `kernel.ι p` are the
actual categorical cokernel and kernel maps.

### The binary lattice laws

For `P Q R : Subobject X`, the two laws are the generic semilattice facts
`le_inf_iff` (`R ≤ P ⊓ Q ↔ R ≤ P ∧ R ≤ Q`) and `sup_le_iff`
(`P ⊔ Q ≤ R ↔ P ≤ R ∧ Q ≤ R`). They are applied to the existing
`Lattice (Subobject X)` instance. That instance needs `HasPullbacks`, `HasImages`
and `HasBinaryCoproducts`, which the abelian structure provides. Its fields come
from Mathlib's categorical constructions:

- The infimum descends `MonoOver.inf`: pull back one representative along the
  other, then compose into `X`. Its `le_inf` field is `MonoOver.leInf`, which is
  the pullback universal property (`pullback.lift`).
- The supremum descends `MonoOver.sup`, the image of the coproduct map
  `coprod.desc i j` into `X`. Its `sup_le` field is `MonoOver.supLe`, which is
  the minimality of the image (`image.lift`) applied to `coprod.desc` of the two
  factorizations.

Thus the actual `P ⊓ Q` and `P ⊔ Q` are a greatest lower bound and a least upper
bound of `P` and `Q`, as A.I.2 requires and A.VI.2(3) asserts. As the target
requests, the proof adds no further lemmas identifying these constructions.

## Scope

This proves only A.VI.2(2–3) as stated by the imported target. It does not
cover the passage from Renard's AB0–AB3* axioms to Mathlib's `Abelian`
structure, images and coimages, A.VI.2(4–8), arbitrary meets and joins, or the
well-powered opposite-category instance. Those keep their existing scopes and
owners.
