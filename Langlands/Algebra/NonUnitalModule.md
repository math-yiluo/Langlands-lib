# Nonunital modules and their nondegenerate part

## Source, hypotheses and correspondence

This unit implements the module conventions and the nondegenerate-part construction in David Renard, *Représentations des groupes réductifs p-adiques*, French version dated **9 July 2026**, Chapter I conventions and I.1.2, printed pages 5–8 / PDF pages 11–14. The registered original is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. The title and cited pages were read directly. No project errata entry was present when this unit was prepared. The available registered corrections to the 2010 edition were also consulted; they supplied no correction to these constructions and do not replace the 2026 original.

All declarations are in `Langlands.Algebra`. The scalar type `A : Type u` has an associative `NonUnitalRing` structure; the carrier `M : Type v` has an `AddCommGroup` structure. The universes `u` and `v` are independent. Homomorphisms can also have source and target carriers in independent universes. Neither commutativity, nontriviality, a scalar field, topology nor finite dimension is assumed. Where the ring has a unit, the ambient action still has no unit law.

The module imports the published `Langlands.Algebra.IdempotentedRing` by its Lean name. In particular, `Idempotent A` is its dedicated structure of actual ambient idempotents, and its order is inclusion of corners. The finite-local-unit predicate `IsIdempotented A` is imported without alteration.

| Original passage | Implemented declarations and scope |
| --- | --- |
| Chapter I conventions, printed pp. 5–6 / PDF pp. 11–12: left and right module notation; rings and their modules need not be unital | `NonUnitalModule`, `NonUnitalModuleHom`, `NonUnitalModuleCat`; right modules use the opposite ring |
| Conventions, printed p. 6 / PDF p. 12: a unital module is an action on which the ring unit acts as identity | `IsUnitalModule`, named `NonUnitalModule.ofModule` and `toModule` adapters |
| I.1.1 lemma (ii), printed p. 6 / PDF p. 12: absorption when one idempotent is below another | Derived module analogue `Idempotent.smul_eq_of_le`, using the imported order |
| I.1.2 module definition and Remark 1, printed p. 7 / PDF p. 13 | `IsNondegenerate`, `exists_idempotent_smul_eq_iff_one_smul_eq`, `isNondegenerate_iff_isUnitalModule` |
| I.1.2, printed p. 7 / PDF p. 13: largest nondegenerate submodule and union of the images `eM` | `nondegeneratePart`, its membership and image-union criteria, `nondegeneratePart_isNondegenerate`, `le_nondegeneratePart_iff` |
| I.1.2, printed p. 7 / PDF p. 13: the full subcategory of nondegenerate modules and the right-module convention | `NondegenerateModuleCat`, `nondegenerateInclusion`, and their right-module specializations |
| First two sentences of the proposition's proof, printed p. 8 / PDF p. 14: intertwiners preserve the part, so restriction defines the functor | `map_mem_nondegeneratePart`, `restrictNondegeneratePart`, `nondegeneratePartFunctor`; the proposition's exactness assertion is deferred |

The explicit endomorphism-ring equivalence, stable-subgroup interface, category and functor law proofs, natural inclusion, and opposite-ring local-unit lemma are derived implementation content. They realize the cited actions and constructions rather than additional assertions attributed verbatim to Renard.

## Ambient actions and the endomorphism description

`NonUnitalModule A M` extends Mathlib's `DistribSMul A M` and `SemigroupAction A M`, and adds distributivity in the scalar and the scalar-zero law. Thus its action satisfies

```text
a • 0 = 0
a • (m + n) = a • m + a • n
(a * b) • m = a • (b • m)
(a + b) • m = a • m + b • m
0 • m = 0.
```

There is no axiom concerning `1 • m`. The instance `NonUnitalModule.actionSMul` exposes this specified action with priority 1200. This matters when the same underlying carrier types already have another canonical scalar action: for example, the specified zero action of `ℤ` on `ℤ` must remain the action in module formulas.

`NonUnitalModule.toEndHom` constructs an actual nonunital ring homomorphism

```text
A →ₙ+* AddMonoid.End M.
```

Each scalar acts by an additive endomorphism. The scalar-zero and scalar-addition laws prove preservation of zero and addition; associativity proves preservation of multiplication, which is composition of endomorphisms. Conversely, `ofEndHom` evaluates such a homomorphism on vectors and obtains each action law by evaluating its corresponding homomorphism law. `equivEndHom` proves that these constructions are inverse: extensionality gives equality of homomorphisms, and structure decomposition gives equality of action structures. This is a checked equivalence with the ordinary nonunital endomorphism-ring description. No unitization is introduced or needed.

`ofModule` explicitly converts an ordinary unital `Module R M` to an ambient action by retaining its action laws. It is a named adapter, not a global instance requiring ambient actions to be unital. Conversely, `toModule` constructs an actual `Module R M` once supplied with the missing law `∀ m, (1 : R) • m = m`. `NonUnitalModule.zero` constructs the zero action on any abelian group, including a nonzero group over a unital ring.

## Actual morphisms, category and submodules

`NonUnitalModuleHom A M N` extends the actual additive homomorphism type `M →+ N` with the intertwining equation `f (a • m) = a • f m`. It coerces to a function; `map_zero`, `map_add`, and `map_smul` expose its laws. Its extensionality theorem reduces equality to equality on all vectors.

`NonUnitalModuleHom.id` is the identity additive homomorphism. `comp g f` is composition of the underlying additive homomorphisms; applying the two intertwining equations proves that it intertwines. `id_apply` and `comp_apply` give their elementwise behavior.

`NonUnitalModuleCat.{u, v} A` bundles a carrier in `Type v`, its additive commutative group, and its specified ambient action. `of` bundles an existing action. The actual `Category` instance has the above intertwiners as its morphisms, identity as its identity morphism, and their composition as categorical composition. Both identity laws and associativity follow by extensionality and evaluation; they are proved fields of this instance.

`NonUnitalSubmodule A M` is an actual `AddSubgroup M` stable under every scalar. Its `SetLike` structure and partial order use its underlying set and inclusion. Every such subgroup inherits an additive commutative group and a `NonUnitalModule A S` structure. Scalar multiplication acts on underlying elements; closure supplies its membership proof. Each action law follows from the ambient law by subtype extensionality. `subtype S` and `inclusion h` are actual additive intertwiners into the ambient module and between included submodules, respectively.

## Nondegeneracy and the unital comparison

`IsNondegenerate A M : Prop` means exactly

```text
∀ m : M, ∃ e : Idempotent A, (e : A) • m = m.
```

This predicate itself makes sense over any nonunital ring; the construction of the largest such submodule below assumes `IsIdempotented A`. A witness is an actual ring element with its idempotence proof.

`IsUnitalModule R M : Prop` means `∀ m, (1 : R) • m = m`, for an ambient action of a unital ring. At each vector, `exists_idempotent_smul_eq_iff_one_smul_eq` proves that having an idempotent fixer is equivalent to being fixed by `1`. If `e • m = m`, then

```text
1 • m = 1 • (e • m) = (1 * e) • m = m.
```

Conversely, the actual idempotent `1` supplies the witness. Quantifying this equivalence proves `isNondegenerate_iff_isUnitalModule`, exactly the module assertion of I.1.2 Remark 1. In conjunction with the named adapters, it identifies these ambient nondegenerate actions with ordinary unital module structures on the same action; no equivalence of bundled categories is asserted here.

`nondegenerateProperty A` is this predicate as a `CategoryTheory.ObjectProperty` on the ambient category. `NondegenerateModuleCat` is its actual Mathlib `FullSubcategory`; `nondegenerateInclusion` is its actual inclusion functor. Fullness and faithfulness are supplied by Mathlib's full-subcategory construction. No categorical abelianness follows merely from this definition.

## The largest nondegenerate submodule

For `hA : IsIdempotented A`, `nondegeneratePart hA M` has underlying set

```text
{m : M | ∃ e : Idempotent A, (e : A) • m = m}.
```

Its additive and scalar closure are constructed, not additional hypotheses. Zero is fixed by the zero idempotent. If `e` fixes `m` and `f` fixes `n`, the imported `hA.finite_upper_bound {e, f}` gives an idempotent `g` above both. The derived lemma `Idempotent.smul_eq_of_le` says that `e ≤ g` and `e • m = m` imply `g • m = m`: substitute `e • m` and use the imported absorption identity `g * e = e`. Thus distributivity makes `g` fix `m + n`. A fixer of `m` also fixes `-m` by `smul_neg`.

For scalar closure, choose `e` such that `a ∈ e.corner` using `hA.exists_mem_corner a`. Then `e * a = a`, so `e • (a • m) = a • m` by action associativity. This argument works for any `m`, even without a prior membership witness. It uses only the singleton local-unit consequence of `hA`.

`mem_nondegeneratePart` unfolds its exact defining predicate. `mem_nondegeneratePart_iff_exists_smul` proves the set-theoretic union formula in membership form:

```text
m ∈ nondegeneratePart hA M ↔
  ∃ (e : Idempotent A) (n : M), (e : A) • n = m.
```

A fixed vector is its own image witness. Conversely, the vector `e • n` is fixed by `e` because `e * e = e`. This is an equality with a union of images as sets; no categorical colimit is claimed.

`nondegeneratePart_isNondegenerate` retains each element's membership witness as its fixer in the inherited action, using subtype extensionality. `le_nondegeneratePart_iff hA S` proves the exact maximality criterion

```text
S ≤ nondegeneratePart hA M ↔ IsNondegenerate A S.
```

In the forward direction, inclusion gives an ambient fixer for each element of `S`, which also fixes it in the inherited action. In the reverse direction, forget the subtype from a fixer in `S` to obtain the membership witness in the part. Consequently the constructed part is itself nondegenerate and contains every nondegenerate submodule. The map `NonUnitalSubmodule.inclusion` realizes any such containment by an actual intertwiner.

For a unital ring, `mem_nondegeneratePart_iff_one_smul_eq` specializes the vectorwise comparison using the imported `IsIdempotented.of_ring`: the part consists exactly of vectors fixed by the ring's unit, even when the original action is not unital.

## Restriction, functor and natural inclusion

`NonUnitalModuleHom.map_mem_nondegeneratePart` uses the same fixing idempotent for the image of a vector. If `e • m = m`, intertwining gives `e • f m = f (e • m) = f m`. `restrictNondegeneratePart hA f` therefore constructs an actual intertwiner between the two inherited submodules. Its additive and scalar laws are the laws of `f` lifted by subtype extensionality. The application lemma shows that its underlying value is exactly `f m`.

`restrictNondegeneratePart_id` and `restrictNondegeneratePart_comp` prove equality of actual intertwiners by evaluation and extensionality. These supply the intrinsic laws of `nondegeneratePartFunctor hA`, whose type is

```text
NonUnitalModuleCat.{u, v} A ⥤ NondegenerateModuleCat.{u, v} A.
```

On objects it bundles the constructed submodule and its proved nondegeneracy. On morphisms it bundles the actual restriction as a morphism in the full subcategory. Its identity and composition fields use the proved restriction equalities and Mathlib's full-subcategory homomorphism extensionality.

`nondegeneratePartInclusion hA` is a natural transformation from this functor followed by the full inclusion to the identity functor on all ambient modules. Its component is the actual submodule inclusion. Naturality is proved by evaluating either composite at a vector: both produce its image under the original ambient morphism.

These are constructions and their intrinsic laws. The exactness proposition on printed p. 8 / PDF p. 14 requires a separate proof about exact sequences.

## Right modules and remaining obligations

`IsIdempotented.op` proves the finite-local-unit property for `Aᵐᵒᵖ`. It applies `hA` to the finite image of the opposite elements under `unop`, chooses that idempotent, and takes its opposite. Opposite multiplication and associativity transport both its idempotence and the sandwich equations.

`RightNonUnitalModule A M` means `NonUnitalModule Aᵐᵒᵖ M`. `RightNonUnitalModuleCat`, `IsRightNondegenerate`, and `RightNondegenerateModuleCat` are the corresponding ambient category, predicate, and full subcategory over the opposite ring. `rightNondegeneratePartFunctor hA` is precisely `nondegeneratePartFunctor hA.op`, so the same construction and laws apply. A right action written `m · a` is represented by `MulOpposite.op a • m`; `right_mul_smul` verifies the order convention

```text
op (a * b) • m = op b • (op a • m).
```

The elementary decomposition from the conventions on printed p. 6 / PDF p. 12, `M = eM ⊕ ker(m ↦ e • m)`, and the actual unital action of the corner `eAe` on `eM` remain separate successor obligations. The source's notation `(1-e)M` means the image of `m ↦ m - e • m`; its `1` does not require an ambient ring unit.

Also deferred are the exactness proposition, categorical abelianness and quotient constructions, categorical colimit universal properties, cofinal or relatively directed idempotent systems, completion and adjunctions. They remain obligations of the surrounding Renard development. This unit provides their ambient categories and nondegenerate-part functor without claiming these further results.
