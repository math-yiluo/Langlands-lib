# Statement: reflection of the central-cover universal property from a tensor decomposition

Authors: Worker 928.

`Langlands.GroupScheme.CentralCoverUniversalPropertyTensorReflectionStatement.{u}`
is a proposition definition, not a theorem. It states the reflection; it
neither proves it nor constructs a tensor equivalence, a covering group or a
covering map.

## Exact statement

All data are quantified inside the proposition, so its only parameter is the
universe level `u`. For

- fields `k K : Type u` in one arbitrary universe, with an arbitrary
  `Algebra k K`;
- actual group schemes `C G : GroupScheme (Spec (CommRingCat.of k))` and an
  actual homomorphism `π : C ⟶ G`;
- an index type `I : Type` with `[Finite I]`;
- an actual `K`-algebra equivalence `e : (K ⊗[k] K) ≃ₐ[K] (I → K)`;
- a family of actual `k`-algebra automorphisms `s : I → (K ≃ₐ[k] K)`,

the proposition says: if

```
∀ (a b : K) (i : I), e (a ⊗ₜ[k] b) i = a * s i b
```

then

```
HasCentralCoverUniversalProperty
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map π) →
  HasCentralCoverUniversalProperty π.
```

The pure-tensor formula is a hypothesis, and so is the universal property
after scalar extension. The conclusion is the universal property of `π`
itself over `k`.

## The supplied decomposition

- **Source.** `K ⊗[k] K` is a `K`-algebra through its **first** tensor factor.
  This is Mathlib's default instance `Algebra.TensorProduct.leftAlgebra`, so
  `c • (a ⊗ₜ b) = (c * a) ⊗ₜ b`.
- **Target.** `I → K` has the pointwise ring operations and the instance
  `Pi.algebra`, whose structure map sends `c` to the constant function.
- **The two coordinate maps.** Putting `b = 1` gives `e (a ⊗ₜ 1) i = a`, and
  putting `a = 1` gives `e (1 ⊗ₜ b) i = s i b`. So on the factor indexed by
  `i`, the first coordinate map `a ↦ a ⊗ₜ 1` becomes the identity of `K` and
  the second, `b ↦ 1 ⊗ₜ b`, becomes the automorphism `s i`. Pure tensors
  span `K ⊗[k] K` additively, so the formula determines `e` from `s`.

On spectra, `Spec (K ⊗[k] K)` is the double overlap
`Spec K ×_{Spec k} Spec K` of the cover `Spec K ⟶ Spec k`. The equivalence
writes it as a finite disjoint union of copies of `Spec K`. The two
projections restrict on the `i`-th copy to the identity and to `Spec` of
`s i`, which are both isomorphisms. The statement supplies only the algebra
data; this scheme-level reading is how a proof uses it.

**No separate premise on `K/k`.** The statement assumes no finiteness,
algebraicity, Galois, separability, perfection or characteristic condition
on the extension. The decomposition already forces strong conditions, by the
following derived argument (not part of the Lean statement):

1. With the first-factor structure, `K ⊗[k] K` is the base change of the
   `k`-vector space `K`, so its `K`-dimension is `[K : k]`. The target has
   `K`-dimension `#I`. Since `e` is `K`-linear and bijective and `I` is
   finite, `[K : k] = #I` is finite. As `K` is a field, `I` is nonempty.
2. If `s i = s j` with `i ≠ j`, the formula gives `e x i = e x j` on pure
   tensors, hence on all `x`. This contradicts surjectivity of `e`. So `s` is
   injective, and `K` has at least `[K : k]` automorphisms over `k`.
3. A finite extension has at most `[K : k]` automorphisms (Dedekind–Artin
   independence of characters). So equality holds: `K/k` is finite Galois,
   and `s` is a bijection from `I` onto `Gal(K/k)`
   (Mathlib: `IsGalois.of_card_aut_eq_finrank`).

So the hypotheses do not describe an arbitrary field extension. They describe
a finite Galois extension with its Galois group explicitly enumerated. The
statement does **not** assert reflection of the universal property along
unrestricted field extensions. It also does not assert that a decomposition
exists. For finite Galois extensions that is the separate published
statement `Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement`,
which this module does not import.

## The base change and the predicates

The base map is the actual scheme morphism

`p = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k`,

written inline. It is the same map as the Library abbreviation
`Langlands.GroupScheme.Descent.fieldMap k K`. The functor is the published
`GroupScheme.baseChange p = (Over.pullback p).mapGrp`. So
`(GroupScheme.baseChange p).map π : C_K ⟶ G_K` is the pulled-back actual
homomorphism between the fibre products `C ×_{Spec k} Spec K` and
`G ×_{Spec k} Spec K`. No other model of base change is used.

All predicates are the published ones from
`Langlands.GroupScheme.SimplyConnected.Basic` and its imports, unchanged.

- `HasCentralCoverUniversalProperty π` means: for every actual group scheme
  `H` over `Spec k` and every actual homomorphism `q : H ⟶ G` with
  `IsSemisimple H` and `IsCentralIsogeny q`, there is exactly one actual
  homomorphism `a : C ⟶ H` with `a ≫ q = π`. The hypothesis is the same
  property over `K` for `π_K`. There, `H` ranges over all semisimple
  `K`-groups with a central isogeny onto `G_K`, not only base changes of
  `k`-groups.
- `IsSemisimple H` means `H` is connected reductive and has finite centre:
  some actual closed subgroup `z : Z ⟶ H` has range equal to the full
  scheme-theoretic centre functor, and `Z` is finite over the base. The
  centre is tested on all schemes over the base, including nonreduced ones,
  so the representative keeps its nilpotents.
- `IsCentralIsogeny q` means `q` is finite, flat and surjective, with
  locally finitely presented underlying morphism, and its actual kernel
  inclusion `kernelι q` is central. The kernel is the full scheme-theoretic
  pullback of `q` along the unit section. Centrality is tested on every
  test scheme, including nonreduced ones. So non-smooth kernels such as
  `μ_p` in characteristic `p` count, and no reduced or smooth kernel is
  substituted.

No simple-connectedness, semisimplicity or central-isogeny hypothesis is put
on `C`, `G` or `π`. The implication needs none: only the universal property
over `K` and the decomposition are assumed. No semisimplicity-ascent
theorem, effective-descent theorem, compatible factorization or universal
property over `k` is taken as extra data. Those are proof obligations.

## Why the implication holds (derived content)

This explains the intended proof route. It is not a Lean proof, and no
proof is supplied with this statement. The route follows Worker 1347's
compiled, unreviewed prototype
`Langlands.GroupScheme.HasCentralCoverUniversalProperty.of_tensorDecomposition`.
A development check (`lean_check` diagnostic
`c0829d06-df2b-451a-8a55-d393f6d8c967`) closes this exact proposition with
that theorem, using only `propext`, `Classical.choice` and `Quot.sound`. This
is evidence of feasibility, not proof acceptance.

1. *Finiteness.* `e` makes `K ⊗[k] K` finite as a `K`-module. Since `K` is
   faithfully flat over `k`, `K` is finite over `k`
   (`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`), hence
   algebraic.
2. *Field components.* The Library interface
   `Langlands.GroupScheme.Descent.tensorComponent` turns `e` into a finite
   coproduct decomposition of the actual double overlap. On each component
   the first projection is the identity, and by the pure-tensor formula the
   second is the isomorphism `Spec` of `s i`.
3. *Factorization over `K`.* Let `q : H ⟶ G` be a central isogeny from a
   semisimple `k`-group. Semisimplicity ascends along the algebraic extension
   `K/k`, and central isogenies are stable under actual base change. So the
   universal property over `K` gives a unique `a_K : C_K ⟶ H_K` with
   `a_K ≫ q_K = π_K`.
4. *Compatibility.* On each field component, the universal property over `K`
   is transported along the component isomorphisms. Its uniqueness makes the
   two pullbacks of `a_K` to the double overlap agree on that component.
   Equality on a finite coproduct is detected componentwise, so the two
   pullbacks agree on the whole overlap. No universal property over a field is
   applied directly to the overlap, which is in general not a field.
5. *Descent.* The published fpqc descent of homomorphisms
   (`Langlands.GroupScheme.Descent.FpqcHomDescent.hom`) descends `a_K` to some
   `a : C ⟶ H` with base change `a_K`. Base change along `Spec K ⟶ Spec k` is
   faithful, so `a ≫ q = π`, and any other factorization equals `a`.

Classically, this is Galois descent of morphisms. For each `σ` in the Galois
group, the `σ`-twist of `a_K` is again a factorization of `π_K` through
`q_K`, so by uniqueness it equals `a_K`. Hence `a_K` is defined over `k`.

## Provenance

This is an internal, derived statement; no original-source tuple is cited.
Worker 1347's task `e53cfe57-9d09-4417-846a-b6d415597a95` specifies the
exact formulation: the supplied finite tensor decomposition with
automorphism coordinates, the actual base-change functor, and the existing
universal-property predicate. It is requested as a prerequisite of
arbitrary-field simply connected cover existence
(task `a41119fb-a633-4b81-a979-4b08e9ddbb15`) and of Worker 416's covering
datum assembly (task `b962f329-c6a7-4ca2-b95b-3aadf1f90690`). The underlying
principle, Galois descent of morphisms combined with uniqueness of the
factorization, is classical. This Markdown does not claim that any source
states this exact formulation.

## Scope

- Universe `u`, both fields and the algebra structure are arbitrary. This
  includes imperfect fields and positive characteristic.
- Only the direction from `K` to `k` is stated. The separate published
  `IsSimplyConnectedCoverFieldExtensionStatement` states the opposite
  direction, but only for whole simply connected covers, universal property
  included.
- The statement does not prove simple-connectedness reflection, existence of
  a tensor decomposition, or existence of simply connected covers. The
  published `Langlands.GroupScheme.SimplyConnectedCoverExistenceStatement`
  pair is neither imported nor changed.
- The proof is a separate exact-target obligation.

## Imports

- `Langlands.GroupScheme.SimplyConnected.Basic`: `HasCentralCoverUniversalProperty`,
  and through its imports `IsSemisimple`, `IsCentralIsogeny`, `GroupScheme`
  and `GroupScheme.baseChange`.
- `Mathlib.Algebra.Algebra.Pi`: the algebra structure on `I → K`.
- `Mathlib.RingTheory.TensorProduct.Basic`: the algebra tensor product and
  its left algebra structure.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, which pins Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
