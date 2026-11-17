# Proof: the largest subtorus of a group of multiplicative type

Worker 351.

The theorem `Langlands.GroupScheme.multiplicativeTypeLargestSubtorus` proves
`Langlands.GroupScheme.MultiplicativeTypeLargestSubtorusStatement.{u}`
([statement](MultiplicativeTypeLargestSubtorusStatement.md)) in every universe `u`:

```lean
theorem multiplicativeTypeLargestSubtorus : MultiplicativeTypeLargestSubtorusStatement.{u}
```

The statement is about a group `H` of multiplicative type over a field `k`, as in Milne,
*Algebraic Groups* (2017), Notation 12.29. It has four parts: (1) `H` has a largest subtorus;
(2) a closed subtorus with a finite fppf quotient is a largest subtorus; (3) a largest
subtorus stays largest after any field extension `K` of `k`; (4) if `H` is a closed normal
subgroup of `G` (smooth and quasi-compact over `k`), then the image in `G` of a largest
subtorus of `H` is normal in `G`.

The module adds five helper theorems in the namespace
`Langlands.GroupScheme.LargestSubtorus`, described below. It uses only results already in
the Library and Mathlib. It adds no definitions and no axioms. The main theorem and the
helpers depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Route

The proof goes through the Library predicate `IsUniversalSubtorus t`
([`Torus.UniversalSubtorus`](UniversalSubtorus.md)). It says three things: `t` is a closed
subgroup, `T` is a relative torus, and after every base change every relative torus mapping
to `H` factors through `t`. The steps are:

1. A closed torus `t : T ⟶ H` whose fppf quotient `q : H ⟶ Q` is finite is a universal
   subtorus. The reason is that `Q` is killed by a nonzero integer.
2. A universal subtorus over a field is a largest subtorus. This gives parts 1 and 2.
3. A largest subtorus is a universal subtorus, because it contains the universal subtorus
   from part 1. Universal subtori are stable under base change. This gives part 3.
4. The kernel description of step 1 and an epimorphism argument with multiplication by `n`
   on `T` give part 4.

## Helper theorems

### `LargestSubtorus.exists_multiplication_eq_one_of_isFinite`

```lean
theorem exists_multiplication_eq_one_of_isFinite
    {Q : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Q.X]
    (hQ : IsMultiplicativeType Q) (hfin : IsFinite Q.X.hom) :
    ∃ n : ℤ, n ≠ 0 ∧ multiplication Q n = 1
```

A finite group `Q` of multiplicative type over a field is killed by a nonzero integer.
Here `multiplication Q n` is the Library's multiplication-by-`n` homomorphism
([`AbelianScheme.Multiplication`](../../AbelianScheme/Multiplication.md)).

Proof. By definition of `IsMultiplicativeType` there are a field extension `K` of `k`, a
finitely generated abelian group `Λ` and an isomorphism `e : Q_K ≅ D_K(Λ)`. The base change
`Q_K` is finite over `K`, and so is `D_K(Λ)`, since its structure morphism is the composite
of the inverse of `e` with the structure morphism of `Q_K`. By
`RelativeMultiplicativeType.finite_characters_of_isFinite`
([`Torus.RelativeMultiplicativeTypeFinite`](RelativeMultiplicativeTypeFinite.md)) the group
`Λ` is finite. Let `n` be its exponent; it is nonzero. By
`Diagonalizable.multiplication_exponent_eq_one`
([`Torus.DiagonalizableUniversalSubtorus`](DiagonalizableUniversalSubtorus.md)) the group
`D_K(Λ)` is killed by `n`. By `multiplication_naturality` for `e`, so is `Q_K`.

The base change of `multiplication Q n` is `multiplication Q_K n`
(`multiplication_baseChange`). The map `Spec K → Spec k` is surjective, flat and
quasi-compact (`fieldExtension_fpqc`), so the pullback functor `Over.pullback` along it is
faithful. The pullback of the unit homomorphism `1 : Q.X ⟶ Q.X` is the unit homomorphism of
`Q_K`, since `Over.pullback` preserves the monoid structure on morphisms
(`Functor.homMonoidHom`). Faithfulness then gives `multiplication Q n = 1`.

The `set_option synthInstance.maxHeartbeats 400000 in` before this theorem only raises the
instance-search budget for the unit homomorphism of `(Over.pullback b).obj Q.X`.

### `LargestSubtorus.isUniversalSubtorus_of_finiteQuotient`

```lean
theorem isUniversalSubtorus_of_finiteQuotient
    {H T Q : GroupScheme (Spec (CommRingCat.of k))} (hH : IsMultiplicativeType H)
    (t : T ⟶ H) (hT : IsTorus T) (ht : IsClosedSubgroup t)
    (q : H ⟶ Q) (hQ : IsFinite Q.X.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q) :
    IsUniversalSubtorus t
```

Let `H` be of multiplicative type, `t : T ⟶ H` a closed subgroup with `T` a torus, and
`q : H ⟶ Q` an fppf quotient with kernel `range t` and `Q` finite. Then `t` is a universal
subtorus.

Proof. The map `q` is flat, surjective and locally of finite presentation. So `Q` is of
multiplicative type by `IsMultiplicativeType.of_fppfHom`
([`Torus.MultiplicativeTypeQuotients`](MultiplicativeTypeQuotients.md)), and in particular
commutative. The previous helper gives `n ≠ 0` with `multiplication Q n = 1`. The torus `T`
is a relative torus by `IsTorus.isRelativeTorus`
([`Torus.RelativeFieldComparison`](RelativeFieldComparison.md)). The kernel clause of the
fppf quotient gives `range t = range (kernelι q)`. The Library theorem
`isUniversalSubtorus_of_kernel_torsion`
([`Torus.UniversalSubtorusKernel`](UniversalSubtorusKernel.md)) then shows that `t` is a
universal subtorus.

### `LargestSubtorus.isLargest_of_isUniversalSubtorus`

```lean
theorem isLargest_of_isUniversalSubtorus
    {H T : GroupScheme (Spec (CommRingCat.of k))} {t : T ⟶ H}
    (hu : IsUniversalSubtorus t) :
    IsTorus T ∧ IsClosedSubgroup t ∧
      ∀ (T' : GroupScheme (Spec (CommRingCat.of k))) (t' : T' ⟶ H),
        IsTorus T' → IsClosedSubgroup t' → ∃ f : T' ⟶ T, f ≫ t = t'
```

Over a field, a universal subtorus satisfies the statement's `IsLargestSubtorus`. Its torus
is a field-level torus by `RelativeTorus.IsTorus.isTorus`. Every field-level torus `T'` is a
relative torus by `IsTorus.isRelativeTorus`, so `t'` factors through `t` by
`IsUniversalSubtorus.factor` ([`Torus.UniversalSubtorusTransport`](UniversalSubtorusTransport.md)).
The closed-subgroup hypothesis on `t'` is not needed.

### `LargestSubtorus.epi_whiskerLeft`

```lean
theorem epi_whiskerLeft {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] (U : Over B) : Epi (U ◁ f)
```

Over a scheme `B`, the product `U ◁ f = 𝟙 U × f` of a flat surjective morphism with a fixed
`B`-scheme `U` is an epimorphism in `Over B`. The underlying morphism of schemes of `U ◁ f`
is a base change of `f.left`. Flat surjective morphisms are stable under base change
(`MorphismProperty.pullbackMap`), and a flat surjective morphism of schemes is an
epimorphism (Mathlib's `Flat.epi_of_flat_of_surjective`). An epimorphism on underlying
schemes is an epimorphism in `Over B` (`Over.epi_of_epi_left`).

### `LargestSubtorus.range_comp_isNormal_of_kernel_torsion`

```lean
theorem range_comp_isNormal_of_kernel_torsion
    {G H T Q : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Q.X]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) (hnorm : (SubgroupFunctor.range h).IsNormal)
    (t : T ⟶ H) (hT : IsTorus T) (q : H ⟶ Q)
    (hker : SubgroupFunctor.range t = SubgroupFunctor.range (kernelι q))
    {n : ℤ} (hn : n ≠ 0) (hQ : multiplication Q n = 1) :
    (SubgroupFunctor.range (t ≫ h)).IsNormal
```

Let `h : H ⟶ G` be a closed subgroup with normal range, and let `t : T ⟶ H` with `T` a
torus be the full kernel of `q : H ⟶ Q`, where `Q` is commutative and killed by `n ≠ 0`.
Then the range of `t ≫ h` is normal in `G`.

Proof. Since `h` is a monomorphism and its range is normal, the Library gives the
conjugation morphism `c = SubgroupFunctor.normalizedConjugation h (𝟙 G) : G.X ⊗ H.X ⟶ H.X`
([`NormalizedSubgroup`](../NormalizedSubgroup.md)). On points it satisfies
`c(g, x) ≫ h = g · (x ≫ h) · g⁻¹`. Because `h` is a monomorphism and conjugation by `g` is a
group automorphism, `c(g, xⁿ) = c(g, x)ⁿ`.

Consider `φ : G.X ⊗ T.X ⟶ Q.X`, `φ(g, y) = q(c(g, t(y)))`. Then

`φ(g, yⁿ) = q(c(g, t(y)ⁿ)) = q(c(g, t(y)))ⁿ = 1`,

since `t` and `q` are homomorphisms and `multiplication Q n = 1`. In other words,
`(G.X ◁ [n]_T) ≫ φ = 1`. By `IsTorus.flat_and_surjective_multiplication`
([`Torus.Multiplication`](Multiplication.md)) the morphism `[n]_T` is flat and surjective,
so `G.X ◁ [n]_T` is an epimorphism by `epi_whiskerLeft`. Hence `φ = 1`.

Now let `g` be a point of `G` and `y` a point of `T` over a test scheme. Then
`q(c(g, t(y))) = φ(g, y) = 1`, so `c(g, t(y))` lies in the kernel of `q`
(`mem_range_kernelι_iff`), which is `range t` by `hker`. Write `c(g, t(y)) = t(z)`. Then
`g · (t(y) ≫ h) · g⁻¹ = c(g, t(y)) ≫ h = (z ≫ t) ≫ h`. So the conjugate of the point
`y ≫ (t ≫ h)` by `g` lies in the range of `t ≫ h`.

The proof uses neither smoothness nor quasi-compactness of `G`. It does not use that `t` is
a closed subgroup either.

## Main theorem

Let `k` be a field and `H` a group of multiplicative type over `k`. The Library theorem
`IsMultiplicativeType.exists_torus_finiteQuotient`
([`Torus.MultiplicativeTypeStructure`](MultiplicativeTypeStructure.md)) gives a closed
subgroup `j₁ : T₁ ⟶ H` with `T₁` a torus and a finite fppf quotient `q : H ⟶ Q` with kernel
`range j₁`. By `isUniversalSubtorus_of_finiteQuotient`, `j₁` is a universal subtorus.

First an auxiliary claim (`huniv`): every largest subtorus `t : T ⟶ H` is a universal
subtorus. Since `t` is largest, `j₁` factors as `a ≫ t`. By `IsUniversalSubtorus.of_factor`
([`Torus.UniversalSubtorusTransport`](UniversalSubtorusTransport.md)), a closed relative
torus through which a universal subtorus factors is itself universal.

1. **Existence.** `j₁` is a largest subtorus by `isLargest_of_isUniversalSubtorus`.
2. **Finite quotient.** Given `t` with a finite fppf quotient `q'`, the subgroup `t` is a
   universal subtorus by `isUniversalSubtorus_of_finiteQuotient`, hence a largest subtorus.
3. **Base change.** A largest subtorus `t` is universal by `huniv`. Its base change along
   `Spec K → Spec k` is universal by `IsUniversalSubtorus.baseChange`, and hence largest over
   `K` by `isLargest_of_isUniversalSubtorus`.
4. **Normality.** A largest subtorus `t` is universal by `huniv`. As in step 1, `Q` is of
   multiplicative type and killed by some `n ≠ 0`. Two universal subtori of `H` have the same
   range (`IsUniversalSubtorus.range_eq`), so `range t = range j₁ = range (kernelι q)`.
   Then `range_comp_isNormal_of_kernel_torsion` gives normality of `range (t ≫ h)`.
   The hypotheses `Smooth G.X.hom` and `QuasiCompact G.X.hom` of part 4 are not used.

## Relation to the source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Notation 12.29,
p.241, defines `H_t = D(M/M_tors)` and asserts the four properties. Milne derives normality
from Proposition 1.52 and Corollary 1.87, via `H_t = (H°)_red`; that route uses smoothness
of `G`. The Lean proof does not construct `D(M/M_tors)` or `(H°)_red`. It takes the subtorus
from the Library structure theorem, and it proves normality directly from the conjugation
action and the fact that multiplication by `n` on a torus is flat and surjective. This route
is internal to the Library; it is not taken from Milne.

## Imports

- [`Torus.MultiplicativeTypeLargestSubtorusStatement`](MultiplicativeTypeLargestSubtorusStatement.md):
  the target statement.
- [`Torus.MultiplicativeTypeStructure`](MultiplicativeTypeStructure.md):
  `IsMultiplicativeType.exists_torus_finiteQuotient`.
- [`Torus.MultiplicativeTypeQuotients`](MultiplicativeTypeQuotients.md):
  `IsMultiplicativeType.of_fppfHom`.
- [`Torus.RelativeMultiplicativeTypeFinite`](RelativeMultiplicativeTypeFinite.md):
  `RelativeMultiplicativeType.finite_characters_of_isFinite`.
- [`Torus.DiagonalizableUniversalSubtorus`](DiagonalizableUniversalSubtorus.md):
  `Diagonalizable.multiplication_exponent_eq_one`, and through its imports
  `isUniversalSubtorus_of_kernel_torsion`.
- [`Torus.UniversalSubtorusTransport`](UniversalSubtorusTransport.md):
  `IsUniversalSubtorus.factor`, `.of_factor`, `.baseChange` and `.range_eq`.
- [`Torus.RelativeFieldComparison`](RelativeFieldComparison.md):
  `IsTorus.isRelativeTorus` and `RelativeTorus.IsTorus.isTorus`.
- [`Torus.Multiplication`](Multiplication.md): `IsTorus.flat_and_surjective_multiplication`.
- [`NormalizedSubgroup`](../NormalizedSubgroup.md):
  `SubgroupFunctor.normalizedConjugation` and
  `SubgroupFunctor.lift_comp_normalizedConjugation_comp`.

`multiplication`, `points_multiplication`, `multiplication_naturality`,
`multiplication_baseChange`, `kernelι`, `mem_range_kernelι_iff` and `fieldExtension_fpqc` come
in through these imports.
