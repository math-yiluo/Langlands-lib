# Globalization of a cyclic extension of local fields

`Langlands.TraceFormula.CyclicFieldGlobalizationStatement` is a proposition about realizing a
cyclic extension of characteristic-zero local fields as the completion of a cyclic extension
of number fields. Its auxiliary proposition `Langlands.TraceFormula.IsCyclicShiftSplit`
records the splitting together with the action of a chosen generator.

## Notation and hypotheses

- The base `F : Type u` has `[Field F]`, `[ValuativeRel F]`, `[TopologicalSpace F]`,
  `[IsNonarchimedeanLocalField F]` and `[CharZero F]`. Mathlib's local-field class specifies a
  locally compact valuative topology for a nontrivial valuative relation.
- The extension `E : Type v` has `[CommRing E]`, `[Algebra F E]`, `[TopologicalSpace E]`,
  `[IsTopologicalRing E]` and `[IsModuleTopology F E]`. Its topology is the module topology
  over `F`. The types, instances, automorphism `σ : E ≃ₐ[F] E` and degree `l : ℕ` use the
  interface of `Langlands.BaseChange.RegularTransferStatement`.
- `Langlands.BaseChange.IsCyclicAlgebra σ l` says that `E` is a finite reduced `F`-algebra of
  dimension `l`, that `σ` has order `l` and that its fixed elements lie in the image of `F`.
  The additional hypothesis `IsField E` makes `E/F` a cyclic Galois field extension generated
  by `σ`. It ensures that the local target is a single field completion and permits the use
  of the Library's field-realization theorem. In the prime-degree base change application,
  the other cyclic algebra case is a split product of copies of `F`, which is handled by split
  local computations.
- For a number field `K`, `𝓞 K` is its ring of integers. A finite place is a member of
  `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, with prime ideal `v.asIdeal`, completion
  `K_v := v.adicCompletion K` and residue-field cardinality `Ideal.absNorm v.asIdeal`.
  The completion at `w : NumberField.InfinitePlace K` is `w.Completion`.

## Splitting with the cyclic shift

For fields `K` and `L` with `[Algebra K L]`, a commutative `K`-algebra `A`, an automorphism
`σ : L ≃ₐ[K] L` and `l : ℕ`, `IsCyclicShiftSplit K L A σ l` asks for an `A`-algebra
isomorphism `e : A ⊗[K] L ≃ₐ[A] (Fin l → A)` satisfying

    e ((id ⊗ σ) y) = fun i => e y (finRotate l i)

for every `y : A ⊗[K] L`. Here `id ⊗ σ` is `Algebra.TensorProduct.congr AlgEquiv.refl σ`
with the identity on the first factor. Mathlib's `finRotate l` sends `i` to `i + 1` modulo
`l`. The action on the product is precomposition by this rotation.

## Globalization statement

`CyclicFieldGlobalizationStatement.{u, v}` quantifies over the local data above with
`IsCyclicAlgebra σ l` and `IsField E`. It asks for `K L : Type` with `Field` and `NumberField`
structures, `Algebra K L` and `σK : L ≃ₐ[K] L` satisfying all five clauses.

1. `IsCyclicAlgebra σK l` makes `L/K` cyclic Galois of degree `l` with generator `σK`.
2. For every infinite place `w` of `K`, `IsCyclicShiftSplit K L w.Completion σK l` holds.
3. There are a finite place `v₀` of `K` and ring isomorphisms `φ : K_{v₀} ≃+* F` and
   `ψ : K_{v₀} ⊗[K] L ≃+* E` with the following properties.
   - Both `φ` and `φ.symm` are continuous.
   - For every `a : K_{v₀}`, `ψ (a ⊗ₜ[K] (1 : L)) = algebraMap F E (φ a)`.
   - For every `y : K_{v₀} ⊗[K] L`, `ψ ((id ⊗ σK) y) = σ (ψ y)`.
   - Both `ψ` and `ψ.symm` are continuous when the tensor product carries
     `moduleTopology (K_{v₀}) (K_{v₀} ⊗[K] L)`.
4. For every `S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))` and every `N : ℕ`,
   there is a finite place `v ∉ S` with `N ≤ Ideal.absNorm v.asIdeal` and
   `IsCyclicShiftSplit K L (v.adicCompletion K) σK l`.
5. For every such `S` and `N`, there is a finite place `v ∉ S` with
   `N ≤ Ideal.absNorm v.asIdeal` whose extended ideal
   `Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal` is prime. This means that `v` is unramified
   with a single prime above it of residue degree `l`.

In clause 3, the comparison with the field `E` makes the completed tensor product a field.
By completed tensor decomposition, there is a unique place of `L` over `v₀`, and its completion
is identified with `E`. The place `v₀` may be ramified. In clauses 4 and 5, enlarging `S` after
each choice gives distinct auxiliary places as needed.

## Sources and scope

Arthur and Clozel (1989), *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Chapter 1, §6.3, printed pp. 54–55 (PDF pp. 68–69), take a cyclic global extension
realizing the local extension at `v₀`, two split places and an inert place distinct from `v₀`.
They also take every infinite place to split. The inert place is used to distinguish the twists
in the discrete case. Registered source `arthur-clozel-1989-base-change`.
[Arthur–Clozel, §6.3](https://www.math.toronto.edu/arthur/pdf/30.pdf)

Henniart and Lemaire (2011), *Changement de base et induction automorphe pour GLn en
caractéristique non nulle*, use the corresponding function-field setup in §II.6.1, printed
p. 118 (PDF p. 126). In §II.6.7, printed p. 123 (PDF p. 131), they choose a split finite place
whose residue field has cardinality at least `3`. Registered source
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
[Henniart–Lemaire, §II.6.7](https://www.numdam.org/item/10.24033/msmf.436.pdf)

The project formulates a single derived number-field assertion for any degree `l`. It specifies
equivariant topological comparisons at `v₀` and the cyclic-coordinate action at split places.
Its two avoidance and norm conditions let a consumer choose the auxiliary places used in the
sources, including a split place with norm at least `3`. The local universes `u` and `v` are
independent, and the global witnesses use `Type` as in the Library's realization theorem.

## Proposed proof route

1. Construct compatible finite-extension structures over `Padic p` on `F` and `E`, with `p`
   the residue characteristic of `F`. The closure of the rational subfield in `F` gives the
   copy of `ℚ_p`. The bridge must supply the scalar tower and identify the given topologies
   with `Langlands.PadicField.canonicalTopology`. This is a prerequisite to applying the
   Library realization stated for `Langlands.PadicField`.
2. Apply `Langlands.Global.totallyRealGaloisRealization` to the resulting finite Galois
   extension. It supplies totally real `K` and `L`, a single `w₀` above `v₀`, topological
   comparisons with `F` and `E`, and a compatible group isomorphism
   `θ : Gal(L/K) ≃* Gal(E/F)`. Choosing `σK = θ.symm σ` gives the generator of the required
   degree. Use `Langlands.Global.AdelicFunctoriality.completedTensorComparison` and the
   unique place above `v₀` to identify `K_{v₀} ⊗[K] L` with `L_{w₀}`. The comparison on the
   dense embeddings of `K` and `L` gives scalar and generator compatibility after completion.
   The two module topologies give continuity of the semilinear comparison and its inverse.
3. Total reality of `L` gives complete splitting at the infinite places. Over a splitting
   field `A`, the `l` algebra maps `A ⊗[K] L → A` form a torsor under precomposition by
   powers of `id ⊗ σK`. Starting at one map and ordering the others by successive
   precompositions yields exactly `x ↦ x ∘ finRotate l` there and at any split finite place.
4. Apply `Langlands.Global.chebotarevPrimeRealizationStatement` with arithmetic Frobenius
   `1` for complete splitting and `σK` for inertness. At an unramified place the Frobenius
   order is the residue degree, so the generator gives a single unramified prime of degree
   `l`. For either choice, add the finite set of places of norm below `N` to `S`, using
   `Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le`.
