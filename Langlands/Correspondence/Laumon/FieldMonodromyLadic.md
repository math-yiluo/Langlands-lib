# ℓ-adic monodromy over a field, from the homeomorphism onto the fundamental group

Module `Langlands.Correspondence.Laumon.FieldMonodromyLadic`. For a field `K` with separable
closure `Ω`, it proves each clause of `Langlands.Henniart.Laumon.LadicFieldMonodromyStatement`
(module `Langlands.Correspondence.Laumon.FieldMonodromy`) for the monodromy functor
`fieldMonodromyFunctor ℓ K Ω`. The clauses that need it assume that
`fieldGaloisToAut K Ω : Gal(Ω/K) →* Aut (fiber (fieldGeometricPoint K Ω))` is continuous,
surjective or a homeomorphism. The module then assembles them into
`ladicFieldMonodromyStatement_of_isHomeomorph`, which gives `LadicFieldMonodromyStatement`
if `fieldGaloisToAut K Ω` is a homeomorphism for every field `K` and separable closure `Ω`.

Throughout, `M = universalLisseMonodromy ℓ (Spec K) Ω` and `t = fieldGeometricPoint K Ω`.
By definition, `fieldMonodromy ℓ K Ω G = (M.rep t G).comp (fieldGaloisToAut K Ω)`.
`fieldMonodromy_isEquivalenceAt` is weil-conjectures's `universalLisseMonodromy_isEquivalenceAt`
at `t`. `Spec K` is connected, regular and Noetherian, and the instances are found as in the
statement module.

## The clauses of the first conjunct

1. `isLadicContinuous_fieldMonodromyRepresentation` combines continuity of the matrix
   coefficients on `Aut (fiber t)` with continuity of `fieldGaloisToAut K Ω` to obtain
   `continuous_fieldMonodromy_coeff`. The criterion `isLadicContinuous_iff` of
   `Langlands.Correspondence.HenniartLadicTransport` then gives the Library's continuity
   predicate. For `isLadicDefinedOverFiniteExtension_fieldMonodromyRepresentation`, the
   homeomorphism makes `Gal(Ω/K)` compact because `Aut (fiber t)` is compact.
   `IsLadicContinuous.isLadicDefinedOverFiniteExtension` then gives a finite model.
2. For `fieldMonodromyFunctor_full`, surjectivity of `fieldGaloisToAut K Ω` makes a map
   intertwining the Galois actions intertwine the actions of `Aut (fiber t)` as well. Fullness
   follows by `full_comp` of `Langlands.Sheaf.LisseMonodromyTransport`.
   `fieldMonodromyFunctor_faithful` uses faithfulness of the stalk functor at `t`
   (`ext_of_lisseStalkMap`).
3. `exists_fieldMonodromyRepresentation_equiv` transports a continuous
   `A : FiniteRepresentation.{0, u, uW} E Gal(Ω/K)` to an equivalent representation on a
   carrier in universe `u + 1` (`exists_finiteRepresentation_equiv`), which is continuous by
   `IsLadicContinuous.of_equiv`. With the homeomorphism, `essSurj_comp` gives a lisse sheaf with
   an equivalent monodromy representation.
4. `adicStalkMap_shortExact_field` applies `AlgebraicGeometry.ProEtale.adicStalkMap_shortExact`
   of `Langlands.Sheaf.AdicStalkExact` at `t` to an arbitrary short exact sequence of
   `ℓ`-adic sheaves.
5. In `fieldMonodromy_tensor`, lisseness of `G ⊗ H` is given by
   `ProEtale.IsAdicLisseSheaf.tensorLeft` (`isAdicLisseSheaf_tensorLeft_field`). The
   `ℚ̄_ℓ`-linear map `fieldTensorStalkMap ℓ G H : G_t ⊗ H_t → (G ⊗ H)_t` is `tensorStalkMap t`
   composed with `WeilCoefficients.tensorRestrict`, the passage from `ℚ̄_ℓ`-tensors to
   `ULift ℚ̄_ℓ`-tensors. It is bijective (`fieldTensorStalkMap_bijective`), by
   `isIso_tensorStalkMap` at the point `t` with values in the algebraically closed field
   `AlgebraicClosure Ω`, and `θ` is its inverse. It intertwines the monodromy of `G ⊗ H` with
   `Representation.tprod` (`fieldTensorStalkMap_fieldMonodromy`, from
   `LisseMonodromy.mono_tensorStalkMap` for the paths `fieldGaloisToAut K Ω σ`). It is natural
   in both lisse sheaves (`fieldTensorStalkMap_naturality`, from `tensorStalkMap_naturality`).
6. `simple_iff_isIrreducible_fieldMonodromy` combines `simple_iff_isIrreducible` at `t` with
   `isIrreducible_comp_iff` along the surjective `fieldGaloisToAut K Ω`.

## The second conjunct

For a nonarchimedean local field `K` and `n : ℕ+`,
`fieldMonodromy_irreducibleLadicClass` uses the homeomorphism to pass between simple sheaves
and classes. A class `c : IrreducibleLadicClass.{u, u, uW} K Ω ℓ n` is the class of a
representation `A` that is `IsLadicContinuous`, `IsLadicDefinedOverFiniteExtension` and
irreducible. Clause 3 gives a lisse `G` with an equivalence from its monodromy representation to
`A`. `G` is simple by clause 6 and `isIrreducible_of_equiv`, and every representative of
`ladicClassForget K Ω ℓ c` is equivalent to `A` (`FiniteRepresentation.classOf_eq_iff`).
Conversely, for a simple `G` of rank `n`, the monodromy representation has an equivalent copy
`B` in carrier universe `uW` (`exists_finiteRepresentation_equiv`). `B` satisfies the three
conditions by clauses 1 and 6 and the invariance lemmas of
`Langlands.Correspondence.HenniartLadicTransport`, and has rank `n`
(`FiniteRepresentation.rank_eq_of_equiv`). Its class is the required `c`.

All declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
