# Actual descent from a coherent semilinear family

This is an internal construction for actual group schemes over schemes in an
arbitrary universe `u`. It converts a supplied coherent family into a
`Descent.Datum`; it does not supply the family or assert effective descent.

Let `p : S ⟶ B`. The component hypotheses are a finite small type `I`, maps
`q i : S ⟶ Overlap p` whose coproduct is an isomorphism, maps `b i : S ⟶ S`,
and equalities `q i ≫ fst p = 𝟙 S`, `q i ≫ snd p = b i`. The constructor also
takes the redundant instance that every first composite is an isomorphism,
which follows from the displayed first equality. An index operation `m` is
supplied with `b i ≫ b j = b (m i j)`. No group structure or identity law on
the indices is assumed.

`tripleComponent_p12` and `tripleComponent_p23` identify the two adjacent
projections of the existing actual triple components, first in the more
general form allowing any invertible first composite. Their normalized
specializations give the adjacent maps `q i` and `b i ≫ q j`. The first,
middle and last coordinates become respectively `𝟙 S`, `b i` and
`b (m i j)`. The pullback universal property then identifies the remaining
projection with `q (m i j)`.

For an actual group scheme `G` over `S`, `SemilinearComponents.overlap`
assembles supplied isomorphisms
`a i : (baseChange (𝟙 S)).obj G ≅ (baseChange (b i)).obj G` using
`FiniteComponents.pullbackIsoAlong`. Its restrictions recover exactly these
isomorphisms. `SemilinearComponents.cocycle` assumes

```text
(a i).hom ≫ pullHom (b i) (comp_id _) (hm i j) (a j).hom
  = (a (m i j)).hom.
```

It proves the actual Čech cocycle by restricting both sides to the finite
triple components. The successive/direct pullback identity
`pullHom_pullHom`, the projection equalities and component recovery reduce
each restriction to the displayed hypothesis. Joint faithfulness of the
component restrictions gives equality globally.
`SemilinearComponents.datum` bundles this overlap and its proved cocycle.

`semilinearComponent G e` converts an actual isomorphism
`e : (baseChange b).obj G ≅ G` into `baseChangeIdIso G ≪≫ e.symm`.
`baseChangeIdIso_comparison` proves that pulling back the canonical identity
comparison is the canonical iterated/direct comparison; its proof checks
the two actual pullback projections. Inverting the supplied semilinear
tower equation and cancelling this identity comparison proves
`semilinearComponent_comp`.

Consequently `SemilinearComponents.datumOfSemilinear` takes actual
isomorphisms `e i : (baseChange (b i)).obj G ≅ G` and their usual tower law

```text
pullbackComparison (b j) (b i) (b (m i j)) (hm i j) G ≪≫ e (m i j)
  = (baseChange (b i)).mapIso (e j) ≪≫ e i,
```

and constructs actual descent data. `pullIso_datumOfSemilinear` recovers
`baseChangeIdIso G ≪≫ (e i).symm` on each component. The constructor
requires neither affineness nor hypotheses about fields.

The derivation uses the imported actual pullback comparisons, finite
component assembly and triple decomposition. `pullHom_congr_map` is the
elementary equality-transport lemma used to substitute equal component
maps without expanding their endpoint proofs. No external source is
needed for these categorical consequences. Constructing a finite Galois
family from a pinning, a preserved Borel, effective descent, full-centre
adjoints and the unconditional quasi-split inner-form existence theorem
remain separate obligations.
