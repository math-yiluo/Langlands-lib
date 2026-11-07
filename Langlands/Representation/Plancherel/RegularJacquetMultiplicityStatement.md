# Multiplicity one for actual regular square-integrable induction

`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement` is a
Prop-valued proof target. It asserts a cardinal rank bound for the actual
Jacquet Hom space. This file does not prove the bound.

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d’après Harish-Chandra)* (2003), registered as
`waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Corollary III.7.3, printed p.276 / PDF p.42, says that the weak Jacquet module
of induction of a G-regular square-integrable representation is semisimple
and isomorphic to the sum of its conjugates indexed by the finite relative
Weyl group. Its proof cites III.3.2, III.3.3 and III.7.2. Proposition IV.2.2(i)
and its proof, printed pp.284–285 / PDF pp.50–51, use this description,
unitarity, semisimplicity and Frobenius reciprocity to prove irreducibility.

The present statement is a derived multiplicity consequence intended for
that route. It does not restate the full semisimple decomposition, identify
its finite indexing group, or assert simplicity of the whole Jacquet module.

## Actual inputs and normalization

The structural context is copied from
`ConditionalParabolicGenericIrreducibilityStatement`. The field is any
nonarchimedean local field in `Type u`; its characteristic is unrestricted.
The connected reductive group scheme has the canonical rational-point
topology. Local compactness, the nonarchimedean-group property and
Hausdorffness of its actual point group remain explicit inputs. A
`ParabolicRootPresentation p l a` specifies the actual rational parabolic,
Levi and split component. The supplied geometric radical `n`, actual
semidirect decomposition `h`, closedness of its radical and parabolic,
and continuity of the Levi projection are retained unchanged.

Write `Mpt = parabolicLeviPointSubgroup p l`. The quotient subgroup is
exactly `C = range(parabolicSplitComponentPointHom r)` inside `Mpt`.
Centrality is the published theorem
`parabolicSplitComponentPointHom_range_le_center`; normality follows from
centrality. Square integrability uses the supplied Borel measurable
structure and Haar measure on `Mpt / C`. The representation is the actual
`π : SmoothRep.{0,u,uV} ℂ Mpt`, with group and carrier universes independent.
The square-integrability predicate includes admissibility, a unitary
character of the full abstract center, and square integrability of every
smooth-dual matrix-coefficient norm on this prescribed quotient.

Besides irreducibility and square integrability, the statement assumes
`IsNormalizerRegular π`. This excludes a genuine equivariant equivalence
between `π` and its inverse-conjugate by each actual normalizer element
outside `Mpt`. The elementary normalizer helper does not identify this
condition with the source’s finite relative-Weyl-group condition. That
comparison is part of proving the present derived target.

Induction is literally
`(DynamicNormalization.leviTwistedInductionFunctor h hU).obj π`, the positive
Levi Haar half-modulus followed by inflation and actual smooth induction.
This is the induction used by `UnramifiedLeviInduction` at the trivial
parameter. The Jacquet functor is the existing actual normalized
`jacquetFunctor h hU`. There is no added radical-unimodularity hypothesis;
the actual geometric radical must supply the normalization comparison
when the bound is proved.

## Bound and remaining obligations

The conclusion is

```text
rank_ℂ Hom_Mpt(r_P(I_P π), π) ≤ 1.
```

Here Hom means `Representation.IntertwiningMap` between the displayed
actual algebraic actions, and rank is `Module.rank`, a cardinal. In
particular the statement introduces no finite-dimensionality hypothesis
and preserves the induction carrier universe `max u uV` independently of
the target carrier universe `uV`.

The expected source route restricts maps into the tempered inducing
representation to the weak (unitary) Jacquet part. In the decomposition
of III.7.3 only the identity conjugate contributes: regularity kills the
other Hom spaces, and admissible Schur identifies the remaining
endomorphisms with scalars. This route still requires proofs of the
actual weak-part decomposition, the temperedness and normalization
comparisons, and the finite Weyl interpretation of literal-normalizer
regularity. None is assumed as an extra premise of this statement.

This is a supporting target for the existing generic-irreducibility task,
not a proof or completion of that task. Existence of regular unitary
twists and an open irreducibility locus remain separate obligations.
