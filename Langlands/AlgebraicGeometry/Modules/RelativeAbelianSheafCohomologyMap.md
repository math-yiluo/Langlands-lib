# Actual relative cohomology maps and Ext-defined sheaf cohomology

Let `f : X → Spec R` be an actual scheme morphism in arbitrary universe `u`.
For an actual module `M` on `X` and any `n : ℕ`, `relativeHAddEquiv f M n`
is the unchanged additive equivalence from Ext-defined cohomology of the
underlying abelian sheaf to absolute module cohomology, followed by the
existing `relativeCohomologyRestrictScalarsIso`. Thus its target is the actual
relative cohomology module with the specified `R` action. No finiteness,
flatness, properness or quasi-coherence hypothesis is imposed.

`relativeCohomologyIso_relativeHAddEquiv` proves that applying the existing
canonical relative module/abelian-sheaf comparison to this equivalence gives
exactly `AbelianSheafDerivedSections.HAddEquiv`. The proof evaluates
`relativeCohomologyIso_restrictScalars` on the existing absolute comparison
and cancels the forward and inverse absolute comparison maps.

`relativeHAddEquiv_naturality` retains every actual coefficient morphism
`a : M → N`; its two routes are the relative cohomology image of `a` and
the Ext-defined `Sheaf.H.map` of the underlying morphism.
`relativeHAddEquiv_baseRing` retains a map `φ : R → S`, another structure
map `f' : X → Spec S`, and the actual equality `f = f' ≫ Spec.map φ`.
It compares the same Ext class with the actual
`relativeCohomologyBaseRingIso`. Both proofs apply injectivity of the
relative module/sheaf comparison, use its already proved naturality or
base-ring identity, and then apply the preceding normalization.

Now let `h : X → Y` be an actual closed immersion whose underlying
topological map is an isomorphism, and let `g : Y → Spec R`.
`relativeCohomologyIso_pushforward_apply` identifies the existing module
`pushforwardCohomologyIso.hom`, after the relative module/sheaf comparison,
with `UnitSheafPushforward.pushforwardDerivedComparison (asIso h.base)`.
The underlying forgetting comparison has identity components, so its
derived image is an identity. The two actual sections isomorphisms are
definitionally equal; evaluating the existing relative pushforward identity
then gives the result. Closed-immersion vanishing supplies the actual
module comparison's higher-direct-image premise.

`relativeHAddEquiv_pushforward` identifies this forward module comparison
with the published `cohomologyPushforwardEquiv` under `relativeHAddEquiv`.
It applies the relative module/sheaf comparison and uses the already proved
Ext/derived-sections pushforward square. The inverse theorem
`relativeHAddEquiv_pushforward_inv` cancels the module isomorphism and
retains the forward Ext pushforward.

Finally, fix `g' : X → Spec S`, `φ : R → S`, and the actual commutative
square `h ≫ g = g' ≫ Spec.map φ`. For an actual coefficient map
`a : M → h_*N`,
`relativeHAddEquiv_closedImmersionCohomologyMap` proves that the published
`closedImmersionCohomologyMap` applied to `relativeHAddEquiv g M n x`
is exactly

`relativeHAddEquiv g' N n (cohomologyPushforwardEquiv (asIso h.base)
  ((toAbSheaf X).obj N) n (Sheaf.H.map ((toAbSheaf Y).map a) n x))`.

The proof unfolds the canonical closed-immersion map into the coefficient
map, inverse module pushforward comparison, and base-ring comparison,
and applies the three corresponding identities. These are independently
defined actual maps; none is replaced by a transported map to force the
equality.

The provenance is internal, from the published actual module/sheaf
comparisons, scalar-restriction isomorphisms and Ext/derived pushforward
square. The construction provides the general map comparison needed for
Picard ideal-cohomology naturality. Specializing it to the actual
Artinian ideal morphisms, identifying actual obstruction classes, and
proving the exact field Picard-stack atlas remain further obligations.
