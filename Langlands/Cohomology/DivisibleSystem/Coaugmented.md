# Resolutions of ℓ-divisible systems by a coaugmented exact functor

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (ℓ-divisible systems, Harris 1999,
(2.1)), `Langlands.Cohomology.CokernelComplex` (iterated-cokernel complexes of
a coaugmented endofunctor), `Langlands.Sheaf.Equivariant.Godement.Smooth`
(the smooth Godement functor), `Langlands.Cohomology.SmoothGodement.Statement`
(Worker 3's statements about it) and
`Langlands.Cohomology.DivisibleSystem.Cokernel` (cokernel systems). All names
below are in the namespace `Langlands.Cohomology.DivisibleSystem`. Write `T m` for `T.obj m`.

Harris (1999, section 2, printed p.304) has an embedding `T ⟶ F(T)` into an
`R Γ`-acyclic sheaf, functorial in `T` (Berkovich's smooth equivariant
Godement construction). It satisfies Fact 3 (`T ↦ F(T)` is exact) and Fact 4
(`F` carries `ℓ`-divisible systems to `ℓ`-divisible systems). He continues: "Let
b_m : T_m → F(T_m) denote the canonical embedding. It follows from Facts 3
and 4 and the snake lemma that {coker b_m} is again an ℓ-divisible system
[...]. By induction, we thus have". Lemma 2.2 follows. For each `m`, the
constant sheaf `ℤ/ℓ^mℤ` has an `R Γ`-acyclic resolution
`0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that each `{F_m^q}` is an
`ℓ`-divisible system. This module carries out
that induction for an exact endofunctor with a monic coaugmentation on any
abelian category and any `ℓ`-divisible system `T`. It proves that the
resulting maps form a resolution at every level. It identifies the levels
with the iterated-cokernel complex of `T m`. It does not prove acyclicity.

## The general construction

`C` is an abelian category and `ℓ : ℕ`. `F : C ⥤ C` is additive and preserves
finite limits and finite colimits, and `η : 𝟭 C ⟶ F` is a natural
transformation. These hypotheses on `F` are the exactness of Harris's Fact 3,
assumed here, not proved. They make `T.map F` an `ℓ`-divisible system (the
parent module's `map`, the generic form of Fact 4).

- `coaugmentation F η T : T ⟶ T.map F` is the morphism of `ℓ`-divisible
  systems with components `η.app (T m)` (`coaugmentation_tower_app`). These
  are Harris's `b_m`. They commute with the tower maps (Harris's `j`) and
  with the inclusions `i` by naturality of `η`.

From here on every component of `η` is a monomorphism (instance argument
`∀ X : C, Mono (η.app X)`); Harris calls the `b_m` embeddings. The
components of `coaugmentation` are then monomorphisms (instance).

- `residualSystem F η T q`: the residual systems. `R 0 = T`
  (`residualSystem_zero`), and `R (q + 1)` is `cokernelSystem` of the
  coaugmentation of `R q` (`residualSystem_succ`). For `q = 0` this is
  Harris's `{coker b_m}`.
- `termSystem F η T q` is `(residualSystem F η T q).map F`, the system
  `F^q = F(R q)`.
- `residualInclusion F η T q : R q ⟶ F^q` is the coaugmentation of `R q`.
  Its components are `η` at the levels of `R q`
  (`residualInclusion_tower_app`) and are monomorphisms (instance).
- `residualQuotient F η T q : F^q ⟶ R (q + 1)` is `toCokernelSystem` of that
  coaugmentation. Its components are epimorphisms (instance).
  `residualInclusion_residualQuotient_tower_app` says that the composite is
  zero at every level.
- `termDifferential F η T q : F^q ⟶ F^(q + 1)` is `residualQuotient` followed
  by `residualInclusion` (`termDifferential_tower_app`).
- `residualInclusion_termDifferential_tower_app` and
  `termDifferential_comp_termDifferential_tower_app` say that
  `R q ⟶ F^q ⟶ F^(q + 1)` and two consecutive differentials compose to zero
  at every level.

Morphisms of `ℓ`-divisible systems have no zero morphisms in this
formalization, so these statements are made at every level `m`, on the
components `tower.app m`.

## Exactness at every level

- `residual_shortExact q m`: `0 ⟶ R q m ⟶ F^q m ⟶ R (q + 1) m ⟶ 0` is short
  exact. This is `shortExact_app` of the cokernel module.
- `residualInclusion_termDifferential_exact q m`:
  `R q m ⟶ F^q m ⟶ F^(q + 1) m` is exact. For `q = 0` this is exactness of
  `T m ⟶ F^0 m ⟶ F^1 m` at `F^0 m`. A refinement chase: if `x` is killed by
  the differential, it is killed by the projection to `R (q + 1) m`, because
  `residualInclusion` at `q + 1` is a monomorphism. Exactness of the short
  exact row then lifts `x`.
- `termDifferential_exact q m`: `F^q m ⟶ F^(q + 1) m ⟶ F^(q + 2) m` is
  exact. An element killed by the differential lifts to `R (q + 1) m` by the
  previous lemma. Since the projection `F^q m ⟶ R (q + 1) m` is an
  epimorphism, it lifts further to `F^q m` (up to refinement).

Together with the monomorphism `T m ⟶ F^0 m`, these say that
`0 ⟶ T m ⟶ F^0 m ⟶ F^1 m ⟶ ⋯` is exact for every `m`. The proofs use only
the short exact rows `residual_shortExact`, which come from the components of
`η` being monomorphisms. The exactness of `F` enters only through the
construction of the systems `F^q` (via `map`).

## Comparison with the iterated-cokernel complex

`CokernelComplex.residual F η q` and `CokernelComplex.term F η q` are the
endofunctors of the published iterated-cokernel construction. Its residual
functor at `q + 1` is the cokernel, in the functor category, of `η`
whiskered by the residual functor at `q`.

- `residualSystemObjIso F η T q m` identifies level `m` of `R q` with
  `(CokernelComplex.residual F η q).obj (T m)`. At `q = 0` it is the
  identity. At `q + 1` it is the map of cokernels induced by the isomorphism
  at `q` and its image under `F` (`cokernel.mapIso`), followed by the
  inverse of Mathlib's `PreservesCokernel.iso` for evaluation at `T m`.
  Evaluation preserves cokernels because cokernels of functors are computed
  objectwise.
- `termSystemObjIso F η T q m` identifies level `m` of `F^q` with
  `(CokernelComplex.term F η q).obj (T m)`. It is `F` applied to
  `residualSystemObjIso`.
- `residualInclusion_comp_termSystemObjIso_hom`,
  `residualQuotient_comp_residualSystemObjIso_hom` and
  `termDifferential_comp_termSystemObjIso_hom` say that these isomorphisms
  carry `residualInclusion`, `residualQuotient` and `termDifferential` to
  `CokernelComplex.inclusion`, `CokernelComplex.quotient` and
  `CokernelComplex.differential` at `T m`.

So at every level the term systems and their differentials are, up to these
isomorphisms, the terms and differentials of `CokernelComplex.complex F η (T m)`.

## The smooth Godement functor

Here `R`, `G` and `X` are as in the published `SmoothTopologicalSheaf R G X`.
They lie in one universe. `G` is a topological group acting on `X` by
continuous translations, and `HasStableNeighbourhoods G X` holds.
`T : SmoothSheafDivisibleSystem R G X ℓ`. `smoothZeroFunctor R G X` is the
degree-zero smooth Godement functor, a transcription of Berkovich's `F` (see
the Markdown of `Langlands.Sheaf.Equivariant.Godement.Smooth`).
`smoothCoaugmentation R G X` is its coaugmentation. Its components are
monomorphisms by a published instance. The exactness of `smoothZeroFunctor`
is not proved in the Library. It is Worker 3's proposition
`SmoothGodementZeroExactStatement R G X`, and every declaration below takes a
proof `h` of it as an explicit argument.

- `smoothGodementResidualSystem h T q` and `smoothGodementTermSystem h T q`
  are `residualSystem` and `termSystem` for this functor and coaugmentation.
- `smoothGodementCoaugmentation h T : T ⟶ smoothGodementTermSystem h T 0` is
  `residualInclusion` at `q = 0`, Harris's `b`.
- `smoothGodementTermDifferential h T q` is `termDifferential`.
- `smoothGodementTermSystemObjIso h T q m` identifies level `m` of the term
  system with the degree-`q` term of `smoothComplex R G X (T m)`, the smooth
  Godement complex of `T m`.
- `smoothGodementTermDifferential_comp_termSystemObjIso_hom` says that it
  carries the differential to the differential `d q (q + 1)` of that complex.

The exactness lemmas of the general section apply to these systems directly.
The smooth section does not need Worker 3's
`SmoothGodementTermExactStatement` (exactness of the higher term functors):
the term systems are obtained by iterating `cokernelSystem`, not by applying
term functors to `T`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.304. Worker 61 read
the page in the scanned original.

1. "By induction". Harris gives no formula for `F_m^q`. The reading used here
   is the induction of the Godement resolution. `R 0 = T`, `F^q = F(R q)`
   and `R (q + 1) = coker (R q ⟶ F(R q))`, so the cokernel fact of p.304 is
   applied at each step to the system `R q`. The differential is the
   projection followed by the embedding. Harris describes Berkovich's
   acyclic resolution (Berkovich's Proposition 1.4.1, cited on p.304) as "a
   smooth G-equivariant version of the Godement flasque resolution", and
   this is how a Godement resolution is built. The comparison isomorphisms
   above show that at each level `m` the induction gives the published
   `CokernelComplex.complex F η (T m)`, the iterated-cokernel complex of a
   single object.
2. General `T`. Harris states Lemma 2.2 for the constant sheaves `ℤ/ℓ^mℤ`.
   The construction here takes any `ℓ`-divisible system. Lemma 2.2 is the
   case where `T` is the system of constant sheaves with its maps `i` and
   `j`. That system is not constructed here.
3. Hypotheses. Fact 3 (exactness of `F`) is a hypothesis. In the smooth
   section it is `SmoothGodementZeroExactStatement`. Fact 4 for `F` follows
   from it by the parent module's `map`. The embeddings `b_m` are monic by
   assumption in the general section and by the published instance in the
   smooth section.
4. Not proved. Harris's `R Γ`-acyclicity of the `F_m^q` is not proved or
   stated here. For the smooth Godement complex, Worker 3's
   `SmoothGodementCompactAcyclicStatement` is a related statement, not used
   here.
5. Sheaves. The smooth section works with Worker 13's smooth equivariant
   sheaves on a topological space in place of Harris's étale sheaves in
   smooth modules on `U(ẽ)` (see item 6 of the Markdown of
   `Langlands.Cohomology.DivisibleSystem`).

`residualSystem` and `termSystem` are the systems of Lemma 2.2.
`coaugmentation` is Harris's `b`. The maps `residualInclusion`,
`residualQuotient` and `termDifferential` are the maps of the induction.
The exactness lemmas and the comparison isomorphisms are derived. The smooth
declarations are the instance of the general construction for the functor
Harris uses, with Fact 3 as a hypothesis.

## Scope

The module does not prove Harris's Facts 3 and 4 for any Godement functor,
the exactness of the smooth Godement functor, or any acyclicity. It does not
construct the constant systems `ℤ/ℓ^mℤ`, the truncations of Lemma 2.2 bis, or
the `ℓ`-divisible system of complexes formed by the resolutions.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
