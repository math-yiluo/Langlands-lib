# Berkovich's composite-functor identification for étale and quasi-étale `G`-sheaves

Author: Worker 16.

This module declares, in the namespace
`Langlands.Cohomology.AnalyticGlobalComposite`, one auxiliary definition and
two theorem-statement definitions. The statements are propositions, not
proofs. The isomorphisms and their naturality are the conclusions; nothing is
supplied as data or as a hypothesis about cohomology. No proof is given here.
The truth argument below explains why the statements are expected to hold.

Berkovich, §1.2, defines for a `G`-space `X` the global sections `Γ_{X(G)}`
on `X(G)` and the functor `Γ_{X{G}}` to discrete `G`-modules, with
`Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`. For every abelian sheaf `F` he asserts a spectral
sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`. This holds both on
the quasi-étale and on the étale site. The propositions below state, in
derived-category form, the composite-functor identification behind that
spectral sequence. The derived invariant global sections `H^n(X(G), F)` are
the morphisms, in the derived category of smooth representations, from the
trivial representation `R` in degree `0` to the `n`-th shift of
`RΓ(X{G}, F)`. The isomorphisms are natural in `F`. The spectral sequence
itself is not constructed or stated here.

These are the analytic counterparts of `EquivariantGlobalCompositeStatement`
in `Langlands.Cohomology.EquivariantComposite.Statement`. That statement
covers equivariant sheaves on a topological space. It is proved in
`Langlands.Cohomology.EquivariantComposite.GlobalProof`
(`equivariantGlobalComposite`).

## Setting and imported objects

All sheaf-theoretic objects come from Worker 26's modules
`Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalComplex` and
`Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleGlobalComplex` (namespace
`Langlands.Sheaf.Equivariant.Analytic`). They also come from the modules these
build on: `AnalyticGSheaves`, `AnalyticEtaleCohomology`,
`AnalyticQuasiEtaleCohomology`, `TwistedExactGlobalComparison` and
`TwistedExactGlobalComplex`, all by Worker 26, and Worker 21's analytic spaces
and étale and quasi-étale sites.

- `K : Type u` is a complete ultrametric normed field (`NormedField`,
  `IsUltrametricDist`, `CompleteSpace`). `X` is an object of Worker 21's
  category of analytic spaces `LocalizedCategory.{u, v, v} (K := K)`. This is
  the category for one fixed field `K`. Its morphisms are built from strong
  atlas maps, whose chart pullbacks are bounded `K`-algebra homomorphisms
  (`BoundedAlgHom K`, in `Langlands.Geometry.Analytic.StrongAtlasMaps`), so
  they are morphisms over `K`. The underlying atlases
  (`Langlands.Geometry.Analytic.DisjointAffinoidAtlas`) require only that the
  space be locally Hausdorff, not Hausdorff.
- `G : Type z` is a topological group (`IsTopologicalGroup`), and
  `ρ : G →* Aut X` is an action of `G` on `X` by automorphisms in that
  category. These are automorphisms over `K`, so `G` acts trivially on the
  base field. Neither continuity of `ρ` nor a Hausdorff property of `X`
  is assumed. The section "Correspondence and modelling choices" compares this
  scope with Berkovich's.
- `R : Type (max u (v + 1) uL)` is a commutative ring. Sheaves take values in
  `R`-modules. This coefficient universe is the one used by Worker 26's
  derived functors.
- `EtaleGSheaf ρ (ModuleCat R)` and `QuasiEtaleGSheaf ρ (ModuleCat R)` are
  Worker 26's models of Berkovich's categories `T_G(X_ét)` and `T_G(X_qét)`
  of Definition 1.4.1, for sheaves of `R`-modules. They are sheaves on the
  twisted étale (resp. quasi-étale) site. Their sections are locally discrete
  for the lifts of the action to distinguished étale objects (resp. discrete
  over compact quasi-étale objects).
- `etaleGSheafInvariantCohomology ρ R n` and
  `quasiEtaleGSheafInvariantCohomology ρ R n` are Berkovich's `H^n(X(G), F)`.
  They are the `n`-th right derived functors of the invariant global sections
  `F ↦ Γ_{X{G}}(F)^G`, computed with injective resolutions among étale (resp.
  quasi-étale) `G`-sheaves, and take values in `ModuleCat R`. In degree `0`
  this is `Γ_{X(G)}`. The `G`-invariants of the smooth global sections are
  exactly the invariant global sections, as in Berkovich's
  `Γ_{X{G}}(F)^N = F(X_{G/N}(G))` for `N = G`.
- `etaleGSheafComplex ρ R` and `quasiEtaleGSheafComplex ρ R` are the complexes
  `RΓ(X{G}, F)` in `DerivedCategory.Plus (SmoothRep R G)`: `Γ_{X{G}}` applied to
  an injective resolution among `G`-sheaves. Here `Γ_{X{G}}(F)` is the smooth
  part of the representation of `G` on the global sections. The cohomology of
  `RΓ(X{G}, F)` in degree `q` is Berkovich's `H^q(X{G}, F)`
  (`etaleGSheafComplexHomologyIso`, `quasiEtaleGSheafComplexHomologyIso`).
  Inside these definitions the derived category of `G`-sheaves is Mathlib's
  `HasDerivedCategory.standard`. The model of the derived category of smooth
  representations is an instance argument.
- Mathlib: `HasDerivedCategory` (a model of the derived category),
  `DerivedCategory.singleFunctor C 0` (an object placed in degree `0`),
  `DerivedCategory.Plus.ι` (the inclusion of the bounded below derived
  category) and `ShiftedHom A B n`. The last is by definition `A ⟶ B⟦n⟧` and
  carries the additive group structure of the preadditive derived category.
  `f⟦n⟧'` is the image of a morphism `f` under the shift functor.

The auxiliary definition `trivialSmoothRep R G` is the trivial representation
`Representation.trivial R G R` packaged as a smooth representation in
`Langlands.SmoothRep.{uR, uG, uR} R G` (`Langlands.SmoothRep.of`). The
smoothness obligation, that every vector is fixed by an open subgroup, is
proved in the definition: the whole group `G` is an open subgroup fixing every
vector. The definition of the same name in
`Langlands.Cohomology.EquivariantComposite` requires `R` and `G` to lie in one
universe. Here `R` and `G` lie in independent universes, as the analytic
modules require (`R` in `max u (v + 1) uL`, `G` in `z`).

## Declarations

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `trivialSmoothRep R G` | `R` a commutative ring, `G` a topological group | The trivial smooth representation of `G` on `R` (data, smoothness proved). |
| `AnalyticEtaleGlobalCompositeStatement X G ρ R` | `X`, `G`, `ρ`, `R` as above; `[Small.{max u (v + 1) uL} G]`; `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`; then any model `HasDerivedCategory.{w}` of `SmoothRep R G` and any `n : ℕ`. | There is a family `e F` of additive isomorphisms, one for each étale `G`-sheaf `F`, from `(etaleGSheafInvariantCohomology ρ R n).obj F` to `ShiftedHom (single₀ (trivialSmoothRep R G)) (ι ((etaleGSheafComplex ρ R).obj F)) n`. The family is natural: for `f : F ⟶ F'`, `e F' (H^n(f) x) = e F x ≫ (ι ((etaleGSheafComplex ρ R).map f))⟦n⟧'`. |
| `AnalyticQuasiEtaleGlobalCompositeStatement X G ρ R` | The same, with `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]` in place of the admissible-refinement condition. | The same for quasi-étale `G`-sheaves, with `quasiEtaleGSheafInvariantCohomology` and `quasiEtaleGSheafComplex`. |

In classical notation both conclusions read

```
H^n(X(G), F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ(X{G}, F)[n]),
```

naturally in the étale (resp. quasi-étale) `G`-sheaf `F`, where `R` is the
trivial representation in degree `0`.

Binders and conventions:

- The two instance binders `[Small.{max u (v + 1) uL} G]` and the refinement
  condition are binders of the definitions, not hypotheses of Berkovich's
  statement. They are exactly the conditions under which Worker 26 defines the
  source and target: the size condition makes the twisted sites essentially
  small, and the refinement condition makes `G`-sheaves an abelian category
  with enough injectives. The size condition holds, for example, when `G` lies
  in a universe at most `max u (v + 1) uL`. The refinement conditions are not
  proved in the Library. Worker 26's `AnalyticEtaleRefinements` reduces the
  étale one to three propositions about the étale site of `X`, which remain
  hypotheses. If a refinement condition fails for an action, the proposition
  cannot be formed for that action.
- The propositions quantify over all models of the derived category of smooth
  representations, with the morphism universe `w` a free level parameter. Any
  two models are equivalent, so for each `w` the statement does not depend on
  the model. Mathlib's `HasDerivedCategory.standard` supplies one.
- The isomorphisms are additive (`≃+`), not `R`-linear. Mathlib's derived
  categories carry no `R`-linear structure here, so the `R`-module structure
  of the morphism groups is not stated.
- The degree `n` ranges over `ℕ`, where the derived functors on the left are
  defined. For negative `n` the right side vanishes, because `RΓ(X{G}, F)` has
  no cohomology in negative degrees
  (`isZero_etaleGSheafComplex_homology`).
- Only the existence of a natural family is asserted. The statement does not
  say that the family is a particular canonical comparison map.
- The level parameters of both statements are `w, u, v, uL, z`, inspected with
  `lean_check` (`statement_returns_prop: true`).

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers. The following passages were read
in the original.

- §1.1, p.1: an analytic space is a pair `(k, X)` of a non-Archimedean field
  `k` and a `k`-analytic space `X`, and `G(X)` is its group of automorphisms.
  "(If `X` is `k`-analytic, then such an automorphism induces an isometric
  automorphism of the field `k`.)" Also: "In what follows all analytic spaces
  considered are assumed to be Hausdorff."
- §1.1, p.2: "An analytic space `X` endowed with a continuous action of a
  topological group `G` will be called a `G`-space."
- §1.2, p.3: for a `G`-space `X`, the quasi-étale (resp. étale) site
  `X(G)_qét` (resp. `X(G)_ét`), its topos, and the category `S(X(G)_qét)`
  (resp. `S(X(G)_ét)`) of abelian sheaves.
- §1.2, p.4: "We denote by `Γ_{X(G)}` the global sections functor on
  `X(G)~_qét` (resp. `X(G)~_ét`) [...] The high direct images of `Γ_{X(G)}` on the
  category of abelian sheaves will be denoted by `H^q(X(G), F)`." The functor
  `Γ_{X{G}}` goes from `X(G)~` "to the category of (discrete) `G`-sets", with
  `Γ_{X{G}}(F) = lim_→ F(X_{G/N}(G))` over open subgroups `N`. Here `P(G)` is the
  category of `G`-sets with the topology of surjective families, and
  `P(G) ≃ P(G)~`. The rule `Σ ↦ X_Σ(G)` defines a morphism of sites
  `γ : X(G) → P(G)`, and `Γ_{X{G}}(F)` is the `G`-set representing `γ_*F`.
- §1.2, p.5: `Γ_{X{G}}(F)^N = F(X_{G/N}(G))` for every open subgroup `N`.
  "The high direct images of the functor `Γ_{X{G}}` on the category of abelian
  sheaves will be denoted by `H^q(X{G}, F)`. For any abelian sheaf `F` there is
  a spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`."
- Definition 1.4.1 and Theorem 1.4.2, pp.7–8: quasi-étale (resp. étale)
  `G`-sheaves on `X`, and the equivalence of `X(G)~_qét` (resp. `X(G)~_ét`) with
  them induced by `b : X → X(G)`.

We read the group cohomology `H^p(G, -)` in the spectral sequence as the
cohomology of the topos `P(G)~ ≃ P(G)` of discrete `G`-sets, evaluated on
abelian objects, that is, on discrete `G`-modules. Berkovich does not spell
this out. It is the standard reading, since `Γ_{X{G}}` is the pushforward
`γ_*` to that topos. The global sections of the sheaf represented by a
`G`-set `Σ` are `Hom_G(G/G, Σ) = Σ^G`, so `H^p(G, -)` is the derived functor of
invariants on discrete `G`-modules. Taking `N = G` in the formula of p.5 gives
`Γ_{X{G}}(F)^G = F(X(G)) = Γ_{X(G)}(F)`, that is, `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`.

This module does not use the field case of §1.3, pp.5–6, where the acting
group in the cohomology differs from `G`. There `X = p_k` is the spectrum of a
non-Archimedean field `k`, and the action gives an exact sequence of
topological groups `1 → Gal_k → 𝒢 → G → 1`. By Proposition 1.3.1, étale
sheaves on `p_k(G)` correspond to discrete `𝒢`-sets `Σ`, with
`Γ_{p_k(G)}(F) = Σ^𝒢` and `Γ_{p_k{G}}(F) = Σ^{Gal_k}`, and for abelian `F` Berkovich
records `H^q(p_k(G), F) = H^q(𝒢, F)` and `H^q(p_k{G}, F) = H^q(Gal_k, Σ)`. The
group in `H^q(p_k(G), F)` is the extension `𝒢`, not `G`. That agrees with the
composite in degree `0`: `(Σ^{Gal_k})^G = Σ^𝒢`, because `G = 𝒢/Gal_k`.

The spectral sequence is the Grothendieck spectral sequence of the composite
`Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`. Its existence uses that `Γ_{X{G}}` sends
injectives to `(-)^G`-acyclic objects. The Lean statements are the
derived-category form of this composite,
`R(Γ_{X(G)}) ≅ RHom_{SmoothRep}(R, RΓ_{X{G}}(-))`. The spectral sequence is the
hyperext spectral sequence of the right side.

## Correspondence and modelling choices

- Berkovich's abelian sheaves on `X(G)_ét` (resp. `X(G)_qét`) are modelled by
  Worker 26's étale (resp. quasi-étale) `G`-sheaves, through Theorem 1.4.2, as
  in all of Worker 26's analytic modules. Theorem 1.4.2 is not formalized.
  Derived functors are therefore taken in the category of `G`-sheaves, which
  corresponds to Berkovich's derived functors on `S(X(G))` under that theorem.
- Coefficients are `R`-modules for an arbitrary commutative ring `R` in the
  coefficient universe. Berkovich's abelian sheaves are the case
  `R = ULift ℤ`.
- Berkovich's `H^p(G, M)` for discrete `G`-modules, read as above through the
  topos `P(G)` of §1.2 p.4, appears as
  `Ext^p_{SmoothRep R G}(R, M) = Hom_D(R, M⟦p⟧)`. Smooth representations are
  representations in which every vector has an open stabilizer, which is
  Berkovich's discreteness. For `R = ULift ℤ` they are discrete `G`-modules,
  and `Ext^p(R, -)` is the derived functor of invariants, since
  `Hom(R, M) = M^G`. The acting group is `G` itself, as in the §1.2 spectral
  sequence; the extension `𝒢` of the field case in §1.3 does not enter.
- The spectral sequence is replaced by the composite isomorphism from which it
  is derived. Its `E_2` page, differentials and abutment filtration are not
  stated.
- Scope of spaces and actions. The formal scope differs from Berkovich's in
  three ways, and it is neither contained in nor contains his.
  - Continuity. Berkovich works with `G`-spaces, that is, continuous actions
    (§1.1 p.2). The Lean propositions do not assume `IsContinuousAction ρ`.
  - Hausdorff spaces. Berkovich assumes all analytic spaces Hausdorff (§1.1
    p.1). The Lean propositions have no Hausdorff premise, and the Library's
    analytic spaces are only required to be locally Hausdorff.
  - Base field. Berkovich's automorphisms of a `k`-analytic space may induce a
    nontrivial isometric automorphism of `k` (§1.1 p.1). In
    `LocalizedCategory (K := K)` all morphisms are over the fixed field `K`, so
    `Aut X` consists of `K`-linear automorphisms. The Lean propositions
    therefore say nothing about actions that move the base field.

  In the first two respects the propositions assert more than Berkovich's
  statement. In the third they cover only part of it. The truth argument
  below is categorical. It uses only the abelian categories of `G`-sheaves
  and their enough injectives, which the two instance binders provide, and
  the exact constant-sheaf functor with its right adjoint. It uses
  neither continuity nor the Hausdorff property, so it applies to the whole
  formal scope. Imposing Hausdorffness of `X` and continuity of `ρ` gives the
  fixed-base-field specialization of Berkovich's setting: Hausdorff
  `K`-analytic `G`-spaces on which `G` acts `K`-linearly. Outside that
  specialization the Library objects remain defined. Theorem 1.4.2 is then not
  available to interpret them as sheaves on `X(G)`, and Berkovich's statement
  says nothing about them.
- Compactness. No compactness of `X` or of `G` is assumed. The identification
  concerns ordinary global sections, and Berkovich states the spectral
  sequence for every `G`-space. This differs from the compactly supported
  `CompactGroupCompactCompositeStatement`, which needs compact `G`.

## Truth argument

Both statements are instances of Grothendieck's composite-functor principle,
by the same argument as for `EquivariantGlobalCompositeStatement`.

1. In `SmoothRep R G`, invariants are morphisms from the trivial
   representation: `M^G ≅ Hom(trivialSmoothRep R G, M)` naturally in `M`.
   Hence the right derived functors of `(-)^G` are
   `Ext^p(R, -) = Hom_D(R, -⟦p⟧)`.
2. `Γ_{X{G}}` sends injective `G`-sheaves to injective smooth
   representations. It is right adjoint to the constant `G`-sheaf functor
   `M ↦ M_X` from smooth representations to `G`-sheaves, which is exact. The
   right adjoint of a functor preserving monomorphisms preserves injective
   objects. Worker 26's published module
   `Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction` proves this as
   `etaleGSheafSections_preservesInjectiveObjects` and
   `quasiEtaleGSheafSections_preservesInjectiveObjects`, with the adjunctions
   `etaleConstantGSheafAdjunction` and `quasiEtaleConstantGSheafAdjunction`.
   Both theorems use only the two instance binders above, without continuity.
   This module does not import `AnalyticConstantAdjunction`, since the
   statements do not mention it.
3. Let `F → I^•` be an injective resolution among `G`-sheaves. Then
   `C = Γ_{X{G}}(I^•)` represents `RΓ(X{G}, F)`. It is a bounded below complex
   of injective smooth representations, so
   `Hom_D(R, C⟦n⟧) = H^n(Hom(R, C)) = H^n(C^G) = H^n(Γ_{X(G)}(I^•))`, and the last
   group is `H^n(X(G), F)`. Both sides are computed functorially from the same
   resolutions, which gives naturality in `F`.

The published proof `GlobalProof` of the topological-space statement follows
this route. It uses `ConstantAdjunction` and `KInjectiveHomology` (Worker 134)
and `InvariantsHom`, and its pattern should transfer.

## Role in the Harris framework

These propositions are theorem statements for Task 16, "Formalize the Harris
and Berkovich cohomological theorem-statement framework". That task covers
Berkovich's equivariant cohomology of analytic spaces with group actions, the
setting of the Drinfeld tower in Harris's local computations. These
propositions state the ordinary-cohomology composite of Berkovich §1.2. The
task's coverage note
`notes/henniart/harris-cohomology-coverage.md` lists the stated and open
comparisons. No other Library statement uses these propositions yet. Their
proofs are separate obligations.
