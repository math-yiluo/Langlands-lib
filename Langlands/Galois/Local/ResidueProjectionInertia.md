# The residue projection of a separable closure: the residue homomorphism and inertia

`Langlands.Galois.Local.ResidueProjectionInertia` proves the clauses of
`ResidueProjectionProperties K Ω` (`Galois/Local/ResidueProjectionStatement.lean`) about
the residue homomorphism and the inertia subgroup of a separable closure that the Library
did not yet have: the ninth (action on residues), the twelfth (openness), the fourteenth
and fifteenth (two descriptions of inertia), the seventeenth to twentieth (inertia is
closed, compact, totally disconnected, Hausdorff) and the twenty-second (compatibility
with restriction to normal intermediate fields). It also makes the residue conjugation a
homeomorphism, which openness and the quotient isomorphism
(`ResidueProjectionQuotient.md`) use.

The other clauses on the residue homomorphism and inertia are existing Library theorems,
stated for exactly these objects and used as they are:

| Clause | Library theorem |
| --- | --- |
| 10. continuity | `SepClosed.absoluteResidueHom_continuous` (`Galois/Local/AbsoluteProof.lean`) |
| 11. surjectivity | `SepClosed.absoluteResidueHom_surjective` (`Galois/Local/AbsoluteProof.lean`), whose hypothesis `[IsGalois K Ω]` is Mathlib's instance `IsSepClosure.isGalois` |
| 13. kernel | `SepClosed.absoluteResidueHom_ker` (`Galois/Local/AbsoluteProof.lean`) |
| 16. normality | instance `SepClosed.absoluteInertia_normal` (`Galois/Local/AbsoluteDefinitions.lean`) |

## Setting

Every declaration takes, as the statement does,

```lean
(K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
(Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
```

in independent universes. Local instances with names specific to this module install
`Algebra.IsAlgebraic K Ω`, the local norm of `K` with its ultrametric and completeness
certificates, and finiteness of the residue field of its unit ball
(`localResidue_finite K`). `IsSepClosed Ω` is supplied in each statement that needs it by
`haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`, as explained in
`ResidueProjectionResidueField.md`; `IsGalois K Ω` is Mathlib's instance
`IsSepClosure.isGalois`.

Notation: `G = Ω ≃ₐ[K] Ω` with the Krull topology; `B = closureIntegers K Ω`, with residue
field `k_B`; `k_A` the residue field of `baseIntegers K`; `ρ = absoluteResidueHom K Ω`,
which is by definition `residueTransport K Ω ∘ residueHom K Ω`, where
`residueHom K Ω : G → Gal(k_B/k_A)` reduces automorphisms modulo the maximal ideal of `B`
and `residueTransport K Ω : Gal(k_B/k_A) ≃* Field.absoluteGaloisGroup 𝓀[K]` conjugates by
`localResidueEquiv K : k_A ≃+* 𝓀[K]` and `residueClosureEquiv K Ω : k_B ≃+*
AlgebraicClosure 𝓀[K]`; `I = absoluteInertia K Ω`, which is by definition
`inertia K Ω`, the kernel of `residueHom K Ω`.

## Statements

**`SepClosed.absoluteResidueHom_residue`** (clause 9). For `σ ∈ G` and `x ∈ B`, `ρ σ` sends
the image of the residue of `x` to the image of the residue of `σ x`:

```lean
theorem Langlands.LocalGalois.SepClosed.absoluteResidueHom_residue
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (σ : Ω ≃ₐ[K] Ω) (x : closureIntegers K Ω) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (AlgEquiv.toAlgHom (absoluteResidueHom K Ω σ))
        (residueClosureEquiv K Ω (residue _ x)) =
      residueClosureEquiv K Ω (residue _ (integerAut K Ω σ x))
```

**`SepClosed.residueTransportEquiv`** (definition). The conjugation `residueTransport K Ω`
as an isomorphism of topological groups, and **`SepClosed.residueTransportEquiv_apply`**,
its value:

```lean
def Langlands.LocalGalois.SepClosed.residueTransportEquiv
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    Gal(ResidueField (closureIntegers K Ω)/ResidueField (baseIntegers K)) ≃ₜ*
      Field.absoluteGaloisGroup 𝓀[K]

theorem Langlands.LocalGalois.SepClosed.residueTransportEquiv_apply
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω]
    (τ : Gal(ResidueField (closureIntegers K Ω)/ResidueField (baseIntegers K))) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    residueTransportEquiv K Ω τ = residueTransport K Ω τ
```

**`SepClosed.isOpenMap_absoluteResidueHom`** (clause 12). `ρ` is an open map:

```lean
theorem Langlands.LocalGalois.SepClosed.isOpenMap_absoluteResidueHom
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    IsOpenMap (absoluteResidueHom K Ω)
```

**`SepClosed.mem_absoluteInertia_iff`** (clause 14). `σ ∈ I` exactly when `σ` acts
trivially on the residues of all elements of `B`:

```lean
theorem Langlands.LocalGalois.SepClosed.mem_absoluteInertia_iff
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω]
    (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ absoluteInertia K Ω ↔ ∀ x : closureIntegers K Ω,
      residue _ (integerAut K Ω σ x) = residue _ x
```

**`SepClosed.absoluteInertia_eq_comap_decompositionHom`** (clause 15). `I` is the preimage,
under `decompositionHom K Ω : G →* B.decompositionSubgroup K`, of Mathlib's inertia subgroup
`ValuationSubring.inertiaSubgroup` of the valuation subring `B`:

```lean
theorem Langlands.LocalGalois.SepClosed.absoluteInertia_eq_comap_decompositionHom
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    absoluteInertia K Ω =
      ((closureIntegers K Ω).inertiaSubgroup K).comap (decompositionHom K Ω)
```

**`SepClosed.isClosed_absoluteInertia`**, **`SepClosed.compactSpace_absoluteInertia`** (an
instance), **`SepClosed.totallyDisconnectedSpace_absoluteInertia`**,
**`SepClosed.t2Space_absoluteInertia`** (clauses 17–20). `I` is closed in `G`, and in the
subspace topology it is compact, totally disconnected and Hausdorff:

```lean
theorem Langlands.LocalGalois.SepClosed.isClosed_absoluteInertia
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    IsClosed (absoluteInertia K Ω : Set (Ω ≃ₐ[K] Ω))
instance Langlands.LocalGalois.SepClosed.compactSpace_absoluteInertia
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    CompactSpace (absoluteInertia K Ω)
theorem Langlands.LocalGalois.SepClosed.totallyDisconnectedSpace_absoluteInertia
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    TotallyDisconnectedSpace (absoluteInertia K Ω)
theorem Langlands.LocalGalois.SepClosed.t2Space_absoluteInertia
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    T2Space (absoluteInertia K Ω)
```

**`SepClosed.absoluteResidueHom_restrictNormal`** (clause 22). For an intermediate field `E`
of `Ω/K` normal over `K`, `σ ∈ G` and `y` in the residue field of the integers of `E`,
reduction commutes with restriction: through `residueInclusion K Ω E` and the comparison,
`ρ σ` acts on the image of `y` as the residue action of `σ.restrictNormal E`:

```lean
theorem Langlands.LocalGalois.SepClosed.absoluteResidueHom_restrictNormal
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω]
    (E : IntermediateField K Ω) [Normal K E]
    (σ : Ω ≃ₐ[K] Ω) (y : ResidueField (extensionIntegers K E)) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (AlgEquiv.toAlgHom (absoluteResidueHom K Ω σ))
        (residueClosureEquiv K Ω (residueInclusion K Ω E y)) =
      residueClosureEquiv K Ω
        (residueInclusion K Ω E (residueHom K E (σ.restrictNormal E) y))
```

Here `
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω]` abbreviates the binders of the setting.

## Proofs

*Action on residues.* Unfolding, `ρ σ` applied to `residueClosureEquiv K Ω (residue x)` is
`residueClosureEquiv K Ω (residueHom K Ω σ (e⁻¹ (e (residue x))))` with
`e = residueClosureEquiv K Ω`; cancelling `e⁻¹ ∘ e`, the residue action of `σ` on the class
of `x` is by definition the class of `integerAut K Ω σ x`.

*The homeomorphism.* `residueTransport K Ω` is continuous (the Library's
`residueTransport_continuous`). Its source `Gal(k_B/k_A)` is compact because `k_B/k_A` is
Galois: `k_B` is an algebraic closure of `k_A` (`residue_isAlgClosure`), hence normal, and
separable since `k_A` is finite. Its target is Hausdorff (Krull topology of
`AlgebraicClosure 𝓀[K]` over `𝓀[K]`). A continuous bijection from a compact space to a
Hausdorff space has a continuous inverse (`Continuous.continuous_symm_of_equiv_compact_to_t2`).

*Openness.* The Library's `residueHom_isOpenMap` (`Galois/Local/SpectralProof.lean`, for
`L/K` Galois with finite residue field of the base) says that `residueHom K Ω` is open;
its proof factors it as the open quotient map `G → G/I` followed by the homeomorphism
`residueQuotientEquiv`. Composing with the homeomorphism `residueTransportEquiv` gives that
`ρ` is open.

*Descriptions of inertia; topology.* Since `absoluteInertia K Ω` is by definition
`inertia K Ω`, the Library's general theorems on `inertia` in `SpectralProof`
(`mem_inertia_iff`, `inertia_eq_comap_valuationSubring`, `inertia_isClosed`,
`inertia_compactSpace` and `inertia_totallyDisconnectedSpace`, the last two for `L/K`
Galois) give clauses 14, 15 and 17–19 by unfolding the definition; the Hausdorff property
is the subspace instance of the Hausdorff group `G`. In `SpectralProof` these rest on:
residues of `B` are surjective, so an automorphism of `k_B` is trivial exactly when it is
trivial on residues of elements of `B`; inertia is the kernel of the continuous map
`residueHom K Ω` into a Hausdorff group, hence closed; a closed subset of the compact group
`G` is compact; subspaces of the totally disconnected group `G` are totally disconnected.

*Restriction.* As for the action on residues, unfolding and cancelling `e⁻¹ ∘ e` reduces
the claim to the Library's `residueHom_restrict` (`Galois/Local/AbsoluteProof.lean`), which
checks it on residue representatives: restriction of `σ` to `E` commutes with the inclusion
of the integers of `E` into those of `Ω`.

## Declarations, in order

1. `rpInertiaIsAlgebraic`, `rpInertiaNormedField`, `rpInertiaUltrametric`,
   `rpInertiaComplete`, `rpInertiaResidueFinite` (local instances, namespace
   `Langlands.LocalGalois.SepClosed`).
2. `SepClosed.absoluteResidueHom_residue` (theorem; clause 9).
3. `SepClosed.residueTransportEquiv` (definition).
4. `SepClosed.residueTransportEquiv_apply` (theorem).
5. `SepClosed.isOpenMap_absoluteResidueHom` (theorem; clause 12).
6. `SepClosed.mem_absoluteInertia_iff` (theorem; clause 14).
7. `SepClosed.absoluteInertia_eq_comap_decompositionHom` (theorem; clause 15).
8. `SepClosed.isClosed_absoluteInertia` (theorem; clause 17).
9. `SepClosed.compactSpace_absoluteInertia` (instance; clause 18).
10. `SepClosed.totallyDisconnectedSpace_absoluteInertia` (theorem; clause 19).
11. `SepClosed.t2Space_absoluteInertia` (theorem; clause 20).
12. `SepClosed.absoluteResidueHom_restrictNormal` (theorem; clause 22).

## Literature

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), file
  `/srv/central-library/Serre--Local Fields--1979.pdf` (SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`): Chapter I, §7,
  definition of the decomposition and inertia groups and Proposition 20, printed p. 21
  (for a finite Galois extension of the field of fractions of a Dedekind domain, reduction
  `ε : D → G(l/k)` has kernel the inertia group `T` and induces `D/T ≅ G(l/k)`);
  Proposition 22, printed pp. 22–23 (for `E/K` Galois inside `L/K`, the restriction maps
  on `G`, `D` and `T` form a commutative diagram with exact rows and columns; clause 22 is
  the commutativity of the residue square of this diagram). Serre's statements are finite;
  over a complete `K` the decomposition group is the whole Galois group.
- Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), file
  `/srv/central-library/Neukirch--Algebraic number theory (book)--1999.pdf` (SHA-256
  `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`): Chapter II, §9,
  Definition (9.3), printed p. 168 (the inertia group is the set of `σ` in the
  decomposition group with `σx ≡ x mod 𝔓` for all integers `x`, clause 14; these
  subgroups are closed in the Krull topology, with the argument given there for the
  decomposition group); Proposition (9.9), printed p. 172 (for an arbitrary, possibly
  infinite, Galois extension, the residue extension is normal and
  `1 → I_w → G_w → G(λ|κ) → 1` is exact; surjectivity is proved by density and
  compactness, which is the route of the Library's `residueHom_surjective`).
- J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Thompson / Academic
  Press (1967), file
  `/srv/central-library/Cassels-Frohlich--Algebraic Number Theory--1967/Cassels-Frohlich--Algebraic Number Theory--1967.pdf`
  (SHA-256 `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`): Chapter I
  (A. Fröhlich, "Local Fields"), §7 "Non-ramified Extensions", Theorem 2, printed p. 27
  (definition of the inertia group `Γ₀` of a finite normal extension as
  `{γ | v_L(xγ − x) > 0 for all integers x}`), and printed p. 28 (`Γ₀` is the kernel of
  `Γ → Ω`, the Galois group of the residue extension). Finite extensions of a complete
  discretely valued field.
