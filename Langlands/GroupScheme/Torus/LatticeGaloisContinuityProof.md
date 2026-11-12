# Continuity of the Galois action on the lattices of a torus: proof

Authors: Worker 3483 (formerly Worker 15; Lean proof and original exposition) and
Worker 119 (dependency documentation and exact-target submission). `Langlands.GroupScheme.torusLatticeGaloisContinuity` proves
`Langlands.GroupScheme.TorusLatticeGaloisContinuityStatement.{u}` exactly,
with no added hypotheses or proposition-valued inputs. Its axioms are `propext`, `Classical.choice`
and `Quot.sound`.

## Proof

Let `E/k` be algebraic and `T` a commutative group scheme over `k` with `T_E` split,
say `e : T_E ≅ splitTorus E I`. Put `S₀ = splitTorus.commGroupScheme k I`.

1. `T` is a torus over `k` in the sense of `IsTorus`, with witness `E`. The published
   `IsTorus.quasiCompact` and `IsTorus.quasiSeparated` make `T` quasi-compact and
   quasi-separated over `k`. `S₀` is smooth over `k` (`IsTorus.smooth`), hence locally of
   finite presentation.
2. Let `e' : T_E ≅ (S₀)_E` be `e` followed by the inverse of `splitTorus.baseChangeIso`.
   The published `Descent.FiniteStage.homModel` gives a finite-dimensional intermediate
   field `L`, a homomorphism `g : T_L ⟶ (S₀)_L`, and the recovery equation relating `g`
   to `e'` through the tower comparisons. This `L` is the field in the conclusion.
3. `model_fst` turns the recovery equation into a scheme-level identity. After
   projection to `T.X` and `S₀.X`, the map `e'` is the finite-stage projection followed
   by `g`. It uses `comparison_hom_fst` and the explicit cone maps `baseChangeCone_π_app`.
4. Let `σ` fix `L` pointwise. Then `Spec σ ≫ Spec(L → E) = Spec(L → E)`
   (`galoisBaseMap_comp_of_fixes`). `cone_descent` shows that the finite-stage
   projection is invariant under the canonical descent isomorphism along `Spec σ`. It
   uses `descentBaseChangeIso_hom_fst` and the pullback condition. `descent_comm_of_model`
   combines this with step 3 and gives `(Spec σ)^* e' ≫ descent = descent ≫ e'`.
   Equivalently, the published `galoisHomTransport σ e'` equals `e'`.
5. Characters (`characters_fixed`). Every character of `(S₀)_E` is the base change of a
   character of `S₀`, because base change of characters of a split torus is bijective
   (`IsSplitTorus.characterLattice_baseChange_bijective`). Such characters are fixed by
   every `σ` (`characterLattice.galoisRepresentation_baseChange`). Every character of
   `T_E` has the form `e' ≫ χ'`. By `galoisHomTransport_comp` and step 4,
   `σ (e' ≫ χ') = e' ≫ σ χ' = e' ≫ χ'`.
6. Cocharacters (`cocharacters_fixed`). `σ⁻¹` also fixes `L`, so it fixes all characters.
   `latticePairing_galoisRepresentation_right` gives
   `⟨χ, σ ν⟩ = ⟨σ⁻¹ χ, ν⟩ = ⟨χ, ν⟩`. The pairing is `gmEndEquiv (ν ≫ χ)`, and
   `gmEndEquiv` is injective, so `σ ν ≫ χ = ν ≫ χ` for every character `χ`. Hence
   `σ ν = ν` by `IsSplitTorus.hom_ext_of_characters`, since `T_E` is split.

Steps 5 and 6 give `galoisRepresentation σ = 1` on both lattices.

## Published inputs and provenance

The proof is reused from the immutable Task 3483 draft revision 3, task
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, directory
`revision-3-ce01aee184dec1c896d6b5edb977d87b1fc08762357b7999f699a7d8b24f5d12/files/`.
The Lean proof is unchanged. Its source assertion and original-literature
provenance are documented by the unchanged target module
`Langlands.GroupScheme.Torus.LatticeGaloisContinuityStatement`.
The implemented argument is the finite-model and lattice-pairing argument above.

The following table names the published project results used directly. Names in
this table have the prefix `Langlands.GroupScheme` unless another namespace is
shown. Standard category, pullback, equality and linear-map lemmas are supplied
by Mathlib through the listed imports.

| Published declaration | Module | Use |
| --- | --- | --- |
| `IsSplitTorus.isTorus` | `Langlands.GroupScheme.Torus.Lattice` | The split standard torus is a torus over `k`, so torus smoothness applies. |
| `IsTorus.quasiCompact`, `IsTorus.quasiSeparated` | `Langlands.GroupScheme.Torus.SplittingDescentHelpers` | Quasi-compact and quasi-separated source for finite-stage descent. |
| `IsTorus.smooth` | `Langlands.GroupScheme.Torus.Geometry` | Smoothness of the split torus over `k`, giving local finite presentation. |
| `isSplitTorus_splitTorus` | `Langlands.GroupScheme.Torus.Split` | The standard torus over `k` is split. |
| `Descent.FiniteStage.homModel`, `Descent.FiniteStage.comparison_hom_fst` | `Langlands.GroupScheme.Descent.FiniteStageHom` | Finite field of definition, recovery equation and its underlying projection. |
| `Langlands.AlgebraicGeometry.Picard.baseChangeCone_π_app` | `Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit` | Explicit finite-stage projection. |
| `galoisBaseMap_over` | `Langlands.GroupScheme.Torus.LatticeGalois` | `Spec σ` lies over `Spec k`, supplying the compatibility proof for each canonical descent isomorphism. |
| `descentBaseChangeIso_hom_fst` | `Langlands.GroupScheme.CocharacterTransport` | Descent preserves projection to the original group scheme. |
| `galoisHomTransport_comp` | `Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent` | Transport respects composition of homomorphisms. |
| `IsSplitTorus.characterLattice_baseChange_bijective` | `Langlands.GroupScheme.Torus.SplitLatticeBaseChange` | All characters of the split target descend from `k`. |
| `characterLattice.galoisRepresentation_baseChange` | `Langlands.GroupScheme.Rational.CharacterBaseChange` | Base-changed characters are Galois invariant. |
| `latticePairing_galoisRepresentation_right` | `Langlands.GroupScheme.Absolute.CocharacterAveraging` | Pairing identity reducing cocharacter invariance to character invariance under the inverse. |
| `IsSplitTorus.hom_ext_of_characters` | `Langlands.GroupScheme.Torus.CharacterIsomorphism` | Characters separate homomorphisms into a split torus. |

The proof also uses the published constructions `splitTorus.baseChangeIso`
(`Langlands.GroupScheme.Torus.Split`), `descentBaseChangeIso`
(`Langlands.GroupScheme.CocharacterTransport`), `galoisHomTransport`
(`Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent`) and `gmEndEquiv`
(`Langlands.GroupScheme.Torus.Lattice`). The injectivity of `gmEndEquiv` is
injectivity of that additive equivalence, rather than an additional mathematical
hypothesis. The six lemmas in the local namespace `LatticeGaloisContinuity` are
proved in this file; they are not assumed published inputs.
