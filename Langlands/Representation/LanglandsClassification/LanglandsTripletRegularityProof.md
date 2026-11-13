# `PP̄`-regularity of Langlands triplets (Renard VII.4.1, Lemma): proof

Author: Worker 82, task `78bf8d31-8006-42a6-b25c-c9a031cbbf64`. Module
`Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The theorem `langlandsTripletOppositeRegularity` has exactly the published type
`LanglandsTripletOppositeRegularityStatement.{u, v}` (module
`Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityStatement`), at
the field/group universe `u` and the representation-carrier universe `v`. It adds no
hypothesis. The module also proves two auxiliary theorems,
`GeometricLemmaIntersectionDatum.finite_actionQuotient_piece_of_irreducible` and
`langlandsTripletOppositeKernel`. It defines nothing and states no new `Prop`.

## Source and provenance

The target is the Lemma of VII.4.1 of David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` (printed p.241 /
PDF p.247; the proof is on printed pp.241–242 / PDF pp.247–248). The paired statement
Markdown quotes it and explains how the Lean statement renders it.

This module is an internal proof assembly. It transcribes no new source text, and its
route differs from Renard's in one place. Renard checks `PP̄`-regularity through the
VII.3.3 Lemma for representations of finite length. The Library states that lemma as
`PQRegularityLemmaStatement`, but proves it only under the two finite-length statements
`LeviJacquetFiniteLengthStatement` and `LeviInductionFiniteLengthStatement`, which are
not proved. This proof does not use `PQRegularityLemmaStatement` or either finite-length
statement. It uses the irreducibility and admissibility of `σ ⊗ ψ` instead (see below).

## Overall assembly

`langlandsTripletOppositeRegularity` is

```
langlandsTripletOppositeRegularity_of_kernel_and_identitySupport oppositeIdentitySupport
  langlandsTripletOppositeKernel
```

The published theorem `langlandsTripletOppositeRegularity_of_kernel_and_identitySupport`
(module `LanglandsTripletRegularityReduction`) proves
`OppositeIdentitySupportStatement → LanglandsTripletOppositeKernelStatement →
LanglandsTripletOppositeRegularityStatement`. Its first input is the published theorem
`oppositeIdentitySupport`. Its second input is `langlandsTripletOppositeKernel`, proved
here. `LanglandsTripletOppositeKernelStatement` is clause 1 of the target alone: under
the same data and hypotheses, `IsPQRegular … pbar lbar rbar … a τ` for
`τ = σ.twist ψ …`. The reduction derives clause 2 (the dimension of the intertwining
space is one) from clause 1 and the identity support.

## The kernel clause: `langlandsTripletOppositeKernel`

This theorem proves `LanglandsTripletOppositeKernelStatement.{u, v}`. After introducing
the data, the proof installs the same instances as the statement: `hG.isAffineHom`, the
topology `RationalPointFamily.pointTopology` on `G(F)`, `leviPointTopology l hl` on
`M(F)`, `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup` for `M(F)`.
It also installs `RationalPointFamily.splitComponentPointTopology ha` on `A(F)`. The
hypotheses are named `hLevi : lbar ≫ pbar = l ≫ p`,
`hOpp : pointImage p ⊓ pointImage pbar = pointImage (l ≫ p)` and
`hTrip : IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ`.

1. **The twist.** Let `τ := σ.twist ψ.val.toMonoidHom
   (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)`. The second component of `hTrip`
   says that `σ` is irreducible, so `τ` is irreducible by
   `SmoothRep.isIrreducible_twist_iff`. The third component says that `σ` is tempered,
   and its `.isAdmissible` field gives admissibility of `σ`. So `τ` is admissible by
   `SmoothRep.isAdmissible_twist_iff`. The published reduction makes the same two
   deductions.
2. **The geometric lemma.** The published `representedGeometricLemma` for `P = MU` and
   `P̄ = MŪ` gives `m`, a bijection `c₀ : Fin m ≃ P(F)\G(F)/P̄(F)`, representatives
   `z i` with `DoubleCoset.mk (z i) = c₀ i`, and an intersection datum `E i` at `z i`.
   Reindexing by `c₀.symm` gives representatives `z' w := z (c₀.symm w)` for every
   double coset `w`, with `DoubleCoset.mk (z' w) = w` (`hz'`). It also gives data
   `E' w _ := E (c₀.symm w)` for every `w` strictly below the identity double coset in
   the Bruhat order (`Geometric.BruhatLT`). The gluing clause of the geometric lemma is
   not used.
3. **The filtration of the regularity quotient.** The published
   `exists_pqRegularity_pieceFiltration`, applied with the common Levi equality
   `hLevi.symm : l ≫ p = lbar ≫ pbar`, `z'`, `hz'` and `E'`, gives `n`, a bijection
   `cc` from `Fin n` to the double cosets strictly below the identity, a finite
   filtration `s`, and, for every `j`, an isomorphism `e j` from the `j`-th grade of `s`
   to `pieces j := (E' (cc j) _).pieceFunctor`.
4. **Hypotheses of the weight criterion.** The published
   `pqRegularity_of_disjoint_weights` concludes `IsPQRegular … a τ` from the following
   inputs.
   - Smoothness of each `(pieces j).obj τ`: the published
     `GeometricLemmaIntersectionDatum.pieceFunctor_isSmooth`.
   - Finite dimensionality of the action quotient of `ℂ[A(F)]` acting on `τ` through
     `a`: the published `finite_splitComponent_actionQuotient`, which needs `τ` to have
     finite length. An irreducible representation has finite length
     (`SmoothRep.hasFiniteLength_of_isIrreducible`, which needs no admissibility).
   - Finite dimensionality of the action quotient on each piece `(pieces j).obj τ`:
     `finite_actionQuotient_piece_of_irreducible` below, applied to the irreducible
     admissible `τ`.
   - For every `j`, disjointness of the exponents `groupExponents ha τ` from the
     generalized weights of `A(F)` on `(pieces j).obj τ`. This is exactly the
     conclusion of the published `langlandsTripletOppositePieceSeparation`, applied to
     the same data, `hLevi`, `hOpp`, `hTrip`, `z'`, `hz'`, `E'` and the double coset
     `cc j`.

## Piece finiteness: `finite_actionQuotient_piece_of_irreducible`

Let `D` be a `GeometricLemmaIntersectionDatum` for two represented parabolics `P = MN`
and `Q = MU` with the same Levi `M`, at any point `z`. Let `a : A_M → M` be a split
component (`ha : IsSplitComponent a`). The theorem says: for every smooth representation
`σ` of `M(F)` that is irreducible and admissible, the quotient
`actionQuotient ((D.pieceFunctor.obj σ).ρ.comp (rationalPoints.map a))` is
finite-dimensional over `ℂ`. Here `D.pieceFunctor.obj σ` is the full piece
`i^M_{Q'} ∘ ι ∘ r^M_{P'}(σ)` of the geometric lemma, and the action quotient is the
quotient of the group algebra `ℂ[A_M(F)]` by the annihilator of the piece.

Proof.

1. The published `GeometricLemmaIntersectionDatum.exists_isSplitComponent_factor` gives
   a split component `a' : A' → L'` of the piece Levi `L'` and `f : A_M → A'` with
   `f ≫ a' ≫ D.lQ' ≫ D.q' = a`. Reassociating gives `hb : (f ≫ a') ≫ D.lQ' ≫ D.q' = a`.
2. The published `GeometricLemmaIntersectionDatum.finite_actionQuotient_piece`, applied
   with `b := f ≫ a'` and `hb`, reduces the claim to two properties of the normalized
   Jacquet module `r^M_{P'}(σ) = (leviJacquetFunctor D.p' D.l' D.r' …).obj σ`, where
   `P'` is the parabolic of `M` in `D`. The first property is admissibility over
   `M'(F)`. The second is finite generation of its group-algebra module over
   `ℂ[M'(F)]`.
3. **Admissibility.** The published `arbitraryParabolicJacquetAdmissibility` (Renard
   VI.6.1 Corollary) applied to the admissible `σ` makes the Jacquet module admissible
   as a representation of the Levi image `pointImage (D.l' ≫ D.p')`, a subgroup of
   `M(F)`. The published topological-group isomorphism
   `leviPointsEquiv D.p' D.l' D.hp' D.hl' : M'(F) ≃ₜ* pointImage (D.l' ≫ D.p')`, through
   `isAdmissible_comp_continuousMulEquiv`, transfers admissibility to `M'(F)` with its
   own topology `leviPointTopology D.l' D.hl'`.
4. **Finite generation.** An irreducible `σ` is a simple, hence finitely generated,
   `ℂ[M(F)]`-module (`moduleFinite_asModule_of_isIrreducible`). The published
   `leviJacquetFiniteType` (Renard VI.1.3 Proposition) then makes its normalized Jacquet
   module finitely generated over `ℂ[M'(F)]`.

The same argument appears inside the published
`RepresentedSameLeviGenericRegularity` development. This theorem states it on its own
for irreducible admissible `σ`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.LanglandsTripletOppositePieceSeparation` | `langlandsTripletOppositePieceSeparation` |
| `Langlands.Representation.Intertwining.OppositeIdentitySupportProof` | `oppositeIdentitySupport` |
| `Langlands.Representation.Intertwining.PQRegularityFiniteLength` | `finite_splitComponent_actionQuotient` |
| `Langlands.Representation.Intertwining.PieceActionQuotientFiniteness` | `GeometricLemmaIntersectionDatum.finite_actionQuotient_piece` |
| `Langlands.Representation.Exponents.GeometricLemmaSplitComponent` | `GeometricLemmaIntersectionDatum.exists_isSplitComponent_factor` |
| `Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof` | `arbitraryParabolicJacquetAdmissibility` |
| `Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof` | `leviJacquetFiniteType` |
| `Langlands.Representation.Geometric.RepresentedGeometricLemmaProof` | `representedGeometricLemma` |
| `Langlands.Representation.Smooth.IsotypicProjector` | `moduleFinite_asModule_of_isIrreducible` |

These imports also bring in, transitively, the other published names used above:
`LanglandsTripletOppositeKernelStatement` and
`langlandsTripletOppositeRegularity_of_kernel_and_identitySupport`
(`LanglandsClassification.LanglandsTripletRegularityReduction`), the target statement
(`LanglandsClassification.LanglandsTripletRegularityStatement`),
`exists_pqRegularity_pieceFiltration` (`Intertwining.PQPredecessorFiltration`),
`pqRegularity_of_disjoint_weights` (`Intertwining.PQRegularityFiltration`),
`GeometricLemmaIntersectionDatum.pieceFunctor_isSmooth` (`Intertwining.PQRegularityCriteria`),
`SmoothRep.hasFiniteLength_of_isIrreducible` (`Smooth.IrreducibleRealization`),
`SmoothRep.isIrreducible_twist_iff` and `SmoothRep.isAdmissible_twist_iff` (`Category.Twist`),
`leviPointsEquiv` (`Exponents.ArbitraryParabolicLeviPoints`) and
`isAdmissible_comp_continuousMulEquiv` (`CuspidalSupport.GroupTransport`). All module
names in this paragraph are under `Langlands.Representation`.
