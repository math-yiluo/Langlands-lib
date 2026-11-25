/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence

/-!
# Compact-support amplitude bounded by the original geometric fibres

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/
lem-dg-compact-support-amplitude.md, order 1625
(blueprint: theorem-results-from-etale-theory--5).

## Main definitions

- `compactSupportAmplitudeCompactification`: the existing Nagata compactification with
  its base conditions supplied by the finite-type field hypotheses.

## Main statements

- `isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`: vanishing above
  twice the dimension bound on the original geometric fibres.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The existing Nagata compactification for a morphism over a finite-type field scheme.
This supplies its quasi-compact quasi-separated base instances from the finite-type hypotheses;
it introduces no additional choice beyond `NagataCompactification`.
Source: blueprint lem-dg-compact-support-amplitude.md, proof step 1
(blueprint: theorem-results-from-etale-theory--5). -/
noncomputable def compactSupportAmplitudeCompactification
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Compactification f :=
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  NagataCompactification f

/-- For a separated finite-type morphism of finite-type schemes over a field, the higher
compact-support direct image of any etale module sheaf over a finite coefficient ring of
invertible exponent vanishes above twice the dimension bound on the original geometric fibres.
All derived functors are on the ordinary unbounded derived categories.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-dg-compact-support-amplitude.md,
order 1625 (blueprint: theorem-results-from-etale-theory--5).

Proof, following the node's nine steps:
1. A field is Noetherian. By lem-weil-pbc-finite-type-over-noetherian, X and Y are
Noetherian, and Y is quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated.
Use theorem-nagata-s-compactification-theorem--1 to write f = j followed by r with j open and r
proper. By proposition-construction-independence-rf-shriek and
proposition-construction-independence-rf-shriek--7, Rf_! F is Rr_* j_! F. The bounded-below
injective resolution from lem-weil-pbc-dplus-injective-representative is K-injective, so this
computes the same object in the ordinary unbounded derived category.
2. Fix y and its algebraic-closure geometric point. Set T equal to the compactified fibre,
and U equal to the original fibre. By lem-weil-pbc-open-immersion-base-change the map U to T
is open. Apply the derived clause of corollary-cohomology-geometric-fibres--2 and
proposition-extension-zero-restriction-closed-subscheme--11 to identify the pulled-back direct image
with the derived sections of G = j_! F on T. Exactness from situation-conventions and
lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-stalk identifies the q-th geometric
stalk with H^q_A(T,G). By lem-weil-pbc-etale-module-cohomology-forget its underlying group is
H^q(T,G_ab). No finiteness assumption is made on F.
3. By lem-pc-proper-base-change, T is proper and finite type over the algebraic closure.
Use lem-weil-pbc-reduced-induced-closed-subscheme for the reduced closure C of U in T.
By lem-weil-pbc-closed-immersion-proper, C is proper and finite type. Its finitely many
components (lem-sc-noetherian-closed-subset-finite-components) have reduced induced integral
scheme structures, by def-pc-integral-scheme. No factorization of nonreduced U through C is used.
4. Each component C_a meets U: otherwise the finite closed union of the other components
would contain U and hence its closure C. The nonempty open V_a = C_a intersect U has the
same dimension as C_a by lem-sc-integral-locally-algebraic-opens-dimension. It is closed
in U, so def-kun-topological-krull-dimension gives dim C_a = dim V_a <= dim U <= d.
5. Each finite chain in nonempty C lies in one of its components, because its largest
irreducible member lies in a component of the finite closed cover. Thus dim C <= d.
If C is empty, U is empty, and lem-weil-pbc-extension-by-zero-stalks together with
lemma-weil-pbc-geometric-stalk-conservative makes G_ab zero; all its cohomology vanishes.
6. Extension-by-zero stalks vanish outside U, hence outside C. By
proposition-extension-zero-restriction-closed-subscheme--5, G_ab is the closed direct image of H =
i^-1 G_ab on C. A positive additive exponent of the finite ring kills every module. The additive
exact inverse image of prop-weil-pbc-inverse-image-exact therefore makes H torsion, without a
constructibility or finite-stalk assumption.
7. The closed immersion is finite by lem-weil-pbc-closed-immersion-finite, and
lemma-finite-morphisms-cohomology--2 identifies H^q(T,G_ab) with H^q(C,H).
8. The algebraic closure is separably closed, so lemma-cohomological-dimension-base-field--1 gives
torsion cohomological dimension zero. Apply lemma-uniform-bounds-pro-etale-affines to C of dimension
e <= d to obtain torsion cohomological dimension at most 2e, in the sense of
definition-cohomological-dimension. Thus H^q(C,H) vanishes for q > 2d. Retain the stated
invertibility hypothesis; no stronger coefficient assumption is used.
9. By lem-kun-support-geometric-point-independent the vanishing holds at every geometric
point over y. Apply lemma-weil-pbc-geometric-stalk-conservative to the map from zero to the
underlying abelian sheaf. A module sheaf with zero underlying sheaf is zero. Only the
original fibre U and its closed support C were bounded, never the whole compactified fibre T. -/
theorem isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasInvertibleExponent Λ Y] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hq : 2 * (d : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (compactSupportAmplitudeCompactification k Y f)).obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have hdim (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective s
    let a : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶
        Spec (Y.residueField y) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) _))
    have he (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (Y.residueField y)) :
        topologicalKrullDim (pullback f (b ≫ Y.fromSpecResidueField y) : Scheme.{u}) =
          topologicalKrullDim (f.fiber y) := by
      let e := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) b
      calc
        _ = topologicalKrullDim
            (pullback (pullback.snd f (Y.fromSpecResidueField y)) b : Scheme.{u}) :=
          (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
        _ = _ := topologicalKrullDim_pullback_eq_of_field
          (k := Y.residueField y) (pullback.snd f (Y.fromSpecResidueField y)) b
    change topologicalKrullDim
      (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u}) ≤ _
    rw [he Ω (Spec.map t), ← he (AlgebraicClosure (Y.residueField y)) a]
    exact hd y
  have hz := isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt Λ f
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (comp_over f _) d hdim F q hq
  let K := (_root_.DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((rightDerivedLowerShriekOfCompactificationPlusιIso Λ
      (compactSupportAmplitudeCompactification k Y f)
      (HasCompactification.compactification f)).app K))

end AlgebraicGeometry.Etale
