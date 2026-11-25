/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteGenericFiberStratumInteriors
import WeilConjectures.AlgebraicGeometry.LisseStratumInteriors
import WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant

/-!
# Generic lissity on the source of a finite morphism

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, proof paragraphs 1--3.
(blueprint: lem-weil-pbc-finite-source-generic-lisse).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible sheaf on a finite scheme over an integral Noetherian affine base
is lisse over some dense open of the base.
This concerns the source sheaf, not its direct image.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, proof paragraphs 1--3.
(blueprint: lem-weil-pbc-finite-source-generic-lisse).

Proof:
1. A finite morphism is integral and closed (`pqf-lem-finite-integral-lft`), and its
source is Noetherian. Replace the source by its reduction using
`thm-weil-pbc-universal-homeomorphism-invariance`. Its irreducible components are
finite in number (`lem-weil-pbc-noetherian-finite-components`).
2. Remove the closed images of the components not dominating the integral base.
For each remaining component the points above the generic point are its generic
point: a finite algebra over the fraction field is Artinian. Use
`lem-weil-pbc-irreducible-lisse-strata` to find a lisse stratum containing that
point. A locally closed stratum containing a generic point contains an open
neighbourhood in that component. Remove the intersections with other components;
the remaining neighbourhoods are open in the source and disjoint. Their finite
union W is lisse and contains the entire generic fibre.
3. Remove the closed image of the complement of W. This image misses the generic
point, so its complement U is dense, and the restriction of E to g⁻¹(U) is lisse.
If there are no dominating components, g⁻¹(U) is empty; its unique underlying
abelian sheaf is lisse (the geometric-stalk condition is vacuous).
Transport back through reduction, which is an equivalence of etale sites.
4. The comparison in `situation-conventions`
identifies set pullback of the underlying sheaf with the underlying sheaf of
abelian pullback. Transport the trivializing cover and finite stalks through
this isomorphism to obtain exactly the displayed underlying abelian restriction. -/
theorem exists_dense_open_lisse_finite_source
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose Z.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      IsLisseEtaleSheafOfSets
        ((sheafCompose (g ⁻¹ᵁ U).toScheme.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι).obj E)) := by
  classical
  obtain ⟨T, hT⟩ := hE
  let W := T.interiorUnion
  have hW := lisse_on_stratum_interiors E T hT
  let U : S.Opens := ⟨(g '' (W : Set Z)ᶜ)ᶜ,
    (g.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hη : genericPoint S ∈ U := by
    rintro ⟨x, hx, hxη⟩
    exact hx (generic_fiber_subset_stratum_interiors S g T x hxη)
  have hUd : Dense (U : Set S) := by
    apply dense_iff_closure_eq.mpr
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure S]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
  have hUW : g ⁻¹ᵁ U ≤ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  refine ⟨U, hUd, ?_⟩
  have h := (pullback_finite_locally_constant
    (Z.homOfLE hUW) W.ι E hW).2
  rw [Scheme.homOfLE_ι] at h
  exact h

end AlgebraicGeometry.Scheme
