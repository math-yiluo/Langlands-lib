/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!
# Auxiliary facts on affine curves

Small lemmas used in the covering step of blueprint `lemma-tangent-cones-on-cover`:

* `AlgebraicGeometry.isClosed_singleton_apply_of_comp_eq_id`: rational points of schemes locally
  of finite type over an algebraically closed field are closed points.
* `AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen`: the dimension of a
  scheme is that of the ring of sections over an affine open covering it.
* `AlgebraicGeometry.isIntegral_of_smooth_of_irreducibleSpace`: an irreducible scheme smooth over
  a field is integral.
* `AlgebraicGeometry.isDedekindDomain_of_isAffineOpen_of_isIntegrallyClosed_stalk`: the ring
  of sections over an affine open of a locally noetherian normal integral scheme of dimension
  `≤ 1` is a Dedekind domain.
* `IsLocalRing.eq_maximalIdeal_of_map_eq`: an ideal mapping onto the maximal ideal under a ring
  isomorphism of local rings is the maximal ideal.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

/-- An ideal `J` of a local ring whose image under a bijective ring homomorphism to a local ring
is the maximal ideal is the maximal ideal. -/
lemma IsLocalRing.eq_maximalIdeal_of_map_eq {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (g : R →+* S) (hg : Function.Bijective g) {J : Ideal R}
    (h : J.map g = maximalIdeal S) : J = maximalIdeal R := by
  have : IsLocalHom g := .of_surjective g hg.2
  rw [← Ideal.comap_map_of_bijective g hg (I := J), h, maximalIdeal_comap]

namespace AlgebraicGeometry

/-- The image of a `K`-rational point (a section `y` of `f : X ⟶ Spec K`) of a scheme `X` locally
of finite type over an algebraically closed field `K` is a closed point. -/
lemma isClosed_singleton_apply_of_comp_eq_id {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (y : Spec (.of K) ⟶ X)
    (hy : y ≫ f = 𝟙 _) (a : Spec (.of K)) : IsClosed {y a} := by
  rw [Subsingleton.elim a (closedPoint K)]
  exact (pointEquivClosedPoint f ⟨y, hy⟩).2

/-- The dimension of a scheme covered by an affine open `U` is the Krull dimension of
`Γ(X, U)`. -/
lemma topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (hU' : (U : Set X) = Set.univ) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  rw [← hU.topologicalKrullDim_eq, hU']
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).symm

/-- An irreducible scheme smooth over a field is integral. -/
lemma isIntegral_of_smooth_of_irreducibleSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [IrreducibleSpace X] : IsIntegral X := by
  have := IsRegular.of_smooth f
  have : IsReduced X := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- The ring of sections over a nonempty affine open of a locally noetherian integral scheme with
integrally closed local rings is a Dedekind domain if it has dimension at most one. -/
lemma isDedekindDomain_of_isAffineOpen_of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (hint : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : ringKrullDim Γ(X, U) ≤ 1) : IsDedekindDomain Γ(X, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Ring.KrullDimLE 1 Γ(X, U) := ⟨hdim⟩
  have : Ring.DimensionLEOne Γ(X, U) := ⟨fun hne hp ↦ hp.isMaximal_of_ne_bot hne⟩
  have : IsIntegrallyClosed Γ(X, U) := by
    refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
    have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.subset ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hy⟩
    have := hU.isLocalization_stalk' y hy
    have := hint (hU.fromSpec y)
    exact .of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  exact { }

end AlgebraicGeometry
