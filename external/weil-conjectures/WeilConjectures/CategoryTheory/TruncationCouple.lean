/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES

/-!
# The truncation couple

Source: Weil conjectures blueprint, chap-Abelian-varieties, cor-pqf-proper-quasifinite-finite,
node def-sp-truncation-couple, order 520 (blueprint: def-sp-truncation-couple).

The terms use the chosen-resolution convention of `def-sp-kinjective-bridge`.
The maps are transported from the image of the canonical truncation triangle
under the K-injective right derived functor. Exactness is a separate statement,
`lem-sp-truncation-couple-exact`; it is not a field of the construction here.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory
namespace TruncationCouple

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- Smart upper truncations of a bounded-below complex remain bounded below.
Choose a lower bound for K. Below that bound the original terms are zero;
the truncation has the same terms, a subobject of a zero term at its boundary,
or zero. This gives a lower bound for the truncation.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
theorem truncLE_plus (K : CochainComplex.Plus A) (q : ℤ) :
    CochainComplex.plus A (K.obj.truncLE q) := by
  obtain ⟨n, hn⟩ := K.property
  have := hn
  exact ⟨n, inferInstance⟩

/-- The bounded-below complex representing tau_{<=q}K.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def truncation (K : CochainComplex.Plus A) (q : ℤ) :
    CochainComplex.Plus A :=
  ⟨K.obj.truncLE q, truncLE_plus K q⟩

/-- The complex H^q(K)[-q], represented by the single complex in degree q.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def cohomologyComplex (K : CochainComplex.Plus A) (q : ℤ) :
    CochainComplex.Plus A :=
  ⟨(CochainComplex.singleFunctor A q).obj (K.obj.homology q), ⟨q, inferInstance⟩⟩

/-- The truncation tau_{<=q-1}K is strictly concentrated in degrees <= q.
It is strictly concentrated in degrees <= q-1, and q-1 <= q.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
instance truncLE_pred_isStrictlyLE (K : CochainComplex.Plus A) (q : ℤ) :
    (K.obj.truncLE (q - 1)).IsStrictlyLE q :=
  CochainComplex.isStrictlyLE_of_le _ (q - 1) q (by omega)

/-- The canonical first arrow of the truncation triangle: Mathlib's truncation
`truncLEMap` of the inclusion tau_{<=q-1}K -> K, preceded by the inverse of the
inclusion tau_{<=q}(tau_{<=q-1}K) -> tau_{<=q-1}K, an isomorphism since
tau_{<=q-1}K is strictly concentrated in degrees <= q.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def transition (K : CochainComplex.Plus A) (q : ℤ) :
    K.obj.truncLE (q - 1) ⟶ K.obj.truncLE q :=
  inv ((K.obj.truncLE (q - 1)).ιTruncLE q) ≫
    CochainComplex.truncLEMap (K.obj.ιTruncLE (q - 1)) q

/-- The transition commutes with the two inclusions into K.
Proof: by `ιTruncLE_naturality` the truncated inclusion followed by the
inclusion of tau_{<=q}K is the inclusion of tau_{<=q}(tau_{<=q-1}K) followed by
the inclusion of tau_{<=q-1}K; cancel the inverse.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
theorem transition_comp_ιTruncLE (K : CochainComplex.Plus A) (q : ℤ) :
    transition K q ≫ K.obj.ιTruncLE q = K.obj.ιTruncLE (q - 1) := by
  simp [transition, Category.assoc]

/-- The cycles-to-cohomology quotient in degree q kills the incoming differential
of tau_{<=q}K: in degree q that complex has the cycles of K, the incoming
differential lands in the boundaries (it is the corestriction of the
differential of K into the cycles), and boundaries map to zero in cohomology.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
theorem truncLE_d_comp_homologyπ (K : CochainComplex.Plus A) (q : ℤ) :
    ∀ i : ℤ, (ComplexShape.up ℤ).Rel i q →
      (K.obj.truncLE q).d i q ≫ (K.obj.truncLEXIsoCycles q).hom ≫ K.obj.homologyπ q = 0 := by
  obtain ⟨i, j, b, hi, hs, hz, he, hj, hn⟩ :=
    CochainComplex.exists_upperTruncationStepSES (C := A)
  intro r hr
  rw [← (hj K.obj q).1, ← Category.assoc, ← (j K.obj q).comm r q]
  simp

/-- The canonical second arrow of the truncation triangle: the map to the single
complex H^q(K)[-q] whose degree-q component is the quotient from cycles to
cohomology (Mathlib's `mkHomToSingle`); all other components are zero.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def projection (K : CochainComplex.Plus A) (q : ℤ) :
    K.obj.truncLE q ⟶ (cohomologyComplex K q).obj :=
  HomologicalComplex.mkHomToSingle
    ((K.obj.truncLEXIsoCycles q).hom ≫ K.obj.homologyπ q) (truncLE_d_comp_homologyπ K q)

section Derived

variable [HasDerivedCategory A]

/-- The canonical truncation triangle has a unique connecting arrow with these
first two arrows. The cone of the transition is quasi-isomorphic to the single
cohomology complex by the projection just defined. Transport the mapping-cone
triangle across that quasi-isomorphism. For uniqueness, TR3 compares two such
triangles with identities on their first two terms; the map on the third term
induces identity on H^q (the projection induces an isomorphism there). An
endomorphism of this single cohomology object is determined by H^q, so that
third map is identity, and the connecting arrows coincide.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
theorem existsUnique_boundary (K : CochainComplex.Plus A) (q : ℤ) :
    ∃! δ : DerivedCategory.Q.obj (cohomologyComplex K q).obj ⟶
        (DerivedCategory.Q.obj (truncation K (q - 1)).obj)⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (transition K q))
        (DerivedCategory.Q.map (projection K q)) δ ∈ distTriang (DerivedCategory A) := by
  obtain ⟨i, j, hi, hj, hδ⟩ := (DerivedCategory.truncation_triangle A q).1 K.obj
  have hi' : i = transition K q := by
    have : Mono (K.obj.ιTruncLE q) := by
      dsimp only [CochainComplex.ιTruncLE]
      infer_instance
    apply (cancel_mono (K.obj.ιTruncLE q)).1
    rw [hi, transition_comp_ιTruncLE]
  have hj' : j = projection K q := by
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.obj.homology q)).hom).1
    rw [hj]
    simp [projection, HomologicalComplex.mkHomToSingle_f]
  simpa only [hi', hj', truncation, cohomologyComplex] using hδ

/-- The canonical truncation triangle, with all three objects represented by complexes.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def triangle (K : CochainComplex.Plus A) (q : ℤ) :
    Triangle (DerivedCategory A) :=
  Triangle.mk (DerivedCategory.Q.map (transition K q))
    (DerivedCategory.Q.map (projection K q)) (Classical.choose (existsUnique_boundary K q))

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
  [IsGrothendieckAbelian.{v₁} A] [IsGrothendieckAbelian.{v₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- Comparison with the recorded K-injective bridge: apply RF to the
quasi-isomorphism K -> I, compute RF(I) by its unit on the K-injective complex,
and then use the standard comparison between derived and complex cohomology.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def bridgeIso (L : CochainComplex.Plus A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj L.obj)) ≅
      F.rightDerivedCohomologyWithResolution L
        (CochainComplex.grothendieckKInjectiveResolutionChoice.{v₁} L.obj) n :=
  let r := CochainComplex.grothendieckKInjectiveResolutionChoice.{v₁} L.obj
  letI : QuasiIso r.map := r.quasiIso
  letI : r.complex.IsKInjective := r.isKInjective
  (DerivedCategory.homologyFunctor B n).mapIso
    (F.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map r.map)) ≪≫
      F.rightDerivedFunctorObjQIso r.complex) ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app
      (F.rightDerivedComplexWithResolution L r)

/-- D^{p,q} = H^{p+q}(Rv(tau_{<=q}K)), using the bridge's chosen resolution.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def D (K : CochainComplex.Plus A) (p q : ℤ) : B :=
  F.rightDerivedCohomologyWithResolution (truncation K q)
    (CochainComplex.grothendieckKInjectiveResolutionChoice.{v₁}
      (truncation K q).obj) (p + q)

/-- E^{p,q} = H^{p+q}(Rv(H^q(K)[-q])), with the argument a single complex.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def E (K : CochainComplex.Plus A) (p q : ℤ) : B :=
  F.rightDerivedCohomologyWithResolution (cohomologyComplex K q)
    (CochainComplex.grothendieckKInjectiveResolutionChoice.{v₁}
      (cohomologyComplex K q).obj) (p + q)

/-- The triangle after applying the K-injective right derived functor.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def derivedTriangle (K : CochainComplex.Plus A) (q : ℤ) :
    Triangle (DerivedCategory B) :=
  F.rightDerivedFunctor.mapTriangle.obj (triangle K q)

/-- The truncation-inclusion map has bidegree (-1,+1); its total degree is unchanged.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def alpha (K : CochainComplex.Plus A) (p q : ℤ) :
    D F K p q ⟶ D F K (p - 1) (q + 1) :=
  (bridgeIso F (truncation K q) (p + q)).inv ≫
    (DerivedCategory.homologyFunctor B (p + q)).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map
        (eqToHom (congrArg (fun n : ℤ ↦ K.obj.truncLE n)
          (by omega : q = (q + 1) - 1)) ≫ transition K (q + 1)))) ≫
    (bridgeIso F (truncation K (q + 1)) (p + q)).hom ≫
    eqToHom (by unfold D; congr 1; omega)

/-- The projection map has bidegree (0,0).
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def g (K : CochainComplex.Plus A) (p q : ℤ) :
    D F K p q ⟶ E F K p q :=
  (bridgeIso F (truncation K q) (p + q)).inv ≫
    (DerivedCategory.homologyFunctor B (p + q)).map (derivedTriangle F K q).mor₂ ≫
    (bridgeIso F (cohomologyComplex K q) (p + q)).hom

/-- The boundary in total degree p+q lands in total degree p+q+1 and
truncation index q-1, hence has bidegree (+2,-1).
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def f (K : CochainComplex.Plus A) (p q : ℤ) :
    E F K p q ⟶ D F K (p + 2) (q - 1) :=
  (bridgeIso F (cohomologyComplex K q) (p + q)).inv ≫
    DerivedCategory.HomologySequence.δ (derivedTriangle F K q) (p + q) (p + q + 1) ≫
    (bridgeIso F (truncation K (q - 1)) (p + q + 1)).hom ≫
    eqToHom (by unfold D; congr 1; omega)

end Derived
end TruncationCouple

/-- The truncation couple is the displayed pair of bigraded objects with the
three maps induced by the truncation triangles. The lower cohomological bound
is recorded even though the construction of the maps does not depend on it.
The bidegrees agree with the type-zero `BigradedExactCouple` convention;
exactness is reserved for lem-sp-truncation-couple-exact.
Source: blueprint order 520 (blueprint: def-sp-truncation-couple). -/
noncomputable def truncationCouple
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)) :
    Σ D : ℤ → ℤ → B, Σ E : ℤ → ℤ → B,
      (∀ p q, D p q ⟶ D (p - 1) (q + 1)) ×
      (∀ p q, E p q ⟶ D (p + 2) (q - 1)) × (∀ p q, D p q ⟶ E p q) :=
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard B
  let _ := ha
  ⟨TruncationCouple.D F K, TruncationCouple.E F K,
    TruncationCouple.alpha F K, TruncationCouple.f F K, TruncationCouple.g F K⟩

end CategoryTheory
