/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Etale origin of constructible complexes locally of finite Tor dimension

Source: Stacks Project, proetale.tex, Tags 09C2 and 09AL
(auxiliary; not a blueprint node).

We use the recorded coefficient-sized small sites and their constant ring sheaves.
The inverse image of a derived object C is expressed using a cochain representative P:
Q(P) is isomorphic to C, and Q of its canonical termwise comparison pullback is isomorphic
to M. Exactness makes this precisely the inverse image on derived categories, independent
of the representative. No inverse-image functor or tensor product is chosen anew.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem torAmplitude_iso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    {K L : ConstantCompletion.D R} (e : K ≅ L) (a b : ℤ)
    (hK : HasCoefficientModelTorAmplitude R K a b) :
    HasCoefficientModelTorAmplitude R L a b := by
  exact ⟨hK.1, fun P hP ⟨f⟩ ↦ hK.2 P hP ⟨f ≪≫ e.symm⟩⟩

private theorem cohomologyBounded_of_torAmplitude {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (M : ConstantCompletion.D R) (a b : ℤ)
    (hab : HasCoefficientModelTorAmplitude R M a b) :
    ∀ q : ℤ, q < a ∨ b < q → IsZero ((coefficientModelCohomology R q).obj M) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  obtain ⟨P, hge, hle, _, ⟨i⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R M a b hab.1).mp hab
  let := hge
  let := hle
  intro q hq
  let iH := (coefficientModelCohomology R q).mapIso i.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ConstantCompletion.Mod R) q).app P
  rcases hq with hq | hq
  · exact (P.isZero_of_isGE a q hq).of_iso iH
  · exact (P.isZero_of_isLE b q hq).of_iso iH

private theorem boundedConstructible_iso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    {K L : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)} (e : K ≅ L)
    (hK : coefficientBoundedConstructibleProEtale X A K) :
    coefficientBoundedConstructibleProEtale X A L := by
  constructor
  · intro q
    exact coefficientProEtale_constructible_of_iso X A
      ((coefficientModelCohomology _ q).mapIso e) (hK.1 q)
  · obtain ⟨a, b, hab, hv⟩ := hK.2
    exact ⟨a, b, hab, fun q hq ↦
      (hv q hq).of_iso ((coefficientModelCohomology _ q).mapIso e.symm)⟩

/-- On a quasi-compact quasi-separated scheme with discrete Noetherian coefficients,
constructible cohomology and locally finite Tor dimension are equivalent to bounded
constructible etale origin with finite Tor amplitude. The local condition tests every
module sheaf on every covering slice, with a possibly different ordered interval on
each covering member. The etale interval is uniform. The complex P only represents C;
its image is the actual canonical termwise comparison pullback, not an arbitrary map.

Source: Stacks Project, Tag 09C2, lemma-describe-constructible-complexes, (2) and (4)
at n = 1, and Tag 09AL, lemma-compare-constructible-derived
(auxiliary; not a blueprint node).

Proof:
1. Apply lem-sfb-proetale-tor-local-global to the local Tor condition. Quasi-compactness
   gives one interval [a,b] for all global module tests, including when X is empty.
2. Test against the constant ring module in degree zero. The K-flat tensor construction
   of prose-03-02 identifies M tensor A_X with M. Thus M has cohomology only
   in [a,b]. Together with the assumed constructibility this gives bounded constructibility.
3. Apply theorem-comparison-constructible-sheaves: its bounded constructible equivalence is
   essentially surjective, giving a bounded constructible etale object C and an isomorphism
   from its derived comparison pullback to M. Choose a cochain representative P of C.
   The localization factorization of the comparison identifies the image of P with M.
4. Apply corollary-finite-tor-amplitude-under-comparison--1 to C and the global interval. Invariance
   under the comparison isomorphism gives the same Tor interval for C. This is the small
   argument omitted in the proof of Tag 09C2 (4).
5. Conversely, the bounded constructible comparison sends C to an object with constructible
   cohomology. The fixed-interval Noetherian Tor comparison sends its Tor bound to M.
   The reverse implication of lem-sfb-proetale-tor-local-global gives the required coverings
   and slice intervals. The termwise representative condition is exactly the comparison
   isomorphism by its canonical localization factorization. No completeness, boundedness
   or prior etale-origin assumption on M enters either direction. -/
theorem constructible_localTor_iff_etaleOrigin
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (M : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :
    ((∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
        ((coefficientModelCohomology _ q).obj M)) ∧
      ∀ U : Scheme.coefficientProEtaleSiteModel.{u, v} X,
        ∃ S : Presieve U,
          Sieve.generate S ∈ Scheme.coefficientProEtaleModelTopology.{u, v} X U ∧
            ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
              ∃ a b : ℤ,
                HasCoefficientModelTorAmplitude
                  ((ConstantCompletion.constant
                    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).over V)
                  ((coefficientModelSliceRestriction
                    (ConstantCompletion.constant
                      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) V).obj M) a b) ↔
      ∃ C : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
        Scheme.IsCoefficientBoundedConstructibleEtale X A C ∧
          (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ C a b) ∧
          ∃ P : ConstantCompletion.Cx (ConstantCompletion.constant
              (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
            Nonempty ((ConstantCompletion.Q _).obj P ≅ C) ∧
              Nonempty ((ConstantCompletion.Q _).obj
                ((constructibleComparisonComplexPullback X A).obj P) ≅ M) := by
  let R : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      CommRingCat.{max v (u + 1)} := ConstantCompletion.constant _ A
  let S : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      CommRingCat.{max v (u + 1)} := ConstantCompletion.constant _ A
  obtain ⟨D, ⟨α⟩, _, e, ⟨β⟩⟩ := finiteTorComparisonNoetherian.{u, v} X A
  constructor
  · rintro ⟨hc, hl⟩
    have ht := (Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally X A M).mpr hl
    have hb : coefficientBoundedConstructibleProEtale X A M := by
      refine ⟨hc, ?_⟩
      obtain ⟨a, b, hab⟩ := ht
      exact ⟨a, b, hab.1, cohomologyBounded_of_torAmplitude R M a b hab⟩
    let M' : ObjectProperty.FullSubcategory
        (fun K ↦ coefficientBoundedConstructibleProEtale X A K ∧
          Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K) := ⟨M, hb, ht⟩
    let C := e.inverse.obj M'
    let i : D.obj C.obj ≅ M := (β.app C).symm ≪≫
      (ObjectProperty.ι _).mapIso (e.counitIso.app M')
    let P := (ConstantCompletion.Q S).objPreimage C.obj
    let j := (ConstantCompletion.Q S).objObjPreimageIso C.obj
    exact ⟨C.obj, C.property.1, C.property.2, P, ⟨j⟩,
      ⟨(α.app P).symm ≪≫ D.mapIso j ≪≫ i⟩⟩
  · rintro ⟨C, hc, ht, P, ⟨j⟩, ⟨k⟩⟩
    let C' : ObjectProperty.FullSubcategory
        (fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
          ∃ a b : ℤ, HasCoefficientModelTorAmplitude S K a b) := ⟨C, hc, ht⟩
    let i : D.obj C ≅ M := (D.mapIso j).symm ≪≫ α.app P ≪≫ k
    let j' : (e.functor.obj C').obj ≅ M := β.app C' ≪≫ i
    refine ⟨(boundedConstructible_iso X A j' (e.functor.obj C').property.1).1, ?_⟩
    apply (Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally X A M).mp
    obtain ⟨a, b, hab⟩ := (e.functor.obj C').property.2
    exact ⟨a, b, torAmplitude_iso R j' a b hab⟩

end AlgebraicGeometry.ProEtale
