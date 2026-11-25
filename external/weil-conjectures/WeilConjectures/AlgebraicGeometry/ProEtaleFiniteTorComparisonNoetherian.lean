/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Noetherian finite-Tor comparison

md
(blueprint: corollary-finite-tor-amplitude-under-comparison--1).

We use the same coefficient-sized small site models, constant ring sheaves and standard
localizations as `constructibleComparison`. The Tor predicates test all module sheaves in
degree zero using K-flat representatives. The equivalence retains all ambient derived
morphisms and is identified with the specified comparison inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem coefficientTor_iso {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat)
    {K L : ConstantCompletion.D R} (e : K ≅ L) (a b : ℤ) :
    HasCoefficientModelTorAmplitude R K a b ↔ HasCoefficientModelTorAmplitude R L a b := by
  constructor
  · rintro ⟨hab, hK⟩
    exact ⟨hab, fun P hP ⟨f⟩ ↦ hK P hP ⟨f ≪≫ e.symm⟩⟩
  · rintro ⟨hab, hL⟩
    exact ⟨hab, fun P hP ⟨f⟩ ↦ hL P hP ⟨f ≪≫ e⟩⟩

private theorem restrictComparison {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (S : ObjectProperty C)
    (T : ObjectProperty D) (F : C ⥤ D) (e : P.FullSubcategory ≌ Q.FullSubcategory)
    (he : e.functor ⋙ Q.ι ≅ P.ι ⋙ F)
    (hT : ∀ {K L : D}, (K ≅ L) → (T K ↔ T L))
    (hST : ∀ K, P K → (S K ↔ T (F.obj K))) :
    ∃ e' : ObjectProperty.FullSubcategory (fun K ↦ P K ∧ S K) ≌
        ObjectProperty.FullSubcategory (fun K ↦ Q K ∧ T K),
      Nonempty (e'.functor ⋙ ObjectProperty.ι (fun K ↦ Q K ∧ T K) ≅
        ObjectProperty.ι (fun K ↦ P K ∧ S K) ⋙ F) := by
  let PS : ObjectProperty C := fun K ↦ P K ∧ S K
  let QT : ObjectProperty D := fun K ↦ Q K ∧ T K
  let i : PS.FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let G := i ⋙ e.functor ⋙ Q.ι
  have hG (K : PS.FullSubcategory) : QT (G.obj K) := by
    refine ⟨(e.functor.obj (i.obj K)).property, ?_⟩
    exact (hT (he.app (i.obj K))).mpr ((hST K.obj K.property.1).mp K.property.2)
  let R := QT.lift G hG
  have : R.Full := by
    dsimp [R, G]
    infer_instance
  have : R.Faithful := by
    dsimp [R, G]
    infer_instance
  have : R.EssSurj := by
    constructor
    intro L
    let L' : Q.FullSubcategory := ⟨L.obj, L.property.1⟩
    let K := e.inverse.obj L'
    have ht : T (F.obj K.obj) :=
      (hT (he.app K)).mp
        ((hT (Q.ι.mapIso (e.counitIso.app L'))).mpr L.property.2)
    let K' : PS.FullSubcategory := ⟨K.obj, K.property, (hST _ K.property).mpr ht⟩
    exact ⟨K', ⟨QT.isoMk (Q.ι.mapIso (e.counitIso.app L'))⟩⟩
  have : R.IsEquivalence := {}
  let e' := R.asEquivalence
  refine ⟨e', ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft i he

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Comparison preserves and reflects the exact Tor interval for bounded constructible
complexes over a discrete Noetherian ring and restricts to the finite-Tor equivalence.
The first natural isomorphism characterizes the derived comparison by its action on all
complexes; the final one identifies the forward restricted equivalence with that functor.

md;
Stacks Tags 05VD, 07A4, 06YQ, 08G0 and 08G1
(blueprint: corollary-finite-tor-amplitude-under-comparison--1).

Proof:
1. Obtain the canonical derived comparison D, its factorization on every cochain
   complex, and its bounded constructible equivalence from constructibleComparison.
2. The proved coefficientModelTorAmplitude_iff_flatModel identifies each Tor interval
   with a representative supported in exactly that interval and flat in every degree.
   This uses the source library's native bounded flat-model theorem, with explicit
   bridges for the coefficient-model tensor test and K-flat predicate.
3. The canonical comparison pulls flat sheaves to flat sheaves by
   constructibleComparisonPullback_flat. Termwise application preserves zero terms,
   so the pulled-back bounded flat model has the same interval. The localization
   factorization identifies it with D(K), proving preservation of every Tor bound.
4. For reflection choose a flat-term K-flat representative P' of K. The supplied
   ringed-topos theorem, transported by uniqueness of left adjoints, shows its
   termwise comparison pullback is K-flat. Test the Tor bound on D(K) against the
   pullback of an arbitrary etale module M.
5. constructibleComparisonTensorTest_reflects_zero identifies the ordinary tensor
   test after inverse image and reflects vanishing of its homology. For an arbitrary
   K-flat representative P of K, coefficientModelTensorTest_iso transfers vanishing
   from P' to P. This proves the reverse implication with the same interval.
6. Isomorphism invariance of the coefficient-model Tor predicate follows by composing
   representative isomorphisms. Restrict the bounded constructible equivalence to
   objects with some finite Tor interval. The full subcategories retain all morphisms;
   the reflected interval supplies essential surjectivity and the forward functor
   retains the prescribed natural comparison with D. -/
theorem finiteTorComparisonNoetherian (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∃ D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Nonempty (ConstantCompletion.Q _ ⋙ D ≅
        constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _) ∧
      (∀ K : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
        Scheme.IsCoefficientBoundedConstructibleEtale X A K →
          ∀ a b : ℤ, a ≤ b →
            (HasCoefficientModelTorAmplitude _ K a b ↔
              Scheme.HasCoefficientProEtaleTorAmplitude X A (D.obj K) a b)) ∧
      ∃ e : ObjectProperty.FullSubcategory
          (fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
            ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ≌
          ObjectProperty.FullSubcategory
            (fun K ↦ coefficientBoundedConstructibleProEtale X A K ∧
              Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K),
        Nonempty (e.functor ⋙ ObjectProperty.ι
            (fun K ↦ coefficientBoundedConstructibleProEtale X A K ∧
              Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K) ≅
          ObjectProperty.ι
            (fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
              ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ⋙ D) := by
  obtain ⟨D, hD, e, ⟨he⟩⟩ := (constructibleComparison X A).2.2.2
  have htor : ∀ K, Scheme.IsCoefficientBoundedConstructibleEtale X A K →
      ∀ a b : ℤ, a ≤ b →
        (HasCoefficientModelTorAmplitude _ K a b ↔
          Scheme.HasCoefficientProEtaleTorAmplitude X A (D.obj K) a b) := by
    intro K _ a b hab
    constructor
    · intro hK
      obtain ⟨P, hge, hle, hflat, ⟨eP⟩⟩ :=
        (coefficientModelTorAmplitude_iff_flatModel _ K a b hab).mp hK
      let F := constructibleComparisonPullback X A
      have : F.PreservesZeroMorphisms :=
        @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
          (SheafOfModules.pullbackPushforwardAdjunction
            (F := Scheme.smallModelComparisonInclusion.{u, v} X)
            (constructibleComparisonRingMap X A)).isLeftAdjoint
      let T := (constructibleComparisonComplexPullback X A).obj P
      have htge : T.IsStrictlyGE a := (T.isStrictlyGE_iff a).mpr (fun i hi ↦
        F.map_isZero (P.isZero_of_isStrictlyGE a i hi))
      have htle : T.IsStrictlyLE b := (T.isStrictlyLE_iff b).mpr (fun i hi ↦
        F.map_isZero (P.isZero_of_isStrictlyLE b i hi))
      apply (coefficientModelTorAmplitude_iff_flatModel _ (D.obj K) a b hab).mpr
      refine ⟨T, htge, htle, fun i ↦ ?_, ?_⟩
      · exact constructibleComparisonPullback_flat X A (P.X i) (hflat i)
      · obtain ⟨α⟩ := hD
        exact ⟨(α.app P).symm ≪≫ D.mapIso eP⟩
    · intro hK
      refine ⟨hab, ?_⟩
      intro P hP ⟨eP⟩ M q hq
      obtain ⟨P', hP', hf, ⟨eP'⟩⟩ := exists_coefficientModelFlatKFlatRepresentative
        (ConstantCompletion.constant (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) K
      let T := (constructibleComparisonComplexPullback X A).obj P'
      have ht : T.IsKFlatIndependentCoefficients :=
        constructibleComparisonComplexPullback_kFlat X A P' hP' hf
      obtain ⟨α⟩ := hD
      have hz : IsZero (coefficientModelTensorTest _ P' M q) := by
        apply constructibleComparisonTensorTest_reflects_zero X A P' M q
        exact hK.2 T ht ⟨(α.app P').symm ≪≫ D.mapIso eP'⟩
          ((constructibleComparisonPullback X A).obj M) q hq
      obtain ⟨eT⟩ := coefficientModelTensorTest_iso _ P P' hP hP' (eP ≪≫ eP'.symm) M q
      exact hz.of_iso eT
  refine ⟨D, hD, htor, ?_⟩
  apply restrictComparison _ _ _ _ D e he
  · intro K L f
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, (coefficientTor_iso _ f a b).mp h⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, (coefficientTor_iso _ f a b).mpr h⟩
  · intro K hK
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, (htor K hK a b h.1).mp h⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, (htor K hK a b h.1).mpr h⟩

end AlgebraicGeometry.ProEtale
