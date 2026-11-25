/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceHeartOrigin
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceModelTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology

/-! # Etale derived origin on a finite-coefficient slice

Source: Stacks Project, proetale.tex, Tag 09AL
(blueprint: lem-weil-pbc-finite-coefficient-etale-slice-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

-- Keep the original signature, including its unused interval and arrow binders.
set_option linter.unusedVariables false in
/-- A bounded object with finite etale-local cohomology descends to the etale site
of the chart. The final clause transports a supplied constant complex model; it
asserts no existence of such a complex.

Source: Stacks Project, proetale.tex, lemma-compare-constructible-derived (09AL),
with the finite-level comparison and weakly etale localization (099R, 03DJ).
(blueprint: lem-weil-pbc-finite-coefficient-etale-slice-origin).

Proof: restrict scalars along the given coefficient isomorphism. Exact slice
restriction identifies the homology of the restricted derived object with the
restrictions of its homology. The hypotheses therefore make that restricted
object bounded in [a,b] with finite etale-local constant cohomology. Identify the
localized pro-etale site at V with the pro-etale site of V.left. Finite constant
module sheaves are constructible with the one-stratum presentation; their local
finite models descend to the etale site. Use the existing bounded derived-origin
theorem on the descended cohomology sheaves; its proof inducts along bounded
truncation triangles. Bounded-below full faithfulness lifts every connecting morphism and
identifies the resulting cones. The comparison functor is exact and faithful,
so it preserves and reflects the given bounds. Its homology comparison identifies
the etale cohomology with the finite local systems just descended. Express their
trivializing covers as the displayed covering families. For the final clause,
apply comparison to the supplied model isomorphism, then compose the etale and
pro-etale localization equivalences and the coefficient identification. These
functors commute with further slice restriction and constant realization, in
all module differentials, so the result is the specified actual restriction
isomorphism. No bounded complex of finite modules is constructed here. All
functors send the zero object to zero, including on empty charts and for the
zero coefficient ring. -/
theorem finiteCoefficient_etale_slice_origin
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ)
    (K : DerivedCategory (SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hvan : let R₀ := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R);
      ∀ q : ℤ, q < a ∨ b < q → IsZero
        ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
          ((DerivedCategory.homologyFunctor _ q).obj K)))
    (hloc : let R₀ := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R);
      ∀ (q : ℤ) (W : X.Etale) (g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X φ).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                  koszulConstantFunctor X B).obj N)))) :
    ∃ L : DerivedCategory
        (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))),
      (∀ q : ℤ, q < a ∨ b < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj L)) ∧
      (∀ (q : ℤ) (W : V.left.Etale),
        ∃ (I : Type (t + 1)) (U : I → V.left.Etale) (f : ∀ i, U i ⟶ W),
          Sieve.ofArrows U f ∈ V.left.smallEtaleTopology W ∧
          ∀ i, ∃ N : ModuleCat.{t + 1} (ULift.{t + 1} B),
            Module.Finite (ULift.{t + 1} B) N ∧ Nonempty
              (((DerivedCategory.homologyFunctor _ q).obj L).over (U i) ≅
                (constantSheaf (V.left.smallEtaleTopology.over (U i))
                  (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj N)) ∧
      ∀ (W : X.Etale) (g : W ⟶ V)
        (P : CochainComplex (ModuleCat.{t} B) ℤ),
        Nonempty
          ((AlgebraicGeometry.Etale.upperStar
              (ModuleCat.{t + 1} (ULift.{t + 1} B)) g.left).mapDerivedCategory.obj L ≅
            DerivedCategory.Q.obj
              (((constantSheaf W.left.smallEtaleTopology
                (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapHomologicalComplex (.up ℤ)).obj
                (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
                  ).mapHomologicalComplex (.up ℤ)).obj P))) →
        Nonempty
          (ringedSiteDerivedRestrictionOfUniverses
              ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
              ((toProEt X).obj W) K ≅
            ringedSiteDerivedRestrictionOfUniverses
              ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
              ((toProEt X).obj W) ((completedAdicDerivedChange X φ).obj
                (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)))) := by
  classical
  let F := finiteCoefficientSliceRestriction X B R φ V
  let C := comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.left
  let J := F.mapDerivedCategory.obj K
  have hJvan (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj J) := by
    exact (finiteCoefficientSliceRestriction_isZero X B R φ V
      ((DerivedCategory.homologyFunctor _ q).obj K) (hvan q hq)).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  have hheart (q : ℤ) := finiteCoefficient_slice_heart_origin X B R φ hφ
    ((DerivedCategory.homologyFunctor _ q).obj K) V (hloc q)
  choose G hG eG using hheart
  have eH (q : ℤ) : C.obj (G q) ≅ (DerivedCategory.homologyFunctor _ q).obj J :=
    (eG q).some ≪≫ (F.mapDerivedCategoryHomologyFunctorIso q).app K
  have hb : DerivedCategory.TStructure.t.bounded J :=
    ⟨⟨a, (DerivedCategory.isGE_iff J a).2 (fun q hq ↦ hJvan q (Or.inl hq))⟩,
      ⟨b, (DerivedCategory.isLE_iff J b).2 (fun q hq ↦ hJvan q (Or.inr hq))⟩⟩
  obtain ⟨L, _, ⟨eL⟩⟩ :=
    ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology
      (ULift.{t + 1} B) V.left (fun q ↦ ⟨G q, ⟨eH q⟩⟩) hb
  have eLH (q : ℤ) : C.obj ((DerivedCategory.homologyFunctor _ q).obj L) ≅
      (DerivedCategory.homologyFunctor _ q).obj J :=
    (C.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eL
  have eLG (q : ℤ) : (DerivedCategory.homologyFunctor _ q).obj L ≅ G q :=
    C.preimageIso (eLH q ≪≫ (eH q).symm)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro q hq
    apply IsZero.of_full_of_faithful_of_isZero C
    exact (hJvan q hq).of_iso (eLH q)
  · intro q W
    obtain ⟨I, U, f, hcover, hmodels⟩ := hG q W
    refine ⟨I, U, f, hcover, fun i ↦ ?_⟩
    obtain ⟨N, hN, ⟨eN⟩⟩ := hmodels i
    exact ⟨N, hN, ⟨(V.left.smallEtaleTopology.overPullback
      (ModuleCat.{t + 1} (ULift.{t + 1} B)) (U i)).mapIso (eLG q) ≪≫ eN⟩⟩
  · intro W g P hP
    exact finiteCoefficient_slice_model_transport X B R φ hφ K V L ⟨eL⟩ W g P hP

end AlgebraicGeometry.Scheme
