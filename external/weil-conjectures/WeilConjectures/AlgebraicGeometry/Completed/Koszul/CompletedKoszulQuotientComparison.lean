/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantPresentationTransport

/-!
# The normalized Koszul-to-quotient comparison over completed coefficients

Source: blueprint, proper base change, Koszul and quotient reconstruction, order 1248;
Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-weil-pbc-completed-koszul-quotient-comparison).

This is the reconstruction comparison in the actual completed coefficient presentation,
with coefficient universe one above the scheme universe. The quotient unit is the
constant-tower adjunction unit followed by the specified strict quotient augmentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The localized explicit Koszul fiber is isomorphic to the derived strict quotient
limit, carrying its transported (u,0) unit to the actual quotient completion unit.
No completeness hypothesis on the input is required.

Source: blueprint `prop-weil-pbc-koszul-reconstruction`, comparison assertion;
Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-weil-pbc-completed-koszul-quotient-comparison).

Proof: use the joint constant coefficient transport for the actual quotient completion
and the intrinsic Koszul fiber, with their specified units. Carry the Koszul comparison
along the supplied representative isomorphism, then compose with the inverse quotient
comparison. Full faithfulness lifts this composite to the actual derived category.
Naturality of the constant completion unit and the two transport equations identify its
composite with the intrinsic unit as the actual quotient completion unit.
The construction applies equally to an empty generator list, the zero ring and the
empty scheme: the same normalized towers and completion units are used. -/
theorem completedKoszulQuotientComparison
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T)
    (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K) :
    ∃ c : intrinsicCompletion T d r a ha K C eC ≅
        (completedRlim T (d.completedRing T)).obj ((completedReductionTower T d).obj K),
      intrinsicCompletionUnit T d r a ha K C eC ≫ c.hom =
        ((constLimAdj :
          (Functor.const ℕᵒᵖ : reductionModules T (d.completedRing T) ⥤ d.towers T) ⊣
            completedTowerLimit T (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction
              ).unit.app K ≫
          (completedRlim T (d.completedRing T)).map ((completedReductionTowerUnit d T).app K) := by
  classical
  obtain ⟨D⟩ := completed_constant_presentation_transport T d
  obtain ⟨F, hQ, hKoszul⟩ := D
  obtain ⟨q, hq⟩ := hQ K
  delta completedQuotientCompletionUnit at hq
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hq
  obtain ⟨k, hk⟩ := hKoszul r a ha C
  let G := ConstantCompletion.completion (completedCechTopology T) A d.ideal true
  let c' := k ≪≫ G.mapIso (F.functor.mapIso eC) ≪≫ q.symm
  let c := F.functor.preimageIso c'
  refine ⟨c, F.functor.map_injective ?_⟩
  rw [F.functor.map_comp]
  change F.functor.map (eC.inv ≫ _) ≫ _ = _
  rw [F.functor.map_comp]
  simp only [c, Functor.preimageIso_hom, Functor.map_preimage, c', Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom]
  have hn := (ConstantCompletion.completionUnit
    (completedCechTopology T) A d.ideal true).naturality (F.functor.map eC.hom)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  erw [reassoc_of% hk, ← reassoc_of% hn]
  rw [← Category.assoc, ← F.functor.map_comp, eC.inv_hom_id,
    F.functor.map_id, Category.id_comp]
  rw [← hq, Category.assoc, q.hom_inv_id]
  erw [Category.comp_id]

end AlgebraicGeometry.Scheme
