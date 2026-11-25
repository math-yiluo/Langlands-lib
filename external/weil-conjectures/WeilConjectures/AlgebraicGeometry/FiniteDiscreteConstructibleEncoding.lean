/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleLocalPiece

/-! # Finite presentations under the common coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_finiteDiscreteConstructibleEncoding
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- A constructible internal module has a constructible ordinary module sheaf
under the sectionwise finite-coefficient encoding.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemma 5.4.1
(auxiliary; not a blueprint node).

Proof in words. Retain the finite stratification in the internal constructibility
hypothesis. On each stratum, normalize the coefficient pullbacks and choose its
finite-presentation cover. Compatibility of the fixed encoding with restriction
and preservation of finite sums and cokernels give presentations between finite
constant module sheaves. The rank-one module has finite carrier by hG. Lift each
presentation map to constant etale sheaves using full faithfulness of comparison
pullback. Their cokernel is finite locally constant by the existing etale theorem;
exact comparison pullback gives finite local constancy of the pro-etale cokernel.
Bind these trivialization covers with the presentation cover. The original
stratification and these finite locally constant restrictions witness intrinsic
constructibility. Empty schemes and covers, rank zero, and the zero ring are
included without additional assumptions. -/
theorem finiteDiscreteCoefficient_constructible [DiscreteTopology B] [Finite B]
    (T : Scheme.{u}) (M : FiniteDiscreteInternalModules B T)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M) :
    ProEtale.IsConstructible (ULift.{u + 1} B)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  -- The local piece now obtains finite presentations through the shared pullback API.
  exact finiteDiscreteCoefficient_local_piece B eR G hG T S a M (hS a)

end AlgebraicGeometry.ProEtale.CondensedRing
