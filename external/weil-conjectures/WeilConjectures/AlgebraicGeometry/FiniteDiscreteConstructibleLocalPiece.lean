/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteConstantCokernel
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation

/-! # One stratum of finite discrete coefficient constructibility -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_finiteDiscreteConstructibleLocalPiece
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

open AlgebraicGeometry.ProEtale in
private lemma finiteLocallyConstant_of_cover {Λ : Type (u + 1)} [CommRing Λ]
    {X : AlgebraicGeometry.Scheme.{u}}
    (F : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (C : AlgebraicGeometry.Scheme.Cover.{u}
      AlgebraicGeometry.Scheme.proetalePrecoverage X)
    (hC : ∀ i : C.I₀, AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant Λ
      (((C.f i)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant Λ F := by
  classical
  choose I W g hg h using hC
  let D (i : C.I₀) : AlgebraicGeometry.Scheme.Cover.{u + 1}
      AlgebraicGeometry.Scheme.proetalePrecoverage (C.X i) :=
    ⟨⟨I i, W i, g i⟩, hg i⟩
  let E := C.bind D
  refine ⟨E.I₀, E.X, E.f, E.mem₀, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := h i j
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (AlgebraicGeometry.ProEtale.upperStarComp (ModuleCat.{u + 1} Λ)
    (g i j) (C.f i)).app F ≪≫ e

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

/-- A locally finitely presented internal module on one stratum is sent by the
sectionwise finite coefficient encoding to a finite locally constant ordinary
module sheaf. This is the finite presentation and locally constant matrix step
in Proposition 5.3.2 and Lemmas 5.4.1, 5.4.3 of Bhatt--Scholze.
(auxiliary; not a blueprint node)

Proof in words. Choose the presentation cover from the encoded-presentation
theorem. On each member the ordinary restriction is a cokernel between finite
constant sheaves. Full faithfulness and exactness of etale comparison transport
the proved etale finite locally constant cokernel theorem to this cokernel.
Choose its finite constant trivialization cover and bind it with the presentation
cover. Inverse-image composition identifies the resulting restrictions. The
bound family gives the required finite locally constant witness on the stratum. -/
theorem finiteDiscreteCoefficient_local_piece [DiscreteTopology B] [Finite B]
    (T : Scheme.{u}) (S : Scheme.Stratification T) (a : Fin S.n)
    (M : FiniteDiscreteInternalModules B T)
    (hM : IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T))
      (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M)) :
    IsFiniteLocallyConstant (ULift.{u + 1} B)
      (((S.immersion a)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M)) := by
  obtain ⟨C, hC⟩ := finiteDiscreteCoefficient_encoded_presentation B eR G hG
    T (S.domain a) (S.immersion a) M hM
  apply finiteLocallyConstant_of_cover _ C
  intro i
  obtain ⟨P, Q, hP, hQ, f, ⟨e⟩⟩ := hC i
  exact isFiniteLocallyConstant_of_iso e.symm
    (isFiniteLocallyConstant_cokernel_constant (C.X i) P Q f)

end AlgebraicGeometry.ProEtale.CondensedRing
