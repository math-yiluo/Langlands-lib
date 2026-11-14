import Langlands.Representation.CuspidalSupport.BernsteinBlockCenterFunctionsInvariantCenter
import Langlands.Representation.CuspidalSupport.BernsteinBlockCenterFunctionsLevi
import Langlands.Representation.CuspidalSupport.InducedCenterCriterion
import Langlands.Representation.CuspidalSupport.RationalSummandTwistSeparation
import Langlands.Representation.CuspidalSupport.RationalSummandInductionMembership
import Langlands.Representation.CuspidalSupport.RationalSummandInductionSupercuspidal
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport

/-! # `ℨ_D^{W(D)} ⊂ ℨ_Ω` (Renard VI.10.4, proof of the Theorem): proof -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinInvCenterInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinInvCenterInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinInvCenterInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinInvCenterInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinInvCenterInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinInvCenterInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinInvCenterInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- An irreducible quotient of `Π_D` is an unramified twist of `ρ` (`Π_D` lies in the block of
`ρ`, `rationalSummandInduction_mem_block`). -/
theorem bernsteinSummand_exists_twist_iso_of_surjective
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)))
    (hτ : τ.IsIrreducible)
    (V : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶ τ)
    (hV : Function.Surjective (SmoothRep.hom V)) :
    ∃ χ : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul),
      Nonempty (τ ≅ rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) χ
        a.representation) := by
  let M := bernsteinLeviScheme i ν a.roots
  have hM := (bernsteinStandardRepresentativesGeometric i ν family a.roots).2.1.isConnectedReductive
  have hblock := rationalSummandInduction_mem_block M hM a.representation a.irreducible ρ₀ hρ₀
    j hj
  have hsub : SmoothRep.IsSubquotient τ
      (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) :=
    SmoothRep.IsQuotient.isSubquotient ⟨V, hV⟩
  obtain ⟨χ, ⟨e₁⟩⟩ := hblock τ hτ hsub
  exact ⟨χ, ⟨e₁ ≪≫ (SmoothRep.twistFunctor _ (isOpen_rationalUnramifiedCharacter_ker M χ)).mapIso
    (SmoothRep.mkIso (SmoothRep.universeLiftEquiv a.representation) :
      a.representation ≅ rationalInertiaBaseLift M a.representation).symm⟩⟩

/-- A central `ζ` of `End(Π_D)` acts on all maps `Π_D → ρ ⊗ ω` by one scalar `s(ω)`
(Renard VI.4.4, `bernsteinLeviCenterVarietyStatement_holds`). -/
theorem bernsteinSummandCenter_exists_scalar
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
    (hζc : ζ ∈ Subring.center
      (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))) :
    ∃ s : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ,
      ∀ ω (φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation),
        ζ ≫ φ = s ω • φ := by
  obtain ⟨Ψ, -, -, hΨ⟩ :=
    bernsteinLeviCenterVarietyStatement_holds.{uF, uV} F G T i ν family a ρ₀ hρ₀ j hj
  let ζ' : Subalgebra.center ℂ
      (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) :=
    ⟨ζ, Subalgebra.mem_center_iff.mpr fun g => (Subring.mem_center_iff
      (R := End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))).mp
        hζc g⟩
  exact ⟨Ψ ζ', fun ω φ => hΨ ζ' ω φ⟩

/-- The composite `U ∘ T` of a map `U : Π_D → ρ ⊗ ω` with a linear `T : Π_D → Π_D` satisfying
`T ∘ Π_D(m) = Π_D(φ m) ∘ T` is a map `Π_D → c^*(ρ ⊗ ω)`. -/
def bernsteinSummandTwistedHom
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν a.roots)))
    (Tl : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ →ₗ[ℂ]
      rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
    (hT : ∀ (m : rationalPoints (bernsteinLeviScheme i ν a.roots))
        (x : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀),
      Tl ((rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          m x) =
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          (rationalPoints.map c.iso.hom m) (Tl x))
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (U : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
      rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation) :
    rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
      rationalIsoPullback c.iso
        (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation) :=
  SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom U).toLinearMap ∘ₗ Tl
      isIntertwining' := fun m => LinearMap.ext fun x => by
        change SmoothRep.hom U (Tl ((rationalNormKernelSummandInduction
            (bernsteinLeviScheme i ν a.roots) ρ₀).representation m x)) =
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω
            a.representation).representation (rationalPoints.map c.iso.hom m)
            (SmoothRep.hom U (Tl x))
        rw [hT]
        exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom U) _ _ }

/-- One map `U : Π_D → ρ ⊗ ω` does not distinguish `T ∘ ζ` from `ζ ∘ T`
(see `bernsteinSummandCenter_comm_twisted`). -/
theorem bernsteinSummandCenter_hom_comm_twisted
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
    (s : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ)
    (hs : ∀ ω (φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation),
        ζ ≫ φ = s ω • φ)
    (c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν a.roots)))
    (hinv : ∀ χ ω : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) χ a.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)) →
      ∀ φ' : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation,
          ζ ≫ φ' = s χ • φ')
    (Tl : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ →ₗ[ℂ]
      rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
    (hT : ∀ (m : rationalPoints (bernsteinLeviScheme i ν a.roots))
        (x : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀),
      Tl ((rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          m x) =
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          (rationalPoints.map c.iso.hom m) (Tl x))
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (U : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
      rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)
    (v : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) :
    SmoothRep.hom U (Tl (SmoothRep.hom ζ v)) = SmoothRep.hom U (SmoothRep.hom ζ (Tl v)) := by
  let V := bernsteinSummandTwistedHom.{uF, uV} i ν family a ρ₀ c Tl hT ω U
  have hVx (x : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) :
      SmoothRep.hom V x = SmoothRep.hom U (Tl x) := rfl
  have hUω : SmoothRep.hom U (SmoothRep.hom ζ (Tl v)) = s ω • SmoothRep.hom U (Tl v) :=
    congrArg (fun g => SmoothRep.hom g (Tl v)) (hs ω U)
  by_cases hV0 : SmoothRep.hom V = 0
  · have h1 : SmoothRep.hom U (Tl (SmoothRep.hom ζ v)) = 0 := by
      rw [← hVx, hV0]
      rfl
    have h2 : SmoothRep.hom U (Tl v) = 0 := by
      rw [← hVx, hV0]
      rfl
    rw [h1, hUω, h2, smul_zero]
  · have hτirr : (rationalIsoPullback c.iso
        (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω
          a.representation)).representation.IsIrreducible :=
      (SmoothRep.isIrreducible_pullbackFunctor_obj_iff (rationalPointIso c.iso)
        (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)).mpr
        ((isIrreducible_rationalUnramifiedTwist_iff (bernsteinLeviScheme i ν a.roots) ω
          a.representation).mpr a.irreducible)
    have hVsurj : Function.Surjective (SmoothRep.hom V) :=
      (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom V)).resolve_right hV0
    obtain ⟨χ, ⟨e⟩⟩ := bernsteinSummand_exists_twist_iso_of_surjective.{uF, uV} i ν family a ρ₀
      hρ₀ j hj _ hτirr V hVsurj
    have hU := hinv χ ω ⟨e.symm⟩ U
    have hVζ : ζ ≫ V = s χ • V := by
      have h := hs χ (V ≫ e.hom)
      rw [← Category.assoc, ← Linear.smul_comp] at h
      exact (Iso.cancel_iso_hom_right _ _ e).mp h
    have h1 : SmoothRep.hom U (Tl (SmoothRep.hom ζ v)) = s χ • SmoothRep.hom U (Tl v) :=
      congrArg (fun g => SmoothRep.hom g v) hVζ
    have h2 : SmoothRep.hom U (SmoothRep.hom ζ (Tl v)) = s χ • SmoothRep.hom U (Tl v) :=
      congrArg (fun g => SmoothRep.hom g (Tl v)) hU
    rw [h1, h2]

/-- The twisted-commutation input of `leviInduction_map_mem_center_of_twistedCommutation` for
`Π_D`. Let `c = (w, φ)` conjugate the Levi `M` of `a` to itself and `T : Π_D → Π_D` be linear
with `T ∘ Π_D(m) = Π_D(φ m) ∘ T`. If the scalars of `ζ` on the maps `Π_D → ρ ⊗ ω` are invariant
under association, then `T ∘ ζ = ζ ∘ T`. For a map `U : Π_D → ρ ⊗ ω`, `U ∘ T` is a map
`Π_D → c^*(ρ ⊗ ω)`; if it is nonzero, `c^*(ρ ⊗ ω)` is an irreducible quotient of `Π_D`, hence
`≅ ρ ⊗ χ` with `χ ~ ω`, and both `U ∘ T ∘ ζ` and `U ∘ ζ ∘ T` are `s(χ) • U ∘ T`. The maps `U`
separate the vectors of `Π_D`. -/
theorem bernsteinSummandCenter_comm_twisted
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (ζ : End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
    (hζc : ζ ∈ Subring.center
      (End (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))
    (hinv : ∀ ω ω' : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul),
      (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
          (Standard.leviHom i ν (rootSet i ν a.roots)),
        Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω' a.representation))) →
      ∀ c : ℂ, (∀ φ : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation,
          ζ ≫ φ = c • φ) →
        ∀ φ' : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ ⟶
          rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω' a.representation,
          ζ ≫ φ' = c • φ')
    (c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
      (Standard.leviHom i ν (rootSet i ν a.roots)))
    (Tl : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ →ₗ[ℂ]
      rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)
    (hT : ∀ (m : rationalPoints (bernsteinLeviScheme i ν a.roots))
        (x : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀),
      Tl ((rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          m x) =
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀).representation
          (rationalPoints.map c.iso.hom m) (Tl x))
    (v : rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) :
    Tl (SmoothRep.hom ζ v) = SmoothRep.hom ζ (Tl v) := by
  obtain ⟨s, hs⟩ :=
    bernsteinSummandCenter_exists_scalar.{uF, uV} i ν family a ρ₀ hρ₀ j hj ζ hζc
  apply sub_eq_zero.mp
  refine rationalNormKernelSummandInduction_eq_zero_of_forall_twist.{uF, max uF uV}
    (bernsteinLeviScheme i ν a.roots) ρ₀ a.representation (SmoothRep.hom j) hj _ fun ω U => ?_
  rw [map_sub, sub_eq_zero]
  exact bernsteinSummandCenter_hom_comm_twisted.{uF, uV} i ν family a ρ₀ hρ₀ j hj ζ s hs c
    (fun χ ω' he => hinv χ ω' ⟨c, he⟩ (s χ) (hs χ)) Tl hT ω U v

/-- Renard VI.10.4, proof of the Theorem: `ℨ_D^{W(D)} ⊂ ℨ_Ω`. The criterion
`leviInduction_map_mem_center_of_twistedCommutation` (Frobenius reciprocity and the support
filtration of `r_P(i_P Π_D)`) applies to `Π_D`, which is supercuspidal and has no nonzero vector
fixed by an element none of whose positive powers lies in `⁰M(F)`; its twisted-commutation
input is `bernsteinSummandCenter_comm_twisted`. -/
theorem bernsteinInvariantCenterInclusion :
    BernsteinInvariantCenterInclusionStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj X twist Assoc piD I ζ hζc hinv
  have : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  let A := bernsteinStandardRepresentativesGeometric i ν family a.roots
  refine RepresentedParabolic.leviInduction_map_mem_center_of_twistedCommutation.{uF, uV}
    (p := Standard.parabolicHom i ν (rootSet i ν a.roots))
    (l := Standard.leviToParabolic i ν (rootSet i ν a.roots))
    (r := Standard.unipotentToParabolic i ν (rootSet i ν a.roots))
    (hp := A.1) (hr := A.2.2.1) (hl := A.2.1) (hmul := A.2.2.2)
    family.connectedReductive piD ?_ ?_ ζ hζc fun w φ hφ Tl hT v => ?_
  · -- `Π_D` is supercuspidal.
    have := A.2.1.isConnectedReductive.isAffineHom
    let := RepresentedParabolic.leviPointTopology
      (Standard.leviToParabolic i ν (rootSet i ν a.roots)) A.2.1
    have := RepresentedParabolic.leviPoints_locallyCompactSpace
      (Standard.parabolicHom i ν (rootSet i ν a.roots))
      (Standard.leviToParabolic i ν (rootSet i ν a.roots)) A.1 A.2.1
    have := RepresentedParabolic.leviPoints_nonarchimedeanGroup
      (Standard.parabolicHom i ν (rootSet i ν a.roots))
      (Standard.leviToParabolic i ν (rootSet i ν a.roots)) A.1 A.2.1
    exact RepresentedParabolic.isSupercuspidal_rationalNormKernelSummandInduction
      a.representation (a.isSupercuspidal i ν family) ρ₀ j hj
  · -- No nonzero vector of `Π_D` is fixed by an element with no positive power in `⁰M(F)`.
    have := A.2.1.isConnectedReductive.isAffineHom
    let := RepresentedParabolic.leviPointTopology
      (Standard.leviToParabolic i ν (rootSet i ν a.roots)) A.2.1
    have := RepresentedParabolic.leviPoints_nonarchimedeanGroup
      (Standard.parabolicHom i ν (rootSet i ν a.roots))
      (Standard.leviToParabolic i ν (rootSet i ν a.roots)) A.1 A.2.1
    intro t ht v hv
    exact Induction.compactInduced_eq_zero_of_fixed
      (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))
      (isOpen_rationalCommonNormKernel _) _ t ht v hv
  have hc : Standard.leviHom i ν (rootSet i ν a.roots) ≫ (G.innerIso w).hom =
      φ.hom ≫ Standard.leviHom i ν (rootSet i ν a.roots) := by
    rw [← Standard.leviToParabolic_comp, Category.assoc, ← hφ]
  exact bernsteinSummandCenter_comm_twisted.{uF, uV} i ν family a ρ₀ hρ₀ j hj ζ hζc hinv
    ⟨w, φ, hc⟩ Tl hT v

end Langlands.CuspidalSupport
