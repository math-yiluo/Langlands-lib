import Langlands.Sheaf.Equivariant.TwistedPointProductExact
import Langlands.Sheaf.Equivariant.TwistedExactGodement

/-! # The actual smooth Godement term as an independent point product -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits LocalActionSystem

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasAdmissibleRefinements (twistedTopology ρ J)]
variable {I : Type w} (points : I → J.Point.{w})
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The actual point fibers of the restriction, presented as a discrete coefficient diagram. -/
def smoothGodementCoefficientFunctor :
    L.SmoothSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      (Discrete I ⥤ ModuleCat.{w} R) :=
  L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
    restriction ρ J (ModuleCat R) ⋙ PointProduct.fiberFunctor points (ModuleCat R) ⋙
      (piEquivalenceFunctorDiscrete I (ModuleCat R)).functor

/-- The restricted actual smooth Godement functor is the actual restricted smooth point
product applied to its coefficient diagram. -/
def restrictedSmoothGodementPointProductIso :
    exactZeroFunctor ρ J points R
        (L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J))
        (smoothCoreflector L (twistedTopology ρ J)) ⋙
      L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat R) ≅
      smoothGodementCoefficientFunctor ρ J L points R ⋙
        coefficientRestrictedSmoothPointProductFunctor ρ J L points R :=
  Functor.isoWhiskerLeft
    (L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat R))
    (Functor.isoWhiskerRight (PointProduct.godementZeroIso points (ModuleCat R))
      (induction ρ J (ModuleCat R) ⋙ smoothCoreflector L (twistedTopology ρ J) ⋙
        L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
          restriction ρ J (ModuleCat R)))

end Langlands.Sheaf.Equivariant.TwistedOver
