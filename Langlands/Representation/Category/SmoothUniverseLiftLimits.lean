import Langlands.Representation.Category.UniverseLiftFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Small limits under smooth carrier lifts

Smooth parts commute with carrier lifts. A small smooth limit is the smooth
part of an algebraic limit; this presentation transfers preservation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX uG uV uW

namespace Langlands

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- An actual representation equivalence restricts to the smooth parts. -/
def smoothPartMapEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : (smoothPart ρ).Equiv (smoothPart σ) :=
  (smoothMap e.toIntertwiningMap).ofBijective
    ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)),
      fun y => ⟨smoothMap e.symm.toIntertwiningMap y, by
        apply Subtype.ext
        exact e.apply_symm_apply y.val⟩⟩

namespace SmoothRep

variable (G)

/-- Interchanging the lifted carrier with the smooth-vector subtype. -/
def universeLiftSmoothPartEquiv (A : Rep.{uV} ℂ G) :
    ((universeLiftFunctor.{uX} G).obj ((smoothPartFunctor ℂ G).obj A)).representation.Equiv
      ((smoothPartFunctor ℂ G).obj ((RepUniverseLift.functor.{uX} G).obj A)).representation :=
  (Langlands.universeLiftEquiv (smoothPart A.ρ)).symm.trans
    (smoothPartMapEquiv (Langlands.universeLiftEquiv A.ρ))

/-- Smooth part and carrier lift commute naturally. -/
def universeLiftSmoothPartIso :
    smoothPartFunctor ℂ G ⋙ universeLiftFunctor.{uX, uG, uV} G ≅
      RepUniverseLift.functor.{uX, uG, uV} G ⋙ smoothPartFunctor ℂ G :=
  NatIso.ofComponents (fun A => mkIso (universeLiftSmoothPartEquiv G A)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    ext x
    rfl)

/-- Raising smooth carrier universes preserves small limits. -/
instance universeLiftFunctor_preservesLimits :
    PreservesLimitsOfSize.{uV, uV} (universeLiftFunctor.{uX, uG, uV} G) where
  preservesLimitsOfShape {J} _ :=
    { preservesLimit := fun {F} => by
        let R : Rep.{uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ G := smoothPartFunctor ℂ G
        let L := (toRep : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uV} ℂ G)
        let U := universeLiftFunctor.{uX, uG, uV} G
        let adj : L ⊣ R := toRepSmoothPartAdjunction ℂ G
        have : PreservesLimitsOfSize.{uV, uV} R := adj.rightAdjoint_preservesLimits
        have : PreservesLimitsOfSize.{uV, uV}
            (smoothPartFunctor.{0, uG, max uV uX} ℂ G) :=
          (toRepSmoothPartAdjunction ℂ G).rightAdjoint_preservesLimits
        have : PreservesLimit (F ⋙ L) (R ⋙ U) :=
          preservesLimit_of_natIso (F ⋙ L) (universeLiftSmoothPartIso G).symm
        have : PreservesLimit ((F ⋙ L) ⋙ R) U :=
          preservesLimit_of_preserves_limit_cone
            (isLimitOfPreserves R (limit.isLimit (F ⋙ L)))
            (isLimitOfPreserves (R ⋙ U) (limit.isLimit (F ⋙ L)))
        exact preservesLimit_of_iso_diagram U
          ((Functor.associator F L R) ≪≫ Functor.isoWhiskerLeft F (asIso adj.unit).symm ≪≫
            F.rightUnitor) }

end SmoothRep
end Langlands
