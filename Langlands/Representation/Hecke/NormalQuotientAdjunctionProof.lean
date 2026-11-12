import Langlands.Representation.Hecke.NormalQuotientStatements
import Langlands.Representation.Induction.QuotientAdjunction
import Langlands.Representation.Smooth.SmoothPart.HomDefinitions

/-! # Quotient coinvariants and closed-subgroup induction adjunctions -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Hecke.Homomorphism

universe uP uG v

section Quotient

variable {P : Type uP} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (N : Subgroup P) [N.Normal]

/-- The algebraic coinvariant adjunction restricts to the actual smooth categories. -/
def normalCoinvariantAdjunction :
    normalCoinvariantFunctor.{0, uP, v} (R := ℂ) N ⊣
      restriction (QuotientGroup.mk' N) QuotientGroup.continuous_mk where
  unit :=
    { app := fun A => ObjectProperty.homMk
        ((Induction.coinvariantsInflationUnit ℂ N).app A.obj)
      naturality := fun A B f => by
        apply ObjectProperty.hom_ext
        exact (Induction.coinvariantsInflationUnit ℂ N).naturality f.hom }
  counit :=
    { app := fun A => ObjectProperty.homMk
        ((Induction.coinvariantsInflationCounit ℂ N).app A.obj)
      naturality := fun A B f => by
        apply ObjectProperty.hom_ext
        exact (Induction.coinvariantsInflationCounit ℂ N).naturality f.hom }
  left_triangle_components A := by
    apply ObjectProperty.hom_ext
    exact (Induction.coinvariantsInflationAdjunction ℂ N).left_triangle_components A.obj
  right_triangle_components A := by
    apply ObjectProperty.hom_ext
    exact (Induction.coinvariantsInflationAdjunction ℂ N).right_triangle_components A.obj

end Quotient

/-- Renard III.2.10, the quotient adjunction for every carrier universe. -/
theorem normalQuotientAdjunctionStatement : NormalQuotientAdjunctionStatement.{uP, v} := by
  intro P _ _ _ _ _ N _ _
  exact ⟨normalCoinvariantAdjunction N⟩

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P : Subgroup G)

/-- Restriction is left adjoint to the existing smooth function induction. -/
def subgroupRestrictionAdjunction :
    restriction.{uG, uG, max uG v} P.subtype continuous_subtype_val ⊣
      (SmoothRep.toRep ⋙ Induction.smoothInductionFunctor P) where
  unit :=
    { app := fun A => SmoothRep.ofHom (smoothLift A.isSmooth
        ((Rep.resCoindAdjunction ℂ P.subtype).unit.app A.obj).hom)
      naturality := fun A B f => by
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        apply Subtype.ext
        funext g
        exact (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g x).symm }
  counit :=
    { app := fun A => SmoothRep.ofHom
        { toFun := fun f => f.val.val 1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          isIntertwining' := fun p => by
            ext f
            change f.val.val (1 * (p : G)) = A.representation p (f.val.val 1)
            simpa using f.val.property p 1 }
      naturality := by
        intros
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        ext
        rfl }
  left_triangle_components A := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext x
    change A.representation 1 x = x
    exact congrArg (fun h : Module.End ℂ A.obj => h x) A.representation.map_one
  right_triangle_components A := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (1 * g) = f.val.val g
    rw [one_mul]

end Induction

/-- Renard III.2.10 Corollary, by composition of the two actual adjunctions. -/
theorem normalQuotientInductionAdjunctionStatement :
    NormalQuotientInductionAdjunctionStatement.{uG, v} := by
  intro G _ _ _ _ _ P _ N _ _
  exact ⟨(subgroupRestrictionAdjunction P).comp (normalCoinvariantAdjunction N)⟩

end Langlands.Hecke.Homomorphism
