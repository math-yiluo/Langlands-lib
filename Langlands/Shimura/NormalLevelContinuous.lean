import Langlands.Shimura.Coefficients.CongruenceLevels
import Langlands.CategoryTheory.TopCatSelfForget
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Jointly continuous actions on open normal-level spaces -/

noncomputable section

universe u v w z t

namespace Langlands.Shimura

open CategoryTheory Opposite

namespace LevelSpace

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {Γ : Type u} {G : Type v} {X : Type w}
variable [Group Γ] [Group G] [MulAction Γ X]
variable [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ι : Γ →* G) (U : Subgroup G) (N : Subgroup U) [N.Normal]

/-- The actual quotient map, with the quotient topology. -/
def normalQuotientMk : U →ₜ* U ⧸ N :=
  ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩

/-- The inclusion-induced quotient homomorphism is continuous without openness assumptions. -/
def normalQuotientContinuousMap {P : Subgroup U} [P.Normal] (h : N ≤ P) :
    U ⧸ N →ₜ* U ⧸ P where
  toMonoidHom := normalQuotientMap U N h
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    QuotientGroup.continuous_mk

omit [IsTopologicalGroup G] in
@[simp] theorem normalQuotientContinuousMap_mk {P : Subgroup U} [P.Normal]
    (h : N ≤ P) (g : U) :
    normalQuotientContinuousMap U N h (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

/-- Openness of the relative normal level makes the residual action jointly continuous. -/
theorem normalQuotientAction_isContinuous (hN : IsOpen (N : Set U)) :
    (normalQuotientAction (X := X) ι U N).IsContinuous := by
  let _ := QuotientGroup.discreteTopology hN
  apply (Action.isContinuous_def _).mpr
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact ((normalQuotientAction (X := X) ι U N).ρ g).hom.continuous

/-- The existing residual action, now certified in Mathlib's continuous-action category. -/
def normalQuotientContinuousAction (hN : IsOpen (N : Set U)) :
    ContAction TopCat.{max v w} (U ⧸ N) :=
  ⟨normalQuotientAction (X := X) ι U N,
    normalQuotientAction_isContinuous (X := X) ι U N hN⟩

@[simp] theorem normalQuotientContinuousAction_obj (hN : IsOpen (N : Set U)) :
    (normalQuotientContinuousAction (X := X) ι U N hN).obj =
      normalQuotientAction (X := X) ι U N := rfl

/-- Pull back along the continuous quotient map to obtain the original level action. -/
def normalContinuousAction (hN : IsOpen (N : Set U)) :
    ContAction TopCat.{max v w} U :=
  ⟨normalLevelAction (X := X) ι U N,
    ((ContAction.res TopCat (normalQuotientMk U N)).obj
      (normalQuotientContinuousAction (X := X) ι U N hN)).property⟩

@[simp] theorem normalContinuousAction_obj (hN : IsOpen (N : Set U)) :
    (normalContinuousAction (X := X) ι U N hN).obj =
      normalLevelAction (X := X) ι U N := rfl

/-- Forgetting an open normal level is equivariant for continuous residual actions. -/
def normalContinuousCoverMap (hN : IsOpen (N : Set U))
    {P : Subgroup U} [P.Normal] (hP : IsOpen (P : Set U)) (h : N ≤ P) :
    normalQuotientContinuousAction (X := X) ι U N hN ⟶
      (ContAction.res TopCat (normalQuotientContinuousMap U N h)).obj
        (normalQuotientContinuousAction (X := X) ι U P hP) :=
  ObjectProperty.homMk (normalCoverMap (X := X) ι U N h)

/-- The same forgetful map, retaining the fixed original level group. -/
def normalContinuousLevelMap (hN : IsOpen (N : Set U))
    {P : Subgroup U} [P.Normal] (hP : IsOpen (P : Set U)) (h : N ≤ P) :
    normalContinuousAction (X := X) ι U N hN ⟶
      normalContinuousAction (X := X) ι U P hP :=
  ObjectProperty.homMk
    { hom := (normalCoverMap (X := X) ι U N h).hom
      comm g := (normalCoverMap (X := X) ι U N h).comm (QuotientGroup.mk g) }

@[simp] theorem normalContinuousLevelMap_hom (hN : IsOpen (N : Set U))
    {P : Subgroup U} [P.Normal] (hP : IsOpen (P : Set U)) (h : N ≤ P) :
    (normalContinuousLevelMap (X := X) ι U N hN hP h).hom.hom =
      (normalCoverMap (X := X) ι U N h).hom := rfl

@[simp] theorem normalContinuousLevelMap_refl (hN : IsOpen (N : Set U)) :
    normalContinuousLevelMap (X := X) ι U N hN hN (le_refl N) =
      𝟙 (normalContinuousAction (X := X) ι U N hN) := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  exact normalCoverMap_refl (X := X) ι U N

@[reassoc] theorem normalContinuousLevelMap_comp (hN : IsOpen (N : Set U))
    {P Q : Subgroup U} [P.Normal] [Q.Normal]
    (hP : IsOpen (P : Set U)) (hQ : IsOpen (Q : Set U)) (h : N ≤ P) (h' : P ≤ Q) :
    normalContinuousLevelMap (X := X) ι U N hN hP h ≫
        normalContinuousLevelMap (X := X) ι U P hP hQ h' =
      normalContinuousLevelMap (X := X) ι U N hN hQ (h.trans h') := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  exact normalCoverMap_comp (X := X) ι U N h h'

end LevelSpace

namespace Coefficients

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

section General

variable {R : Type u} [CommRing R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : CompactOpenLevel G) (I : Ideal R)
variable (M : Action (ModuleCat.{w} R) U.subgroup)
variable (hN : ∀ n : ℕ, IsOpen (congruenceKernel I M n : Set U.subgroup))
variable {Γ : Type z} {X : Type t} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* G)

/-- All congruence spaces form an inverse diagram with a jointly continuous fixed-level action. -/
def congruenceContinuousLevelSpaces : ℕᵒᵖ ⥤ ContAction TopCat.{max v t} U.subgroup where
  obj n := LevelSpace.normalContinuousAction (X := X) ι U.subgroup
    (congruenceKernel I M n.unop) (hN n.unop)
  map f := LevelSpace.normalContinuousLevelMap (X := X) ι U.subgroup
    (congruenceKernel I M _) (hN _) (hN _)
    (congruenceKernel_antitone I M (leOfHom f.unop))
  map_id n := LevelSpace.normalContinuousLevelMap_refl (X := X) ι U.subgroup
    (congruenceKernel I M n.unop) (hN n.unop)
  map_comp f g :=
    (LevelSpace.normalContinuousLevelMap_comp (X := X) ι U.subgroup
      (congruenceKernel I M _) (hN _) (hN _) (hN _)
      (congruenceKernel_antitone I M (leOfHom f.unop))
      (congruenceKernel_antitone I M (leOfHom g.unop))).symm

@[simp] theorem congruenceContinuousLevelSpaces_obj (n : ℕᵒᵖ) :
    ((congruenceContinuousLevelSpaces (X := X) U I M hN ι).obj n).obj =
      LevelSpace.normalLevelAction (X := X) ι U.subgroup (congruenceKernel I M n.unop) :=
  rfl

@[simp] theorem congruenceContinuousLevelSpaces_map_mk {i j : ℕᵒᵖ}
    (f : i ⟶ j) (x : X × G) :
    ((congruenceContinuousLevelSpaces (X := X) U I M hN ι).map f).hom.hom
        (LevelSpace.mk (congruenceLevel U I M hN i.unop).subgroup x) =
      LevelSpace.mk (congruenceLevel U I M hN j.unop).subgroup x :=
  LevelSpace.normalCoverMap_mk (X := X) ι U.subgroup
    (congruenceKernel I M _) (congruenceKernel_antitone I M (leOfHom f.unop)) x

end General

section HarrisCoefficients

open Langlands.Global
open scoped TensorProduct

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
variable (U : CompactOpenLevel σ.FiniteAdelicPoints)

local instance : TopologicalSpace (FiniteCompletion L l ⊗[L] W) := coefficientTopology L l W

variable (hρ : ∀ x : FiniteCompletion L l ⊗[L] W,
  Continuous (fun g : (σ.baseChange L).Points (FiniteCompletion L l) =>
    ρ.act (FiniteCompletion L l) g x))
variable (m : ℕ) (hm : m ≠ 0)
variable {Γ : Type v} {X : Type w} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* σ.FiniteAdelicPoints)

/-- The actual compact coefficient congruence spaces with jointly continuous original-level action. -/
def compactCoefficientContinuousLevelSpaces :
    ℕᵒᵖ ⥤ ContAction TopCat.{max u w} U.subgroup :=
  congruenceContinuousLevelSpaces (X := X) U (coefficientScalarIdeal l m)
    (compactStableCoefficientLattice ρ p l U hρ).action
    (fun n => (compactCoefficient_congruenceKernel ρ p l U hρ m hm n).1) ι

end HarrisCoefficients

end Coefficients
end Langlands.Shimura
