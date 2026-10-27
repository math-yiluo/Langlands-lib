import Langlands.CategoryTheory.EquivariantDiagramLimit
import Langlands.Shimura.Coefficients.AlgebraicCompactCoefficient

/-! # Profinite congruence groups and their continuous actions on level limits -/

noncomputable section

universe u v w z t

namespace Langlands.Shimura.Coefficients

open CategoryTheory Opposite

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

section General

variable {R : Type u} [CommRing R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : CompactOpenLevel G) (I : Ideal R)
variable (M : Action (ModuleCat.{w} R) U.subgroup)
variable (hN : ∀ n : ℕ, IsOpen (congruenceKernel I M n : Set U.subgroup))

local instance : CompactSpace U.subgroup := isCompact_iff_compactSpace.mp U.isCompact

include hN in
/-- The actual quotient topology and compactness imply finiteness of each congruence group. -/
theorem congruenceQuotient_finite (n : ℕ) :
    Finite (U.subgroup ⧸ congruenceKernel I M n) := by
  let _ := QuotientGroup.discreteTopology (hN n)
  exact finite_of_compact_of_discrete

/-- Each actual coefficient congruence quotient is compact and discrete in its quotient topology. -/
def congruenceProfiniteGroup (n : ℕ) : ProfiniteGrp.{v} :=
  let _ := QuotientGroup.discreteTopology (hN n)
  ProfiniteGrp.of (U.subgroup ⧸ congruenceKernel I M n)

/-- The existing inclusion-induced continuous homomorphism, bundled between profinite quotients. -/
def congruenceProfiniteTransition {i j : ℕ} (h : j ≤ i) :
    congruenceProfiniteGroup U I M hN i ⟶ congruenceProfiniteGroup U I M hN j :=
  ConcreteCategory.ofHom (C := ProfiniteGrp)
    (LevelSpace.normalQuotientContinuousMap U.subgroup (congruenceKernel I M i)
      (congruenceKernel_antitone I M h))

/-- The original congruence quotients with their existing quotient topologies form a profinite diagram. -/
def congruenceProfiniteGroups : ℕᵒᵖ ⥤ ProfiniteGrp.{v} where
  obj n := congruenceProfiniteGroup U I M hN n.unop
  map f := congruenceProfiniteTransition U I M hN (leOfHom f.unop)
  map_id n := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    exact DFunLike.congr_fun (torsionCongruenceTransition_refl I M n.unop) x
  map_comp f g := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    exact DFunLike.congr_fun
      (torsionCongruenceTransition_comp I M (leOfHom g.unop) (leOfHom f.unop)).symm x

/-- Forgetting topology gives exactly the coefficient congruence-group diagram. -/
@[simp] theorem congruenceProfiniteGroups_forget :
    congruenceProfiniteGroups U I M hN ⋙ forget₂ ProfiniteGrp GrpCat =
      torsionCongruenceGroups I M :=
  rfl

@[simp] theorem congruenceProfiniteGroups_map_mk {i j : ℕᵒᵖ}
    (f : i ⟶ j) (g : U.subgroup) :
    (congruenceProfiniteGroups U I M hN).map f (QuotientGroup.mk g) =
      QuotientGroup.mk g :=
  rfl

/-- The actual quotient-group transitions are surjective. -/
theorem congruenceProfiniteGroups_map_surjective {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((congruenceProfiniteGroups U I M hN).map f) :=
  torsionCongruenceTransition_surjective I M (leOfHom f.unop)

/-- Mathlib's actual profinite group of compatible congruence-quotient families. -/
abbrev congruenceGroupLimit : ProfiniteGrp.{v} :=
  ProfiniteGrp.limit.{v, 0} (congruenceProfiniteGroups U I M hN)

/-- The continuous coordinate projection from the actual profinite group limit. -/
def congruenceGroupLimitProjection (n : ℕᵒᵖ) :
    congruenceGroupLimit U I M hN →ₜ* U.subgroup ⧸ congruenceKernel I M n.unop :=
  ((ProfiniteGrp.limitCone.{v, 0} (congruenceProfiniteGroups U I M hN)).π.app n).hom

@[simp] theorem congruenceGroupLimitProjection_apply
    (g : congruenceGroupLimit U I M hN) (n : ℕᵒᵖ) :
    congruenceGroupLimitProjection U I M hN n g = g.val n :=
  rfl

/-- The original compact level maps continuously to its congruence-group limit. -/
def congruenceGroupLimitMap : U.subgroup →ₜ* congruenceGroupLimit U I M hN where
  toFun g := ⟨fun _ => QuotientGroup.mk g, by intro i j f; rfl⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact (QuotientGroup.mk' (congruenceKernel I M n.unop)).map_one
  map_mul' g h := by
    apply Subtype.ext
    funext n
    exact (QuotientGroup.mk' (congruenceKernel I M n.unop)).map_mul g h
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun _ => QuotientGroup.continuous_mk

@[simp] theorem congruenceGroupLimitMap_apply (g : U.subgroup) (n : ℕᵒᵖ) :
    (congruenceGroupLimitMap U I M hN g).val n = QuotientGroup.mk g :=
  rfl

/-- Each coordinate of the original-level map is the original continuous quotient map. -/
@[simp] theorem congruenceGroupLimitProjection_comp_map (n : ℕᵒᵖ) :
    (congruenceGroupLimitProjection U I M hN n).comp (congruenceGroupLimitMap U I M hN) =
      LevelSpace.normalQuotientMk U.subgroup (congruenceKernel I M n.unop) :=
  rfl

/-- The kernel is exactly the intersection of the actual coefficient congruence kernels. -/
theorem congruenceGroupLimitMap_ker :
    (congruenceGroupLimitMap U I M hN).toMonoidHom.ker =
      ⨅ n : ℕ, congruenceKernel I M n := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf]
  constructor
  · intro h n
    have hn := congrArg (fun k : congruenceGroupLimit U I M hN => k.val (op n)) h
    exact (QuotientGroup.eq_one_iff g).mp hn
  · intro h
    apply Subtype.ext
    funext n
    exact (QuotientGroup.eq_one_iff g).mpr (h n.unop)

variable {Γ : Type z} {X : Type t} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* G)

/-- The actual compatible level-space limit has a jointly continuous congruence-limit action. -/
def congruenceLevelLimitAction :
    ContAction TopCat.{max v t} (congruenceGroupLimit U I M hN) :=
  EquivariantDiagram.profiniteLimitAction.{v, 0, t}
    (congruenceProfiniteGroups U I M hN)
    (congruenceLevelSpaces (X := X) U I M hN ι)
    (fun n => LevelSpace.normalQuotientAction_isContinuous (X := X) ι U.subgroup
      (congruenceKernel I M n.unop) (hN n.unop))

@[simp] theorem congruenceLevelLimitAction_obj :
    (congruenceLevelLimitAction (X := X) U I M hN ι).obj.V =
      (TopCat.limitCone.{0, max v t}
        (congruenceLevelSpaces (X := X) U I M hN ι).obj).pt :=
  rfl

/-- The limit-space coordinate projections are equivariant along the actual group projections. -/
def congruenceLevelLimitProjection (n : ℕᵒᵖ) :
    congruenceLevelLimitAction (X := X) U I M hN ι ⟶
      (ContAction.res TopCat (congruenceGroupLimitProjection U I M hN n)).obj
        (LevelSpace.normalQuotientContinuousAction (X := X) ι U.subgroup
          (congruenceKernel I M n.unop) (hN n.unop)) :=
  EquivariantDiagram.profiniteLimitProjection.{v, 0, t}
    (congruenceProfiniteGroups U I M hN)
    (congruenceLevelSpaces (X := X) U I M hN ι)
    (fun k => LevelSpace.normalQuotientAction_isContinuous (X := X) ι U.subgroup
      (congruenceKernel I M k.unop) (hN k.unop)) n

@[simp] theorem congruenceLevelLimitProjection_apply (n : ℕᵒᵖ)
    (x : (congruenceLevelLimitAction (X := X) U I M hN ι).obj.V) :
    (congruenceLevelLimitProjection (X := X) U I M hN ι n).hom.hom x = x.val n :=
  rfl

/-- Every limit-action coordinate is the original residual action on that actual quotient space. -/
@[simp] theorem congruenceLevelLimitAction_apply
    (g : congruenceGroupLimit U I M hN)
    (x : (congruenceLevelLimitAction (X := X) U I M hN ι).obj.V) (n : ℕᵒᵖ) :
    (((congruenceLevelLimitAction (X := X) U I M hN ι).obj.ρ g).hom x).val n =
      ((congruenceLevelSpaces (X := X) U I M hN ι).ρ n (g.val n)).hom (x.val n) :=
  rfl

/-- Restrict along the constructed continuous map from the original compact level. -/
def congruenceOriginalLevelLimitAction : ContAction TopCat.{max v t} U.subgroup :=
  (ContAction.res TopCat (congruenceGroupLimitMap U I M hN)).obj
    (congruenceLevelLimitAction (X := X) U I M hN ι)

/-- The restricted limit action is the original inverse-right level action in each coordinate. -/
@[simp] theorem congruenceOriginalLevelLimitAction_apply (g : U.subgroup)
    (x : (congruenceOriginalLevelLimitAction (X := X) U I M hN ι).obj.V) (n : ℕᵒᵖ) :
    (((congruenceOriginalLevelLimitAction (X := X) U I M hN ι).obj.ρ g).hom x).val n =
      ((LevelSpace.normalLevelAction (X := X) ι U.subgroup
        (congruenceKernel I M n.unop)).ρ g).hom (x.val n) :=
  rfl

end General

section AlgebraicCompact

open Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
variable (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ) (hm : m ≠ 0)

/-- The actual algebraic compact coefficient congruence groups in their quotient topologies. -/
def algebraicCompactCongruenceProfiniteGroups : ℕᵒᵖ ⥤ ProfiniteGrp.{u} :=
  congruenceProfiniteGroups U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun n => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1)

/-- The topological diagram has exactly the groups used by the algebraic coefficient diagram. -/
@[simp] theorem algebraicCompactCongruenceProfiniteGroups_forget :
    algebraicCompactCongruenceProfiniteGroups ρ p l U m hm ⋙ forget₂ ProfiniteGrp GrpCat =
      (algebraicCompactCoefficientLattice ρ p l U).rationalCongruenceGroups m :=
  rfl

/-- The constructed profinite group of compatible actual algebraic congruence quotients. -/
abbrev algebraicCompactCongruenceGroupLimit : ProfiniteGrp.{u} :=
  ProfiniteGrp.limit.{u, 0} (algebraicCompactCongruenceProfiniteGroups ρ p l U m hm)

/-- The continuous map from the original compact adelic level, without a continuity input. -/
def algebraicCompactCongruenceGroupLimitMap :
    U.subgroup →ₜ* algebraicCompactCongruenceGroupLimit ρ p l U m hm :=
  congruenceGroupLimitMap U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun n => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1)

@[simp] theorem algebraicCompactCongruenceGroupLimitMap_apply
    (g : U.subgroup) (n : ℕᵒᵖ) :
    (algebraicCompactCongruenceGroupLimitMap ρ p l U m hm g).val n =
      QuotientGroup.mk g :=
  rfl

/-- The actual continuous projection to the coefficient congruence group at exponent n. -/
def algebraicCompactCongruenceGroupLimitProjection (n : ℕᵒᵖ) :
    algebraicCompactCongruenceGroupLimit ρ p l U m hm →ₜ*
      (algebraicCompactCoefficientLattice ρ p l U).RationalCongruenceGroup m n.unop :=
  congruenceGroupLimitProjection U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun k => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm k).1) n

@[simp] theorem algebraicCompactCongruenceGroupLimitProjection_apply
    (g : algebraicCompactCongruenceGroupLimit ρ p l U m hm) (n : ℕᵒᵖ) :
    algebraicCompactCongruenceGroupLimitProjection ρ p l U m hm n g = g.val n :=
  rfl

/-- The original-level map has exactly the intersection of the actual coefficient kernels. -/
theorem algebraicCompactCongruenceGroupLimitMap_ker :
    (algebraicCompactCongruenceGroupLimitMap ρ p l U m hm).toMonoidHom.ker =
      ⨅ n : ℕ, congruenceKernel (coefficientScalarIdeal l m)
        (algebraicCompactCoefficientLattice ρ p l U).action n :=
  congruenceGroupLimitMap_ker U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun k => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm k).1)

variable {Γ : Type z} {X : Type t} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* σ.FiniteAdelicPoints)

/-- The profinite algebraic congruence group acts continuously on the actual level-space limit. -/
def algebraicCompactCongruenceLimitAction :
    ContAction TopCat.{max u t} (algebraicCompactCongruenceGroupLimit ρ p l U m hm) :=
  congruenceLevelLimitAction (X := X) U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun n => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1) ι

/-- The action uses the actual compatible-family space of the published algebraic level diagram. -/
@[simp] theorem algebraicCompactCongruenceLimitAction_obj :
    (algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι).obj.V =
      (TopCat.limitCone.{0, max u t}
        (algebraicCompactCongruenceSpaces (X := X) ρ p l U m hm ι).obj).pt :=
  rfl

/-- Each limit-space projection is equivariant along its actual group-limit projection. -/
def algebraicCompactCongruenceLimitProjection (n : ℕᵒᵖ) :
    algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι ⟶
      (ContAction.res TopCat
        (algebraicCompactCongruenceGroupLimitProjection ρ p l U m hm n)).obj
          (LevelSpace.normalQuotientContinuousAction (X := X) ι U.subgroup
            (congruenceKernel (coefficientScalarIdeal l m)
              (algebraicCompactCoefficientLattice ρ p l U).action n.unop)
            (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n.unop).1) :=
  congruenceLevelLimitProjection (X := X) U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun k => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm k).1) ι n

@[simp] theorem algebraicCompactCongruenceLimitProjection_apply (n : ℕᵒᵖ)
    (x : (algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι).obj.V) :
    (algebraicCompactCongruenceLimitProjection (X := X) ρ p l U m hm ι n).hom.hom x =
      x.val n :=
  rfl

/-- Limit translation in every coordinate is the published actual residual action. -/
@[simp] theorem algebraicCompactCongruenceLimitAction_apply
    (g : algebraicCompactCongruenceGroupLimit ρ p l U m hm)
    (x : (algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι).obj.V)
    (n : ℕᵒᵖ) :
    (((algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι).obj.ρ g).hom x).val n =
      ((algebraicCompactCongruenceSpaces (X := X) ρ p l U m hm ι).ρ n (g.val n)).hom
        (x.val n) :=
  rfl

/-- The continuous original-level action is restriction along the constructed adelic-level map. -/
def algebraicCompactOriginalLevelLimitAction : ContAction TopCat.{max u t} U.subgroup :=
  (ContAction.res TopCat (algebraicCompactCongruenceGroupLimitMap ρ p l U m hm)).obj
    (algebraicCompactCongruenceLimitAction (X := X) ρ p l U m hm ι)

/-- Restriction recovers the original inverse-right level action in each coordinate. -/
@[simp] theorem algebraicCompactOriginalLevelLimitAction_apply (g : U.subgroup)
    (x : (algebraicCompactOriginalLevelLimitAction (X := X) ρ p l U m hm ι).obj.V)
    (n : ℕᵒᵖ) :
    (((algebraicCompactOriginalLevelLimitAction (X := X) ρ p l U m hm ι).obj.ρ g).hom x).val n =
      ((LevelSpace.normalLevelAction (X := X) ι U.subgroup
        (congruenceKernel (coefficientScalarIdeal l m)
          (algebraicCompactCoefficientLattice ρ p l U).action n.unop)).ρ g).hom (x.val n) :=
  rfl

end AlgebraicCompact

end Langlands.Shimura.Coefficients
