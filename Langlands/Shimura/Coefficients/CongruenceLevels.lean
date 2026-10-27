import Langlands.Shimura.NormalLevelCover
import Langlands.Shimura.Coefficients.CongruenceDiagram

/-! # Actual compact congruence levels and their equivariant space tower -/

noncomputable section

universe u v w z t

namespace Langlands.Shimura

open CategoryTheory Opposite

namespace CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : CompactOpenLevel G) (N : Subgroup U.subgroup)

/-- An open subgroup of a compact open level is an actual ambient compact open level. -/
def sublevel (hN : IsOpen (N : Set U.subgroup)) : CompactOpenLevel G where
  openSubgroup :=
    { toSubgroup := LevelSpace.sublevelSubgroup U.subgroup N
      isOpen' := by
        change IsOpen (N.map U.subgroup.subtype : Set G)
        rw [Subgroup.coe_map]
        exact U.openSubgroup.isOpen.isOpenMap_subtype_val _ hN }
  isCompact := by
    let H : OpenSubgroup G :=
      { toSubgroup := LevelSpace.sublevelSubgroup U.subgroup N
        isOpen' := by
          change IsOpen (N.map U.subgroup.subtype : Set G)
          rw [Subgroup.coe_map]
          exact U.openSubgroup.isOpen.isOpenMap_subtype_val _ hN }
    exact U.isCompact.of_isClosed_subset H.isClosed (LevelSpace.sublevelSubgroup_le _ _)

@[simp] theorem sublevel_subgroup (hN : IsOpen (N : Set U.subgroup)) :
    (sublevel U N hN).subgroup = LevelSpace.sublevelSubgroup U.subgroup N := rfl

/-- The actual ambient inclusion back into the original compact open level. -/
def sublevelInclusion (hN : IsOpen (N : Set U.subgroup)) : sublevel U N hN ⟶ U :=
  inclusion (LevelSpace.sublevelSubgroup_le U.subgroup N)

end CompactOpenLevel

namespace Coefficients

section General

variable {R : Type u} [CommRing R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : CompactOpenLevel G) (I : Ideal R)
variable (M : Action (ModuleCat.{w} R) U.subgroup)
variable (hN : ∀ n : ℕ, IsOpen (congruenceKernel I M n : Set U.subgroup))

/-- The actual compact open ambient level given by a coefficient congruence kernel. -/
def congruenceLevel (n : ℕ) : CompactOpenLevel G :=
  U.sublevel (congruenceKernel I M n) (hN n)

@[simp] theorem congruenceLevel_subgroup (n : ℕ) :
    (congruenceLevel U I M hN n).subgroup =
      LevelSpace.sublevelSubgroup U.subgroup (congruenceKernel I M n) := rfl

/-- Higher coefficient powers give finer compact open ambient levels. -/
def congruenceLevelMap {i j : ℕ} (h : i ≤ j) :
    congruenceLevel U I M hN j ⟶ congruenceLevel U I M hN i :=
  CompactOpenLevel.inclusion
    (LevelSpace.sublevelSubgroup_mono U.subgroup (congruenceKernel_antitone I M h))

/-- The constructed ambient levels form an inverse diagram in the transporter category. -/
def congruenceLevelTower : ℕᵒᵖ ⥤ CompactOpenLevel G where
  obj n := congruenceLevel U I M hN n.unop
  map f := congruenceLevelMap U I M hN (leOfHom f.unop)
  map_id n := by apply CompactOpenLevel.Arrow.ext; rfl
  map_comp f g := by apply CompactOpenLevel.Arrow.ext; exact (mul_one 1).symm

variable {Γ : Type z} {X : Type t} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* G)

/-- Actual congruence-level double quotients with their residual quotient-group actions. -/
def congruenceLevelSpaces :
    EquivariantDiagram (torsionCongruenceGroups I M) TopCat where
  obj := congruenceLevelTower U I M hN ⋙ LevelSpace.tower (X := X) (ι := ι)
  ρ n := (LevelSpace.normalQuotientAction (X := X) ι U.subgroup
    (congruenceKernel I M n.unop)).ρ
  comm f g :=
    (LevelSpace.normalCoverMap (X := X) ι U.subgroup
      (congruenceKernel I M _) (congruenceKernel_antitone I M (leOfHom f.unop))).comm g

@[simp] theorem congruenceLevelSpaces_action (n : ℕᵒᵖ) :
    (congruenceLevelSpaces (X := X) U I M hN ι).action n =
      LevelSpace.normalQuotientAction (X := X) ι U.subgroup
        (congruenceKernel I M n.unop) := rfl

@[simp] theorem congruenceLevelSpaces_map_mk {i j : ℕᵒᵖ} (f : i ⟶ j) (x : X × G) :
    (congruenceLevelSpaces (X := X) U I M hN ι).obj.map f
        (LevelSpace.mk (congruenceLevel U I M hN i.unop).subgroup x) =
      LevelSpace.mk (congruenceLevel U I M hN j.unop).subgroup x := by
  change LevelSpace.mk _ (x.1, x.2 * 1) = _
  simp only [mul_one]
  rfl

/-- The surjective forgetful projections assemble into a natural transformation. -/
def congruenceLevelProjection :
    (congruenceLevelSpaces (X := X) U I M hN ι).obj ⟶
      (Functor.const ℕᵒᵖ).obj (TopCat.of (LevelSpace (X := X) ι U.subgroup)) where
  app n := LevelSpace.normalCoverProjection (X := X) ι U.subgroup
    (congruenceKernel I M n.unop)
  naturality {i j} f := by
    change (LevelSpace.normalCoverMap (X := X) ι U.subgroup
        (congruenceKernel I M i.unop)
        (congruenceKernel_antitone I M (leOfHom f.unop))).hom ≫
          LevelSpace.normalCoverProjection (X := X) ι U.subgroup
            (congruenceKernel I M j.unop) =
        LevelSpace.normalCoverProjection (X := X) ι U.subgroup
          (congruenceKernel I M i.unop) ≫
            𝟙 (TopCat.of (LevelSpace (X := X) ι U.subgroup))
    simpa only [Category.comp_id] using
      LevelSpace.normalCoverMap_projection (X := X) ι U.subgroup
      (congruenceKernel I M _) (congruenceKernel_antitone I M (leOfHom f.unop))

theorem congruenceLevelProjection_surjective (n : ℕᵒᵖ) :
    Function.Surjective ((congruenceLevelProjection (X := X) U I M hN ι).app n) :=
  LevelSpace.normalCoverProjection_surjective (X := X) ι U.subgroup
    (congruenceKernel I M n.unop)

@[reassoc] theorem congruenceLevelProjection_invariant (n : ℕᵒᵖ)
    (g : (torsionCongruenceGroups I M).obj n) :
    End.asHom ((congruenceLevelSpaces (X := X) U I M hN ι).ρ n g) ≫
        (congruenceLevelProjection (X := X) U I M hN ι).app n =
      (congruenceLevelProjection (X := X) U I M hN ι).app n :=
  LevelSpace.normalCoverProjection_invariant (X := X) ι U.subgroup
    (congruenceKernel I M n.unop) g

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

/-- The ambient compact open levels constructed from the actual stable coefficient lattice. -/
def compactCoefficientCongruenceLevels : ℕᵒᵖ ⥤ CompactOpenLevel σ.FiniteAdelicPoints :=
  congruenceLevelTower U (coefficientScalarIdeal l m)
    (compactStableCoefficientLattice ρ p l U hρ).action
    (fun n => (compactCoefficient_congruenceKernel ρ p l U hρ m hm n).1)

variable {Γ : Type v} {X : Type w} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* σ.FiniteAdelicPoints)

/-- The actual coefficient-congruence space diagram uses the original coefficient quotient groups. -/
def compactCoefficientCongruenceSpaces :
    EquivariantDiagram
      ((compactStableCoefficientLattice ρ p l U hρ).rationalCongruenceGroups m)
      TopCat.{max u w} :=
  congruenceLevelSpaces (X := X) U (coefficientScalarIdeal l m)
    (compactStableCoefficientLattice ρ p l U hρ).action
    (fun n => (compactCoefficient_congruenceKernel ρ p l U hρ m hm n).1) ι

@[simp] theorem compactCoefficientCongruenceSpaces_obj :
    (compactCoefficientCongruenceSpaces (X := X) ρ p l U hρ m hm ι).obj =
      compactCoefficientCongruenceLevels ρ p l U hρ m hm ⋙
        LevelSpace.tower (X := X) (ι := ι) := rfl

include hm in
/-- Every residual group in the constructed diagram is finite. -/
theorem compactCoefficientCongruenceSpaces_group_finite (n : ℕᵒᵖ) :
    Finite (((compactStableCoefficientLattice ρ p l U hρ).rationalCongruenceGroups m).obj n) :=
  (compactCoefficient_congruenceKernel ρ p l U hρ m hm n.unop).2

/-- The natural projection to the original level for the constructed adelic congruence spaces. -/
def compactCoefficientCongruenceProjection :
    (compactCoefficientCongruenceSpaces (X := X) ρ p l U hρ m hm ι).obj ⟶
      (Functor.const ℕᵒᵖ).obj (TopCat.of (LevelSpace (X := X) ι U.subgroup)) :=
  congruenceLevelProjection (X := X) U (coefficientScalarIdeal l m)
    (compactStableCoefficientLattice ρ p l U hρ).action
    (fun n => (compactCoefficient_congruenceKernel ρ p l U hρ m hm n).1) ι

end HarrisCoefficients

end Coefficients
end Langlands.Shimura
