import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement

/-! # Elementary structural and transport targets for standard intertwining -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe u uV uW

/-- Unimodularity for the actual image of a supplied geometric radical. -/
def SuppliedParabolicRadicalUnimodularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (n : U ⟶ P)
      (_r : ParabolicRootPresentation p l a)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : Set (rationalPoints G))),
      IsUnimodularModulus
        ((SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU

/-- The actual integral has full domain simultaneously for equivariantly
equivalent inducing representations, at independent carrier universes. -/
def StandardIntertwiningFullDomainTransportStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    (P M U U' : Subgroup G) (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    [MeasurableSpace (QuotientSpace (U := U) U')]
    (ν : Measure (QuotientSpace (U := U) U'))
    (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ M)
    (_e : A.representation.Equiv B.representation),
    domain h hU U' A ν = ⊤ ↔ domain h hU U' B ν = ⊤

/-- One full-domain proof supplies every equivalent representative's full
domain and the actual positive-normalized standard-intertwining square. -/
def StandardIntertwiningRepresentativeNaturalityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    (P P' M U U' : Subgroup G)
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
    [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (QuotientSpace (U := U) U')]
    [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
    (ν : Measure (QuotientSpace (U := U) U'))
    (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
    [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    (hM : IsClosed (M : Set G))
    (hsq : SquaredModulusCompatibility h hU h' hU')
    (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ M)
    (hfullA : domain h hU U' A ν = ⊤)
    (e : A.representation.Equiv B.representation),
    ∃ hfullB : domain h hU U' B ν = ⊤,
      (fullSourceIntertwiner h hU h' hU' B ν μU' μI hν hM hsq hfullB).comp
          (inducedMap h hU e.toIntertwiningMap) =
        (inducedMap h' hU' e.toIntertwiningMap).comp
          (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfullA)

/-- Group the elementary structural and formal consequences needed by the
conditional finite-length standard intertwining theorem. -/
def ParabolicIntertwiningElementaryStatement : Prop :=
  SuppliedParabolicRadicalUnimodularityStatement.{u} ∧
    StandardIntertwiningFullDomainTransportStatement.{u, uV, uW} ∧
    StandardIntertwiningRepresentativeNaturalityStatement.{u, uV, uW}

end Langlands.Plancherel
