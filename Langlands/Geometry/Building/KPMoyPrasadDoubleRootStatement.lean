import Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement
import Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement

/-!
# Double-root commutator friendliness and KP Proposition 13.2.5 (1), (2), (4)

The commutator clause of KP Definition 7.2.1 (`IsCommutatorFriendly`) bounds the
`Z`-component of `u'⁻¹ u u' u⁻¹` by `r = x_a(u) + x_{-a}(u')`. When `u ∈ U_{2a}(F)` or
`u' ∈ U_{-2a}(F)`, the actual `Z`-component has depth `2r` (KP's `SU_3` computation in the
proof of Proposition 7.1.1), and the proofs of Proposition 13.2.5 (1), (2) and (4) need this
sharper bound. This module states it as a predicate on supplied filtrations, restates those
parts with it as an extra premise, and states existence of a filtration that also satisfies
it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- Commutator friendliness for pairs involving a double root: for `u ∈ U_a(F)*`,
`u' ∈ U_{-a}(F)*` with `u ∈ U_{2a}(F)` or `u' ∈ U_{-2a}(F)`, and a point `x` of the apartment
with `r = x_a(u) + x_{-a}(u') > 0`, the `Z`-component `z` of `u'⁻¹ u u' u⁻¹ ∈ U_{-a}(F) z U_a(F)`
lies in `Z(F)_{2r}`. -/
def IsDoubleRootCommutatorFriendly : Prop :=
  ∀ (x : P.Apartment) (a : relativeRoots P.i) (u u' : rationalPoints G),
    u ∈ P.rootGroup a.1 → u ≠ 1 → u' ∈ P.rootGroup (-a.1) → u' ≠ 1 →
    (u ∈ P.doubleRootGroup a.1 ∨ u' ∈ P.doubleRootGroup (-a.1)) →
    ∀ r : NNReal, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
    ∀ (v' v : rationalPoints G) (z : rationalPoints P.centralizer.Z),
      v' ∈ P.rootGroup (-a.1) → v ∈ P.rootGroup a.1 →
      u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map P.centralizer.j z * v →
      z ∈ Zf.filtration (2 * r)

end ParahoricBuildingData.CentralizerFiltration

/-- `MoyPrasadCovarianceStatement` with the extra premise
`Zf.IsDoubleRootCommutatorFriendly`: the Moy–Prasad subgroup of a point of the reduced
building is well defined (KP Proposition 13.2.5(1) and (2) for supplied data). -/
def MoyPrasadDoubleRootCovarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      Zf.IsDoubleRootCommutatorFriendly →
      ∀ (y : P.ReducedBuilding) (r : NNReal) (Q Q' : Subgroup (rationalPoints G)),
        Zf.IsMoyPrasadAt y r Q → Zf.IsMoyPrasadAt y r Q' → Q = Q'

/-- `MoyPrasadCommutatorStatement` with the extra premise
`Zf.IsDoubleRootCommutatorFriendly`: `[P_{x,r}, P_{x,s}] ⊆ P_{x,r+s}`
(KP Proposition 13.2.5(4) for supplied data). -/
def MoyPrasadDoubleRootCommutatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      Zf.IsDoubleRootCommutatorFriendly →
      ∀ (x : P.Apartment) (r s : NNReal),
        ⁅Zf.moyPrasad x r, Zf.moyPrasad x s⁆ ≤ Zf.moyPrasad x (r + s)

/-- The two corrected targets together: KP Proposition 13.2.5(1), (2) and (4) for supplied
data that are double-root commutator friendly. -/
def MoyPrasadDoubleRootStatement : Prop :=
  MoyPrasadDoubleRootCovarianceStatement.{u} ∧ MoyPrasadDoubleRootCommutatorStatement.{u}

/-- `CentralizerFiltrationExistenceStatement` with the filtration also double-root
commutator friendly (KP §9.8 and Lemma 9.8.1, with the `SU_3` computation behind
Lemma 7.2.3). -/
def CentralizerFiltrationDoubleRootExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
      ∃ Zf : P.CentralizerFiltration, Zf.SatisfiesFiltrationAxioms ∧ Zf.IsOpenFiltration ∧
        Zf.IsDoubleRootCommutatorFriendly

end Langlands.Geometry.Building
