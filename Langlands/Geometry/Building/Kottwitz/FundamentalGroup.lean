import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctor
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.Geometry.Building.Kottwitz.InertiaCoinvariants

/-! # Inertia targets of reductive groups and their torus comparisons -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section TorusComparison
variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (hT : IsTorus T.toGrp)

/-- The actual cocharacter inclusion of the chosen maximal torus into the torus `T`. -/
def torusPresentationMap :
    (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).lattice E →ₗ[ℤ]
      geometricCocharacters k E T :=
  (AddMonoidHom.mk' (fun ν => ν ≫
    (CommGroupScheme.baseChange (algebraBaseMap k E)).map
      (Additive.ofMul
        (chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).inclusion))
    (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)).toIntLinearMap

/-- The canonical identification `π₁(T) → X_*(T)` is characterized on actual
cocharacter representatives. -/
def IsTorusFundamentalComparison
    (m : fundamentalGroup k T.toGrp E hT.isConnectedReductive_of_fieldSplitting →ₗ[ℤ]
      geometricCocharacters k E T) : Prop :=
  ∀ ν, m ((chosenChoice k T.toGrp hT.isConnectedReductive_of_fieldSplitting).projection E ν) =
    torusPresentationMap k E T hT ν

/-- The comparison selected by its actual cocharacter law (KP Fact 11.3.5). -/
def torusFundamentalComparison :
    fundamentalGroup k T.toGrp E hT.isConnectedReductive_of_fieldSplitting →ₗ[ℤ]
      geometricCocharacters k E T :=
  Classical.epsilon (IsTorusFundamentalComparison k E T hT)

end TorusComparison

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Normal k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (hG : IsConnectedReductive G)

/-- The actual integral inertia quotient `A = π₁(G)_I`. -/
abbrev FundamentalInertia :=
  inertiaCoinvariants k K E (fundamentalGroupGalois k G E hG)

/-- The quotient map from the actual fundamental group. -/
abbrev fundamentalInertiaProjection :
    fundamentalGroup k G E hG →ₗ[ℤ] FundamentalInertia k K E G hG :=
  inertiaProjection k K E (fundamentalGroupGalois k G E hG)

/-- The full torsion subgroup `A_tor`, before taking residual invariants. -/
abbrev fundamentalInertiaTorsion :
    Subgroup (Multiplicative (FundamentalInertia k K E G hG)) :=
  CommGroup.torsion _

section Residual
variable [Normal k E]

/-- The descended action of the actual residual group `Gal(K/k)`. -/
abbrev fundamentalGammaRepresentation :
    Representation ℤ (K ≃ₐ[k] K) (FundamentalInertia k K E G hG) :=
  inertiaGammaRepresentation k K E (fundamentalGroupGalois k G E hG)

/-- The fixed submodule `A^Γ`. -/
abbrev FundamentalInvariants :=
  inertiaInvariants k K E (fundamentalGroupGalois k G E hG)

/-- The fixed inertia torsion `(A_tor)^Γ` as a subgroup of `A^Γ`.
Finite order in the fixed subgroup is equivalent to finite order in `A`. -/
abbrev fundamentalInvariantTorsion :
    Subgroup (Multiplicative (FundamentalInvariants k K E G hG)) :=
  invariantTorsion k K E (fundamentalGroupGalois k G E hG)

end Residual

section InducedMaps
variable (H : GroupScheme (Spec (CommRingCat.of k)))
  (hH : IsConnectedReductive H) (f : H ⟶ G)

/-- The induced inertia map descends the actual map on algebraic fundamental groups. -/
def IsFundamentalInertiaMap
    (m : FundamentalInertia k K E H hH →ₗ[ℤ] FundamentalInertia k K E G hG) : Prop :=
  ∀ x, m (fundamentalInertiaProjection k K E H hH x) =
    fundamentalInertiaProjection k K E G hG (fundamentalGroupMap k E H G hH hG f x)

/-- Selected descent of the induced fundamental-group map. No equivariance or
existence theorem is assumed as data; these are unconditional targets. -/
def fundamentalInertiaMap :
    FundamentalInertia k K E H hH →ₗ[ℤ] FundamentalInertia k K E G hG :=
  Classical.epsilon (IsFundamentalInertiaMap k K E G hG H hH f)

end InducedMaps

section TorusInertiaComparison
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)

/-- The inertia comparison is characterized by the actual torus comparison
before passage to coinvariants. -/
def IsTorusInertiaComparison
    (m : FundamentalInertia k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting →ₗ[ℤ]
      torusInertiaCoinvariants k K E T) : Prop :=
  ∀ x, m (fundamentalInertiaProjection k K E T.toGrp
      hT.isConnectedReductive_of_fieldSplitting x) =
    inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E T)
      (torusFundamentalComparison k E T hT x)

/-- The selected comparison `π₁(T)_I → X_*(T)_I`. -/
def torusInertiaComparison :
    FundamentalInertia k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting →ₗ[ℤ]
      torusInertiaCoinvariants k K E T :=
  Classical.epsilon (IsTorusInertiaComparison k K E T hT)

end TorusInertiaComparison

end Langlands.Geometry.Building.Kottwitz
