import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionRestriction
import Langlands.Topology.GroupAction.DiscreteOperatorGroup
import Mathlib.Algebra.Group.PUnit

/-! # Discrete and trivial operators on actual quotient actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory Langlands.Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Replace the retained operator group topology by the discrete topology,
restricting the actual quotient action along the original-value homomorphism. -/
def discreteOperators (X : VariableActionSpace.{u, v} K) :
    VariableActionSpace.{u, v} K :=
  restrict X (DiscreteOperatorGroup.toOriginal X.groupType)

@[simp]
theorem discreteOperators_algebra (X : VariableActionSpace.{u, v} K) :
    (discreteOperators X).algebraAction.obj.V = X.algebraAction.obj.V := rfl

/-- The source's arrow `a`, with original-value group map and bounded identity
algebra pullback on the actual quotient. -/
def discreteOperatorsMap (X : VariableActionSpace.{u, v} K) :
    discreteOperators X ⟶ X :=
  restrictionMap X (DiscreteOperatorGroup.toOriginal X.groupType)

@[simp]
theorem discreteOperatorsMap_groupHom (X : VariableActionSpace.{u, v} K) :
    (discreteOperatorsMap X).groupHom =
      DiscreteOperatorGroup.toOriginal X.groupType := rfl

@[simp]
theorem discreteOperatorsMap_algebraMap (X : VariableActionSpace.{u, v} K) :
    (discreteOperatorsMap X).algebraMap =
      BoundedAlgHom.id K X.algebraAction.obj.V := rfl

/-- Discretizing the group retains every original compatible bounded algebra
map and discretizes its continuous group homomorphism. -/
def discreteOperatorsFunctor :
    VariableActionSpace.{u, v} K ⥤ VariableActionSpace.{u, v} K where
  obj := discreteOperators
  map f :=
    { groupHom := DiscreteOperatorGroup.map f.groupHom.toMonoidHom
      algebraMap := f.algebraMap
      equivariant := f.equivariant }
  map_id _ := by apply Hom.ext <;> rfl
  map_comp _ _ := by apply Hom.ext <;> rfl

@[simp]
theorem discreteOperatorsFunctor_map_groupHom
    {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) :
    (discreteOperatorsFunctor.map f).groupHom =
      DiscreteOperatorGroup.map f.groupHom.toMonoidHom := rfl

@[simp]
theorem discreteOperatorsFunctor_map_algebraMap
    {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) :
    (discreteOperatorsFunctor.map f).algebraMap = f.algebraMap := rfl

/-- The canonical arrows `a` form a natural transformation. -/
def discreteOperatorsNatTrans :
    discreteOperatorsFunctor (K := K) ⟶ 𝟭 (VariableActionSpace.{u, v} K) where
  app := discreteOperatorsMap
  naturality _ _ _ := by apply Hom.ext <;> rfl

/-- The underlying actual quotient, with the genuine one-element operator
group and its trivial norm-continuous action. -/
def trivialOperators (P : PresentedAffinoidAlgebra K) :
    VariableActionSpace.{u, v} K :=
  ⟨PUnit.{v + 1}, NormContinuousAction.trivial P⟩

@[simp]
theorem trivialOperators_algebra (P : PresentedAffinoidAlgebra K) :
    (trivialOperators.{u, v} P).algebraAction.obj.V = P := rfl

/-- Opposite bounded algebra maps give the functor assigning trivial operators
to every actual quotient. -/
def trivialOperatorsFunctor :
    (PresentedAffinoidAlgebra K)ᵒᵖ ⥤ VariableActionSpace.{u, v} K where
  obj P := trivialOperators P.unop
  map f :=
    { groupHom := ContinuousMonoidHom.id PUnit.{v + 1}
      algebraMap := f.unop
      equivariant _ _ := rfl }
  map_id _ := by apply Hom.ext <;> rfl
  map_comp _ _ := by apply Hom.ext <;> rfl

/-- The source's arrow `b` from the underlying quotient with trivial operators,
using the unit group homomorphism and bounded identity algebra pullback. -/
def trivialOperatorsMap (X : VariableActionSpace.{u, v} K) :
    trivialOperators X.algebraAction.obj.V ⟶ X where
  groupHom := 1
  algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
  equivariant _ a := by
    change (X.algebraAction.obj.ρ 1).toAlgHom a = a
    rw [map_one]
    rfl

@[simp]
theorem trivialOperatorsMap_groupHom (X : VariableActionSpace.{u, v} K) :
    (trivialOperatorsMap X).groupHom = 1 := rfl

@[simp]
theorem trivialOperatorsMap_algebraMap (X : VariableActionSpace.{u, v} K) :
    (trivialOperatorsMap X).algebraMap =
      BoundedAlgHom.id K X.algebraAction.obj.V := rfl

/-- The canonical arrows `b` form a natural transformation from the
underlying-quotient functor equipped with trivial operators. -/
def trivialOperatorsNatTrans :
    forget (K := K) ⋙ trivialOperatorsFunctor ⟶ 𝟭 (VariableActionSpace.{u, v} K) where
  app := trivialOperatorsMap
  naturality _ _ f := by
    apply Hom.ext
    · ext g
      exact f.groupHom.map_one.symm
    · rfl

/-- The map from trivial to discrete operators, on the same actual quotient. -/
def trivialToDiscrete (X : VariableActionSpace.{u, v} K) :
    trivialOperators X.algebraAction.obj.V ⟶ discreteOperators X :=
  trivialOperatorsMap (discreteOperators X)

/-- The arrow `b` factors through the arrow `a` as a complete varying-group
geometric arrow, including the group homomorphism. -/
theorem trivialToDiscrete_comp_discreteOperatorsMap
    (X : VariableActionSpace.{u, v} K) :
    trivialToDiscrete X ≫ discreteOperatorsMap X = trivialOperatorsMap X := by
  apply Hom.ext <;> rfl

/-- This factorization is natural in every varying-group quotient arrow. -/
def trivialToDiscreteNatTrans :
    forget (K := K) ⋙ trivialOperatorsFunctor ⟶
      discreteOperatorsFunctor.{u, v} (K := K) where
  app := trivialToDiscrete
  naturality _ _ f := by
    apply Hom.ext
    · ext g
      exact f.groupHom.map_one.symm
    · rfl

theorem trivialToDiscreteNatTrans_comp :
    trivialToDiscreteNatTrans.{u, v} (K := K) ≫ discreteOperatorsNatTrans =
      trivialOperatorsNatTrans := by
  apply NatTrans.ext
  funext X
  exact trivialToDiscrete_comp_discreteOperatorsMap X

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

@[simp]
theorem spectrumFunctor_discreteOperatorsMap_groupHom
    (X : VariableActionSpace.{u, v} K) :
    (spectrumFunctor.map (discreteOperatorsMap X)).groupHom =
      DiscreteOperatorGroup.toOriginal X.groupType := rfl

@[simp]
theorem spectrumFunctor_discreteOperatorsMap_apply
    (X : VariableActionSpace.{u, v} K) (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumFunctor.map (discreteOperatorsMap X)).spaceMap x = x :=
  BanachSpectrum.ext fun _ => rfl

@[simp]
theorem spectrumFunctor_trivialOperatorsMap_groupHom
    (X : VariableActionSpace.{u, v} K) :
    (spectrumFunctor.map (trivialOperatorsMap X)).groupHom = 1 := rfl

@[simp]
theorem spectrumFunctor_trivialOperatorsMap_apply
    (X : VariableActionSpace.{u, v} K) (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumFunctor.map (trivialOperatorsMap X)).spaceMap x = x :=
  BanachSpectrum.ext fun _ => rfl

@[simp]
theorem spectrumFunctor_trivialToDiscrete_groupHom
    (X : VariableActionSpace.{u, v} K) :
    (spectrumFunctor.map (trivialToDiscrete X)).groupHom = 1 := rfl

@[simp]
theorem spectrumFunctor_trivialToDiscrete_apply
    (X : VariableActionSpace.{u, v} K) (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumFunctor.map (trivialToDiscrete X)).spaceMap x = x :=
  BanachSpectrum.ext fun _ => rfl

/-- Actual continuous spectra preserve the complete factorization `b = a ∘ c`. -/
theorem spectrumFunctor_trivialToDiscrete_factorization
    (X : VariableActionSpace.{u, v} K) :
    spectrumFunctor.map (trivialToDiscrete X) ≫
        spectrumFunctor.map (discreteOperatorsMap X) =
      spectrumFunctor.map (trivialOperatorsMap X) := by
  rw [← Functor.map_comp, trivialToDiscrete_comp_discreteOperatorsMap]

end Spectrum

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
