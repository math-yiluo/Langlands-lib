import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionRestriction

/-! # Canonical operators as actual varying-group quotient automorphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Conjugation is a continuous group homomorphism on the retained actual
operator group. -/
def operatorConjugation (X : VariableActionSpace.{u, v} K) (g : X.groupType) :
    X.groupType →ₜ* X.groupType where
  toFun h := g * h * g⁻¹
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]
  continuous_toFun := IsTopologicalGroup.continuous_conj g

@[simp]
theorem operatorConjugation_apply (X : VariableActionSpace.{u, v} K)
    (g h : X.groupType) : operatorConjugation X g h = g * h * g⁻¹ := rfl

/-- The forward algebra action evaluates products by composition. -/
theorem algebraAction_mul_apply (X : VariableActionSpace.{u, v} K)
    (g h : X.groupType) (a : X.algebraAction.obj.V) :
    (X.algebraAction.obj.ρ (g * h)).asHom.toAlgHom a =
      (X.algebraAction.obj.ρ g).asHom.toAlgHom ((X.algebraAction.obj.ρ h).asHom.toAlgHom a) := by
  rw [map_mul]
  rfl

/-- An operator acts on the space with operators by conjugating the group and
pulling algebra elements back by its inverse. -/
def operatorTranslation (X : VariableActionSpace.{u, v} K) (g : X.groupType) :
    X ⟶ X where
  groupHom := operatorConjugation X g
  algebraMap := (X.algebraAction.obj.ρ (g⁻¹)).asHom
  equivariant h a := by
    have e : g⁻¹ * (g * h * g⁻¹) = h * g⁻¹ := by simp [mul_assoc]
    have t := congrArg (fun k => (X.algebraAction.obj.ρ k).asHom.toAlgHom a) e
    simpa only [operatorConjugation_apply, algebraAction_mul_apply] using t

@[simp]
theorem operatorTranslation_groupHom (X : VariableActionSpace.{u, v} K)
    (g : X.groupType) :
    (operatorTranslation X g).groupHom = operatorConjugation X g := rfl

@[simp]
theorem operatorTranslation_algebraMap (X : VariableActionSpace.{u, v} K)
    (g : X.groupType) :
    (operatorTranslation X g).algebraMap = (X.algebraAction.obj.ρ (g⁻¹)).asHom := rfl

@[simp]
theorem operatorTranslation_one (X : VariableActionSpace.{u, v} K) :
    operatorTranslation X 1 = 𝟙 X := by
  apply Hom.ext
  · ext h
    change 1 * h * 1⁻¹ = h
    simp
  · change (X.algebraAction.obj.ρ (1⁻¹)).asHom = (1 : End X.algebraAction.obj.V).asHom
    simp

/-- Geometric composition has the order appropriate to a left group action. -/
theorem operatorTranslation_comp (X : VariableActionSpace.{u, v} K)
    (g h : X.groupType) :
    operatorTranslation X g ≫ operatorTranslation X h = operatorTranslation X (h * g) := by
  apply Hom.ext
  · ext k
    change h * (g * k * g⁻¹) * h⁻¹ = (h * g) * k * (h * g)⁻¹
    simp only [mul_inv_rev, mul_assoc]
  · apply BoundedAlgHom.ext
    intro a
    change (X.algebraAction.obj.ρ (g⁻¹)).asHom.toAlgHom
        ((X.algebraAction.obj.ρ (h⁻¹)).asHom.toAlgHom a) =
      (X.algebraAction.obj.ρ ((h * g)⁻¹)).asHom.toAlgHom a
    rw [mul_inv_rev, algebraAction_mul_apply]

/-- The inverse operator constructs the genuine inverse varying-group arrow. -/
def operatorIso (X : VariableActionSpace.{u, v} K) (g : X.groupType) : X ≅ X where
  hom := operatorTranslation X g
  inv := operatorTranslation X (g⁻¹)
  hom_inv_id := by rw [operatorTranslation_comp, inv_mul_cancel, operatorTranslation_one]
  inv_hom_id := by rw [operatorTranslation_comp, mul_inv_cancel, operatorTranslation_one]

/-- The original operators extend to an actual action on the quotient object
with its operator group retained. -/
def operatorAction (X : VariableActionSpace.{u, v} K) : X.groupType →* Aut X where
  toFun g := Aut.of (operatorIso X g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact operatorTranslation_one X
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    exact (operatorTranslation_comp X h g).symm

@[simp]
theorem operatorAction_hom (X : VariableActionSpace.{u, v} K) (g : X.groupType) :
    (operatorAction X g).asIso.hom = operatorTranslation X g := rfl

@[simp]
theorem operatorAction_inv (X : VariableActionSpace.{u, v} K) (g : X.groupType) :
    (operatorAction X g).asIso.inv = operatorTranslation X (g⁻¹) := rfl

/-- Every actual varying-group arrow intertwines the canonical operators,
using its retained source-to-target group homomorphism. -/
theorem operatorTranslation_naturality {X Y : VariableActionSpace.{u, v} K}
    (f : X ⟶ Y) (g : X.groupType) :
    operatorTranslation X g ≫ f = f ≫ operatorTranslation Y (f.groupHom g) := by
  apply Hom.ext
  · ext h
    change f.groupHom (g * h * g⁻¹) =
      f.groupHom g * f.groupHom h * (f.groupHom g)⁻¹
    simp only [map_mul, map_inv]
  · apply BoundedAlgHom.ext
    intro a
    change (X.algebraAction.obj.ρ (g⁻¹)).asHom.toAlgHom (f.algebraMap a) =
      f.algebraMap ((Y.algebraAction.obj.ρ ((f.groupHom g)⁻¹)).asHom.toAlgHom a)
    rw [← map_inv]
    exact (f.equivariant (g⁻¹) a).symm

/-- In particular, actual group restriction is compatible with the canonical
operators and its genuine canonical geometric arrow. -/
theorem restrictionMap_operatorTranslation (X : VariableActionSpace.{u, v} K)
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : H →ₜ* X.groupType) (h : H) :
    operatorTranslation (restrict X f) h ≫ restrictionMap X f =
      restrictionMap X f ≫ operatorTranslation X (f h) :=
  operatorTranslation_naturality (restrictionMap X f) h

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

@[simp]
theorem spectrumFunctor_operatorTranslation_groupHom
    (X : VariableActionSpace.{u, v} K) (g : X.groupType) :
    (spectrumFunctor.map (operatorTranslation X g)).groupHom =
      operatorConjugation X g := rfl

/-- On actual bounded multiplicative spectra the full varying-group operator
is exactly the original inverse-pullback point action. -/
theorem spectrumFunctor_operatorTranslation_apply
    (X : VariableActionSpace.{u, v} K) (g : X.groupType)
    (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumFunctor.map (operatorTranslation X g)).spaceMap x =
      ConcreteCategory.hom ((NormContinuousAction.spectrum X.algebraAction).obj.ρ g).asHom x := by
  apply BanachSpectrum.ext
  intro a
  change x ((X.algebraAction.actionAut (g⁻¹)).asIso.hom.toAlgHom a) =
    x ((X.algebraAction.actionAut g).asIso.inv.toAlgHom a)
  rw [map_inv]
  rfl

/-- The spectrum functor transports the complete canonical operator
naturality equation, including its group component. -/
theorem spectrumFunctor_operatorTranslation_naturality
    {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) (g : X.groupType) :
    spectrumFunctor.map (operatorTranslation X g) ≫ spectrumFunctor.map f =
      spectrumFunctor.map f ≫
        spectrumFunctor.map (operatorTranslation Y (f.groupHom g)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, operatorTranslation_naturality]

end Spectrum

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
