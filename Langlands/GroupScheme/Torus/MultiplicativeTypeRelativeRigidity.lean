import Langlands.GroupScheme.Torus.RelativeDiagonalizableRigidity
import Langlands.GroupScheme.FppfHomLocality
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Rigidity of families of homomorphisms between groups of multiplicative type

Let `S` be a scheme, `X` a geometrically connected scheme over `S`, and `D`, `D'` groups of
multiplicative type over `S`. A family of homomorphisms `D → D'` parametrized by `X`, given on
points over every `S`-scheme (multiplicative in the group variable and natural in the test
scheme), does not depend on the parameter: two parameters `a a' : V ⟶ X` over the same test scheme
give the same homomorphism.

The statement is fppf local on `S` (`Rigid.of_cover`): equality of two morphisms `V ⟶ D'` is
checked on the fppf cover of `V` pulled back from `S`, and the family base changes to a family
over each member of the cover. Over a member where `D` and `D'` are diagonalizable it is
`RelativeDiagonalizableRigidity.eq_of_isDiagonalizable`, since the fibres of a geometrically
connected morphism are connected.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace MultiplicativeTypeRigidity

open RelativeMultiplicativeType

variable {S : Scheme.{u}}

/-- Rigidity for `X`-parametrized families of homomorphisms `D → D'`: every family of maps on
points that is multiplicative in the group variable and natural in the test scheme takes the same
value at any two parameters over the same test scheme. -/
def Rigid (X : Over S) (D D' : GroupScheme S) : Prop :=
  ∀ (F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X)),
    (∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ D.X), F V a (t₁ * t₂) = F V a t₁ * F V a t₂) →
    (∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ D.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t) →
    ∀ {V : Over S} (a a' : V ⟶ X) (t : V ⟶ D.X), F V a t = F V a' t

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S) {X : Over S} {D D' : GroupScheme S}
  (F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X))

/-- The base change of a family along `b : S' ⟶ S`: on an `S'`-scheme `V`, a parameter
`V ⟶ X_{S'}` and a point `V ⟶ D_{S'}` are, by the pullback adjunction, a parameter and a point of
`V` viewed as an `S`-scheme, where the original family is evaluated. -/
def baseChangeFamily (V : Over S') (a : V ⟶ (Over.pullback b).obj X)
    (t : V ⟶ ((baseChange b).obj D).X) : V ⟶ ((baseChange b).obj D').X :=
  (baseChangePointsEquiv b D' V).symm
    (F ((Over.map b).obj V) (((Over.mapPullbackAdj b).homEquiv V X).symm a)
      (baseChangePointsEquiv b D V t))

/-- The base-changed family is multiplicative. -/
theorem baseChangeFamily_mul
    (hmul : ∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ D.X),
      F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
    (V : Over S') (a : V ⟶ (Over.pullback b).obj X) (t₁ t₂ : V ⟶ ((baseChange b).obj D).X) :
    baseChangeFamily b F V a (t₁ * t₂) =
      baseChangeFamily b F V a t₁ * baseChangeFamily b F V a t₂ := by
  simp only [baseChangeFamily, map_mul, hmul]

/-- The base-changed family is natural in the test scheme. -/
theorem baseChangeFamily_naturality
    (hnat : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ D.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t)
    {V W : Over S'} (f : W ⟶ V) (a : V ⟶ (Over.pullback b).obj X)
    (t : V ⟶ ((baseChange b).obj D).X) :
    baseChangeFamily b F W (f ≫ a) (f ≫ t) = f ≫ baseChangeFamily b F V a t := by
  apply (baseChangePointsEquiv b D' W).injective
  rw [baseChangePointsEquiv_naturality b D' f, baseChangeFamily, baseChangeFamily,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality b D f,
    Adjunction.homEquiv_naturality_left_symm, hnat]

end BaseChange

/-- **Rigidity is fppf local on the base.** -/
theorem Rigid.of_cover {X : Over S} {D D' : GroupScheme S}
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (h : ∀ k, Rigid ((Over.pullback (𝒰.f k)).obj X) ((baseChange (𝒰.f k)).obj D)
      ((baseChange (𝒰.f k)).obj D')) :
    Rigid X D D' := by
  intro F hmul hnat V a a' t
  apply Over.OverMorphism.ext
  apply Precoverage.ZeroHypercover.hom_ext (𝒰.pullback₁ V.hom)
  intro k
  let b := 𝒰.f k
  let Vk : Over (𝒰.X k) := Over.mk (pullback.snd V.hom b)
  let c : (Over.map b).obj Vk ⟶ V := Over.homMk (pullback.fst V.hom b) pullback.condition
  have key : ∀ a₀ : V ⟶ X,
      baseChangeFamily b F Vk ((Over.mapPullbackAdj b).homEquiv Vk X (c ≫ a₀))
          ((baseChangePointsEquiv b D Vk).symm (c ≫ t)) =
        (baseChangePointsEquiv b D' Vk).symm (c ≫ F V a₀ t) := by
    intro a₀
    simp only [baseChangeFamily, Equiv.symm_apply_apply, MulEquiv.apply_symm_apply, hnat]
  have e := h k (baseChangeFamily b F) (baseChangeFamily_mul b F hmul)
    (fun f a t => baseChangeFamily_naturality b F hnat f a t)
    ((Over.mapPullbackAdj b).homEquiv Vk X (c ≫ a))
    ((Over.mapPullbackAdj b).homEquiv Vk X (c ≫ a'))
    ((baseChangePointsEquiv b D Vk).symm (c ≫ t))
  rw [key, key] at e
  have e' := congrArg (fun y => y.left) ((baseChangePointsEquiv b D' Vk).symm.injective e)
  exact e'

/-- The base change of a geometrically connected scheme over `S` is geometrically connected. -/
instance geometricallyConnected_pullback {S' : Scheme.{u}} (b : S' ⟶ S) (X : Over S)
    [GeometricallyConnected X.hom] : GeometricallyConnected ((Over.pullback b).obj X).hom := by
  change GeometricallyConnected (pullback.snd X.hom b)
  infer_instance

/-- Rigidity for diagonalizable groups over a geometrically connected parameter scheme. -/
theorem rigid_of_isDiagonalizable {X : Over S} [GeometricallyConnected X.hom]
    {D D' : GroupScheme S} (hD : IsDiagonalizable D) (hD' : IsDiagonalizable D') :
    Rigid X D D' :=
  fun F hmul hnat _ a a' t => RelativeDiagonalizableRigidity.eq_of_isDiagonalizable
    (fun s => (X.hom.isConnected_preimage_singleton s).isPreconnected) hD hD' F hmul hnat a a' t

/-- Rigidity for a diagonalizable source and a target of multiplicative type. -/
theorem rigid_of_isDiagonalizable_of_isMultiplicativeType {X : Over S}
    [GeometricallyConnected X.hom] {D D' : GroupScheme S} (hD : IsDiagonalizable D)
    (hD' : IsMultiplicativeType D') : Rigid X D D' := by
  obtain ⟨𝒰, h𝒰⟩ := hD'
  exact Rigid.of_cover 𝒰 fun k => rigid_of_isDiagonalizable (hD.baseChange _) (h𝒰 k)

/-- Rigidity for groups of multiplicative type over a geometrically connected parameter
scheme. -/
theorem rigid_of_isMultiplicativeType {X : Over S} [GeometricallyConnected X.hom]
    {D D' : GroupScheme S} (hD : IsMultiplicativeType D) (hD' : IsMultiplicativeType D') :
    Rigid X D D' := by
  obtain ⟨𝒰, h𝒰⟩ := hD
  exact Rigid.of_cover 𝒰 fun k =>
    rigid_of_isDiagonalizable_of_isMultiplicativeType (h𝒰 k) (hD'.baseChange _)

/-- **Rigidity of families of homomorphisms between groups of multiplicative type.** Let `X` be a
geometrically connected scheme over `S` and `D`, `D'` groups of multiplicative type over `S`. A
family of maps `F V a : (V ⟶ D) → (V ⟶ D')`, indexed by `S`-schemes `V` and parameters
`a : V ⟶ X`, multiplicative in the point of `D` and natural in `V`, takes the same value at any
two parameters over the same test scheme. -/
theorem eq_of_isMultiplicativeType {X : Over S} [GeometricallyConnected X.hom]
    {D D' : GroupScheme S} (hD : IsMultiplicativeType D) (hD' : IsMultiplicativeType D')
    (F : ∀ V : Over S, (V ⟶ X) → (V ⟶ D.X) → (V ⟶ D'.X))
    (hmul : ∀ (V : Over S) (a : V ⟶ X) (t₁ t₂ : V ⟶ D.X),
      F V a (t₁ * t₂) = F V a t₁ * F V a t₂)
    (hnat : ∀ {V W : Over S} (f : W ⟶ V) (a : V ⟶ X) (t : V ⟶ D.X),
      F W (f ≫ a) (f ≫ t) = f ≫ F V a t)
    {V : Over S} (a a' : V ⟶ X) (t : V ⟶ D.X) : F V a t = F V a' t :=
  rigid_of_isMultiplicativeType hD hD' F hmul hnat a a' t

end MultiplicativeTypeRigidity

end Langlands.GroupScheme
