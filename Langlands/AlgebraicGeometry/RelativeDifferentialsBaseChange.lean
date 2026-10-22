import Langlands.AlgebraicGeometry.RelativeDifferentialsMaps
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Relative differentials for commutative squares and base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X X' S T : AlgebraicGeometry.Scheme.{u}}

namespace RelativeDerivation

/-- A derivation relative to `T` also vanishes on sections pulled back from `S`. -/
def forgetBase (b : T ⟶ S) {f' : X' ⟶ T} {M : X'.Modules}
    (d : RelativeDerivation f' M) : RelativeDerivation (f' ≫ b) M where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} a := by
    exact d.app_base (b ⁻¹ᵁ U.unop) (b.app U.unop a)

@[simp]
lemma forgetBase_app (b : T ⟶ S) {f' : X' ⟶ T} {M : X'.Modules}
    (d : RelativeDerivation f' M) (U : X'.Opens) (a : Γ(X', U)) :
    (forgetBase b d).app U a = d.app U a := rfl

@[simp]
lemma forgetBase_postcomp (b : T ⟶ S) {f' : X' ⟶ T} {M N : X'.Modules}
    (d : RelativeDerivation f' M) (α : M ⟶ N) :
    forgetBase b (postcomp d α) = postcomp (forgetBase b d) α := by
  ext U a
  rfl

end RelativeDerivation

/-- The pushforward form of the differential comparison for a commutative square. -/
def relativeDifferentialsSquarePushforwardMap (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b) :
    relativeDifferentials f ⟶ (pushforward g).obj (relativeDifferentials f') :=
  relativeDifferentialsDesc f
    (RelativeDerivation.precompOver g w
      (RelativeDerivation.forgetBase b (relativeDifferentialsDerivation f')))

@[simp]
lemma relativeDifferentialsSquarePushforwardMap_fac (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b) :
    RelativeDerivation.postcomp (relativeDifferentialsDerivation f)
      (relativeDifferentialsSquarePushforwardMap g b w) =
        RelativeDerivation.precompOver g w
          (RelativeDerivation.forgetBase b (relativeDifferentialsDerivation f')) :=
  relativeDifferentialsDesc_fac _ _

/-- The canonical map on the actual relative differential sheaves for a commutative square. -/
def relativeDifferentialsSquareMap (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b) :
    (pullback g).obj (relativeDifferentials f) ⟶ relativeDifferentials f' :=
  ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (relativeDifferentialsSquarePushforwardMap g b w)

@[simp]
lemma relativeDifferentialsSquareMap_adjoint (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (relativeDifferentialsSquareMap g b w) =
      relativeDifferentialsSquarePushforwardMap g b w :=
  Equiv.apply_symm_apply _ _

/-- Characterization by the universal derivations under the actual module adjunction. -/
@[simp]
lemma relativeDifferentialsSquareMap_fac (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b) :
    RelativeDerivation.postcomp (relativeDifferentialsDerivation f)
      ((pullbackPushforwardAdjunction g).homEquiv _ _
        (relativeDifferentialsSquareMap g b w)) =
      RelativeDerivation.precompOver g w
        (RelativeDerivation.forgetBase b (relativeDifferentialsDerivation f')) := by
  rw [relativeDifferentialsSquareMap_adjoint, relativeDifferentialsSquarePushforwardMap_fac]

/-- On differentials of local sections, the adjoint applies the pulled-back derivation. -/
lemma relativeDifferentialsSquareMap_adjoint_app (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b)
    (U : X.Opens) (a : Γ(X, U)) :
    ((pullbackPushforwardAdjunction g).homEquiv _ _
      (relativeDifferentialsSquareMap g b w)).app U
        ((relativeDifferentialsDerivation f).app U a) =
      (relativeDifferentialsDerivation f').app (g ⁻¹ᵁ U) (g.app U a) := by
  have h := congrArg (fun d : RelativeDerivation f
      ((pushforward g).obj (relativeDifferentials f')) => d.app U a)
    (relativeDifferentialsSquareMap_fac g b w)
  simpa only [RelativeDerivation.postcomp_app, RelativeDerivation.precompOver_app,
    RelativeDerivation.forgetBase_app] using h

/-- The derivation equation uniquely determines the square comparison. -/
lemma relativeDifferentialsSquareMap_unique (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b)
    (α : (pullback g).obj (relativeDifferentials f) ⟶ relativeDifferentials f')
    (h : RelativeDerivation.postcomp (relativeDifferentialsDerivation f)
      ((pullbackPushforwardAdjunction g).homEquiv _ _ α) =
        RelativeDerivation.precompOver g w
          (RelativeDerivation.forgetBase b (relativeDifferentialsDerivation f'))) :
    α = relativeDifferentialsSquareMap g b w := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply relativeDifferentials_hom_ext f
  rw [relativeDifferentialsSquareMap_fac]
  exact h

/-- The local-section formula alone uniquely determines the square comparison. -/
lemma relativeDifferentialsSquareMap_unique_of_app (g : X' ⟶ X) (b : T ⟶ S)
    {f' : X' ⟶ T} {f : X ⟶ S} (w : g ≫ f = f' ≫ b)
    (α : (pullback g).obj (relativeDifferentials f) ⟶ relativeDifferentials f')
    (h : ∀ (U : X.Opens) (a : Γ(X, U)),
      ((pullbackPushforwardAdjunction g).homEquiv _ _ α).app U
        ((relativeDifferentialsDerivation f).app U a) =
      (relativeDifferentialsDerivation f').app (g ⁻¹ᵁ U) (g.app U a)) :
    α = relativeDifferentialsSquareMap g b w := by
  apply relativeDifferentialsSquareMap_unique g b w
  ext U a
  change Γ(X, U.unop) at a
  change (RelativeDerivation.postcomp (relativeDifferentialsDerivation f)
    ((pullbackPushforwardAdjunction g).homEquiv _ _ α)).app U.unop a =
      (RelativeDerivation.precompOver g w
        (RelativeDerivation.forgetBase b (relativeDifferentialsDerivation f'))).app U.unop a
  rw [RelativeDerivation.postcomp_app, RelativeDerivation.precompOver_app,
    RelativeDerivation.forgetBase_app]
  exact h U.unop a

/-- With the identity base map, the square comparison is the fixed-base comparison. -/
@[simp]
lemma relativeDifferentialsSquareMap_id_base (g : X' ⟶ X)
    {f' : X' ⟶ S} {f : X ⟶ S} (w : g ≫ f = f') :
    relativeDifferentialsSquareMap g (𝟙 S) (by simpa only [Category.comp_id] using w) =
      relativeDifferentialsMap g w := by
  symm
  apply relativeDifferentialsSquareMap_unique_of_app
  intro U a
  exact relativeDifferentialsMap_adjoint_app g w U a

/-- The canonical differential comparison for the categorical scheme fiber product. -/
def relativeDifferentialsBaseChangeMap (f : X ⟶ S) (b : T ⟶ S) :
    (pullback (Limits.pullback.fst f b)).obj (relativeDifferentials f) ⟶
      relativeDifferentials (Limits.pullback.snd f b) :=
  relativeDifferentialsSquareMap (Limits.pullback.fst f b) b Limits.pullback.condition

/-- Local characterization of the canonical base-change comparison. -/
lemma relativeDifferentialsBaseChangeMap_adjoint_app (f : X ⟶ S) (b : T ⟶ S)
    (U : X.Opens) (a : Γ(X, U)) :
    ((pullbackPushforwardAdjunction (Limits.pullback.fst f b)).homEquiv _ _
      (relativeDifferentialsBaseChangeMap f b)).app U
        ((relativeDifferentialsDerivation f).app U a) =
      (relativeDifferentialsDerivation (Limits.pullback.snd f b)).app
        ((Limits.pullback.fst f b) ⁻¹ᵁ U) ((Limits.pullback.fst f b).app U a) :=
  relativeDifferentialsSquareMap_adjoint_app _ _ _ U a

/-- Uniqueness of the base-change comparison from its local-section formula. -/
lemma relativeDifferentialsBaseChangeMap_unique_of_app (f : X ⟶ S) (b : T ⟶ S)
    (α : (pullback (Limits.pullback.fst f b)).obj (relativeDifferentials f) ⟶
      relativeDifferentials (Limits.pullback.snd f b))
    (h : ∀ (U : X.Opens) (a : Γ(X, U)),
      ((pullbackPushforwardAdjunction (Limits.pullback.fst f b)).homEquiv _ _ α).app U
        ((relativeDifferentialsDerivation f).app U a) =
      (relativeDifferentialsDerivation (Limits.pullback.snd f b)).app
        ((Limits.pullback.fst f b) ⁻¹ᵁ U) ((Limits.pullback.fst f b).app U a)) :
    α = relativeDifferentialsBaseChangeMap f b :=
  relativeDifferentialsSquareMap_unique_of_app _ _ _ α h

end Langlands.Scheme
