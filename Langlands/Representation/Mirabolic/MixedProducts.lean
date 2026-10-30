import Langlands.Group.GL.MirabolicMixedProductSubgroups
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Twist.RealPower
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Products.Basic

/-!
# The mixed mirabolic products of BZ77 §4.12(II) and (III)

For smooth complex representations `A` of `GL_k(F)` and `B` of `P_(r+1)(F)`, the
functors `T.leftMixedProductFunctor k r` and `T.rightMixedProductFunctor k r` give
the smooth representations `A × B` and `B × A` of `P_(k+r+1)(F)`. Each is the
normalized compact induction, from the published inducing subgroup, of the
external tensor product `A ⊠ B` pulled back along the published projection and
twisted by an explicit real-power determinant character. All ranks are allowed;
no rank is treated separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct NNReal

namespace Langlands

universe uF uR uG uH uK uV uW uX uY uZ uU

/-! ## Compact induction from a subgroup containing every element -/

namespace Induction

section TopHom

variable {G : Type uG} [Group G]

/-- The identification `G → P`, `g ↦ g`, for a subgroup `P` containing every element. -/
def topHom (P : Subgroup G) (hP : ∀ g, g ∈ P) : G →* P :=
  (MonoidHom.id G).codRestrict P hP

@[simp]
theorem topHom_val (P : Subgroup G) (hP : ∀ g, g ∈ P) (g : G) :
    (topHom P hP g : G) = g := rfl

theorem continuous_topHom [TopologicalSpace G] (P : Subgroup G) (hP : ∀ g, g ∈ P) :
    Continuous (topHom P hP) :=
  continuous_id.subtype_mk hP

end TopHom

section TopEquiv

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem subsingleton_leftQuotient (P : Subgroup G) (hP : ∀ g, g ∈ P) :
    Subsingleton (LeftQuotient P) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun _ _ =>
    Quotient.sound (QuotientGroup.rightRel_apply.mpr (hP _))⟩

/-- The compactly supported covariant function `g ↦ σ(g) v`, when `P` contains
every element; its open stabilizer is the preimage of an open stabilizer of `v`. -/
def topFunction (P : Subgroup G) (hP : ∀ g, g ∈ P) (σ : Representation R P V) {v : V}
    (hv : IsSmoothVector σ v) : CompactFunctions P σ :=
  compactFunctionOf P σ (fun g => σ (topHom P hP g) v)
    (fun q x => by
      rw [map_mul, map_mul, Module.End.mul_apply]
      rfl)
    ((Classical.choose hv).comap (topHom P hP) (continuous_topHom P hP))
    (fun k x => by
      rw [map_mul, map_mul, Module.End.mul_apply]
      congr 1
      exact Classical.choose_spec hv ⟨topHom P hP k, k.property⟩)
    (by
      have := subsingleton_leftQuotient P hP
      exact Set.subsingleton_of_subsingleton.isCompact)

/-- Evaluation at `1` identifies compact induction from a subgroup containing every
element with the pulled-back representation; the inverse is `v ↦ (g ↦ σ(g) v)`. -/
def compactInducedTopEquiv (P : Subgroup G) (hP : ∀ g, g ∈ P) (σ : Representation R P V)
    (hσ : IsSmooth σ) : (compactInduced P σ).Equiv (σ.comp (topHom P hP)) :=
  Representation.Equiv.mk
    { toFun := fun f => eval P σ f.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => topFunction P hP σ (hσ v)
      left_inv := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact (f.1.1.2 (topHom P hP x) 1).symm.trans (congrArg f.1.1.1 (mul_one x))
      right_inv := fun v => by
        change σ (topHom P hP 1) v = v
        rw [map_one, map_one, Module.End.one_apply] }
    fun g => LinearMap.ext fun f => by
      change f.1.1.1 (1 * g) = σ (topHom P hP g) (f.1.1.1 1)
      rw [one_mul]
      exact (congrArg f.1.1.1 (mul_one g)).symm.trans (f.1.1.2 (topHom P hP g) 1)

@[simp]
theorem compactInducedTopEquiv_apply (P : Subgroup G) (hP : ∀ g, g ∈ P)
    (σ : Representation R P V) (hσ : IsSmooth σ) (f : CompactFunctions P σ) :
    compactInducedTopEquiv P hP σ hσ f = eval P σ f.1 1 := rfl

theorem eval_compactInducedTopEquiv_symm (P : Subgroup G) (hP : ∀ g, g ∈ P)
    (σ : Representation R P V) (hσ : IsSmooth σ) (v : V) (g : G) :
    eval P σ ((compactInducedTopEquiv P hP σ hσ).symm v).1 g = σ (topHom P hP g) v := rfl

end TopEquiv

end Induction

/-! ## Binary external tensor products, pullbacks and carrier lifts -/

namespace MixedProductTensor

section External

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
variable {V'' : Type uX} [AddCommGroup V''] [Module ℂ V'']
variable {W : Type uY} [AddCommGroup W] [Module ℂ W]
variable {W' : Type uZ} [AddCommGroup W'] [Module ℂ W']
variable {W'' : Type uU} [AddCommGroup W''] [Module ℂ W'']

/-- The external tensor product: `(g, h)` acts on `V ⊗ W` by `ρ(g) ⊗ σ(h)`. -/
def external (ρ : Representation ℂ G V) (σ : Representation ℂ H W) :
    Representation ℂ (G × H) (V ⊗[ℂ] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

theorem external_apply (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (x : G × H) :
    external ρ σ x = TensorProduct.map (ρ x.1) (σ x.2) := rfl

@[simp]
theorem external_tmul (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (x : G × H)
    (v : V) (w : W) : external ρ σ x (v ⊗ₜ w) = ρ x.1 v ⊗ₜ σ x.2 w := rfl

/-- The tensor product `f ⊗ g` of two intertwiners. -/
def externalMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ') :
    (external ρ σ).IntertwiningMap (external ρ' σ') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := TensorProduct.ext' fun v w => by
    change f (ρ x.1 v) ⊗ₜ g (σ x.2 w) = ρ' x.1 (f v) ⊗ₜ σ' x.2 (g w)
    rw [f.isIntertwining, g.isIntertwining]

@[simp]
theorem externalMap_tmul {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ') (v : V) (w : W) :
    externalMap f g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

theorem externalMap_toLinearMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ') :
    (externalMap f g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

theorem externalMap_id (ρ : Representation ℂ G V) (σ : Representation ℂ H W) :
    externalMap (Representation.IntertwiningMap.id ρ) (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (external ρ σ) :=
  Representation.IntertwiningMap.ext TensorProduct.map_id

theorem externalMap_comp {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {ρ'' : Representation ℂ G V''} {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    {σ'' : Representation ℂ H W''} (f : ρ.IntertwiningMap ρ') (f' : ρ'.IntertwiningMap ρ'')
    (g : σ.IntertwiningMap σ') (g' : σ'.IntertwiningMap σ'') :
    externalMap (f'.comp f) (g'.comp g) = (externalMap f' g').comp (externalMap f g) :=
  Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl)

/-- The tensor unit `ULift ℂ ⊗ W ≃ W`, `c ⊗ w ↦ c.down • w`. -/
def unitTensorLeft (W : Type uY) [AddCommGroup W] [Module ℂ W] :
    (ULift.{uV} ℂ ⊗[ℂ] W) ≃ₗ[ℂ] W :=
  (TensorProduct.congr (ULift.moduleEquiv (R := ℂ) (M := ℂ)) (LinearEquiv.refl ℂ W)).trans
    (TensorProduct.lid ℂ W)

@[simp]
theorem unitTensorLeft_tmul (c : ULift.{uV} ℂ) (w : W) :
    unitTensorLeft.{uV} W (c ⊗ₜ w) = c.down • w := by
  simp [unitTensorLeft]

theorem unitTensorLeft_symm_apply (w : W) :
    (unitTensorLeft.{uV} W).symm w = ULift.up 1 ⊗ₜ w := by
  rw [LinearEquiv.symm_apply_eq, unitTensorLeft_tmul, ULift.down_up, one_smul]

theorem unitTensorLeft_naturality (g : W →ₗ[ℂ] W') (t : ULift.{uV} ℂ ⊗[ℂ] W) :
    unitTensorLeft.{uV} W' (TensorProduct.map LinearMap.id g t) = g (unitTensorLeft W t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor unit `V ⊗ ULift ℂ ≃ V`, `v ⊗ c ↦ c.down • v`. -/
def unitTensorRight (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    (V ⊗[ℂ] ULift.{uY} ℂ) ≃ₗ[ℂ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) (ULift.moduleEquiv (R := ℂ) (M := ℂ))).trans
    (TensorProduct.rid ℂ V)

@[simp]
theorem unitTensorRight_tmul (v : V) (c : ULift.{uY} ℂ) :
    unitTensorRight.{uV, uY} V (v ⊗ₜ c) = c.down • v := by
  simp [unitTensorRight]

theorem unitTensorRight_symm_apply (v : V) :
    (unitTensorRight.{uV, uY} V).symm v = v ⊗ₜ ULift.up 1 := by
  rw [LinearEquiv.symm_apply_eq, unitTensorRight_tmul, ULift.down_up, one_smul]

theorem unitTensorRight_naturality (f : V →ₗ[ℂ] V') (t : V ⊗[ℂ] ULift.{uY} ℂ) :
    unitTensorRight.{uW, uY} V' (TensorProduct.map f LinearMap.id t) =
      f (unitTensorRight V t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- With the trivial line as first factor, `ULift ℂ ⊠ σ ≃ σ ∘ snd`. -/
def externalUnitLeftEquiv (σ : Representation ℂ H W) :
    (external (Representation.trivial ℂ G (ULift.{uV} ℂ)) σ).Equiv
      (σ.comp (MonoidHom.snd G H)) :=
  Representation.Equiv.mk (unitTensorLeft W) fun x => TensorProduct.ext' fun c w => by
    change unitTensorLeft W (c ⊗ₜ σ x.2 w) = σ x.2 (unitTensorLeft W (c ⊗ₜ w))
    rw [unitTensorLeft_tmul, unitTensorLeft_tmul, map_smul]

/-- With the trivial line as second factor, `ρ ⊠ ULift ℂ ≃ ρ ∘ fst`. -/
def externalUnitRightEquiv (ρ : Representation ℂ G V) :
    (external ρ (Representation.trivial ℂ H (ULift.{uY} ℂ))).Equiv
      (ρ.comp (MonoidHom.fst G H)) :=
  Representation.Equiv.mk (unitTensorRight V) fun x => TensorProduct.ext' fun v c => by
    change unitTensorRight V (ρ x.1 v ⊗ₜ c) = ρ x.1 (unitTensorRight V (v ⊗ₜ c))
    rw [unitTensorRight_tmul, unitTensorRight_tmul, map_smul]

section Smooth

variable [TopologicalSpace G] [TopologicalSpace H]

/-- A pure tensor `v ⊗ w` is fixed by the product of open stabilizers of `v` and
`w`; sums of smooth vectors are smooth. -/
theorem isSmooth_external {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) : IsSmooth (external ρ σ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨K, hK⟩ := hρ v
    obtain ⟨L, hL⟩ := hσ w
    refine ⟨K.prod L, ?_⟩
    intro x
    have hx : (x : G × H).1 ∈ K ∧ (x : G × H).2 ∈ L := x.property
    have h₁ : ρ (x : G × H).1 v = v := hK ⟨_, hx.1⟩
    have h₂ : σ (x : G × H).2 w = w := hL ⟨_, hx.2⟩
    change external ρ σ (x : G × H) (v ⊗ₜ w) = v ⊗ₜ w
    rw [external_tmul, h₁, h₂]
  | add x y hx hy => exact isSmoothVector_add hx hy

theorem isSmooth_trivial : IsSmooth (Representation.trivial ℂ G V) :=
  fun _ => ⟨⊤, fun _ => rfl⟩

end Smooth

end External

section Pullback

variable {G : Type uG} [Group G] {K : Type uK} [Group K]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- Pull back an intertwiner using `BinaryTensor.compMap`, with the homomorphism first. -/
abbrev pullbackMap (φ : K →* G) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : Representation.IntertwiningMap (ρ.comp φ) (ρ'.comp φ) :=
  BinaryTensor.compMap f φ

@[simp]
theorem pullbackMap_apply (φ : K →* G) {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ') (v : V) :
    pullbackMap φ f v = f v := rfl

/-- Pull back an equivalence using `BinaryTensor.compEquiv`, with the homomorphism first. -/
abbrev compEquiv (φ : K →* G) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') : Representation.Equiv (ρ.comp φ) (ρ'.comp φ) :=
  BinaryTensor.compEquiv e φ

@[simp]
theorem compEquiv_apply (φ : K →* G) {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (v : V) : compEquiv φ e v = e v := rfl

/-- Twisting by a character equal to `1` is the identity map. -/
def twistOneEquiv (χ : G →* ℂˣ) (hχ : χ = 1) (ρ : Representation ℂ G V) :
    (twist χ ρ).Equiv ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => LinearMap.ext fun v => by
    change (χ g : ℂ) • ρ g v = ρ g v
    rw [hχ, MonoidHom.one_apply, Units.val_one, one_smul]

@[simp]
theorem twistOneEquiv_apply (χ : G →* ℂˣ) (hχ : χ = 1) (ρ : Representation ℂ G V) (v : V) :
    twistOneEquiv χ hχ ρ v = v := rfl

end Pullback

section Lift

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- The existing `BinaryTensor.lift` carrier lift to `ULift V`. -/
abbrev lift (ρ : Representation ℂ G V) : Representation ℂ G (ULift.{uY} V) :=
  BinaryTensor.lift ρ

@[simp]
theorem lift_apply (ρ : Representation ℂ G V) (g : G) (v : ULift.{uY} V) :
    lift ρ g v = ULift.up (ρ g v.down) := rfl

/-- The existing `BinaryTensor.liftEquiv`, given by `ULift.up`. -/
abbrev liftEquiv (ρ : Representation ℂ G V) : ρ.Equiv (lift.{uG, uV, uY} ρ) :=
  BinaryTensor.liftEquiv ρ

@[simp]
theorem liftEquiv_apply (ρ : Representation ℂ G V) (v : V) :
    liftEquiv.{uG, uV, uY} ρ v = ULift.up v := rfl

/-- The existing `BinaryTensor.liftMap`, acting by `up ∘ f ∘ down`. -/
abbrev liftMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') :
    (lift.{uG, uV, uY} ρ).IntertwiningMap (lift.{uG, uW, uY} ρ') :=
  BinaryTensor.liftMap f

@[simp]
theorem liftMap_apply {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (v : ULift.{uY} V) :
    liftMap.{uG, uV, uW, uY} f v = ULift.up (f v.down) := rfl

theorem isSmooth_lift [TopologicalSpace G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    IsSmooth (lift.{uG, uV, uY} ρ) := by
  intro v
  obtain ⟨K, hK⟩ := hρ v.down
  refine ⟨K, ?_⟩
  intro k
  exact congrArg ULift.up (hK k)

end Lift

section Functors

variable {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

/-- Morphisms of smooth representations agree when their underlying maps agree. -/
theorem smoothRep_hom_ext {A B : SmoothRep.{0, uG, uV} ℂ G} {f g : A ⟶ B}
    (h : ∀ x, SmoothRep.hom f x = SmoothRep.hom g x) : f = g := by
  have e : SmoothRep.hom f = SmoothRep.hom g :=
    Representation.IntertwiningMap.ext (LinearMap.ext h)
  calc f = SmoothRep.ofHom (SmoothRep.hom f) := rfl
    _ = SmoothRep.ofHom (SmoothRep.hom g) := by rw [e]
    _ = g := rfl

/-- The bundled external tensor product of two smooth representations. -/
def externalObj (X : SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uH, uV} ℂ H) :
    SmoothRep.{0, max uG uH, uV} ℂ (G × H) :=
  SmoothRep.of (external X.1.representation X.2.representation)
    (isSmooth_external X.1.isSmooth X.2.isSmooth)

/-- The external tensor product as a functor on pairs; a pair of maps goes to `f ⊗ g`. -/
def externalFunctor :
    (SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uH, uV} ℂ H) ⥤
      SmoothRep.{0, max uG uH, uV} ℂ (G × H) where
  obj X := externalObj X
  map f := SmoothRep.ofHom (externalMap (SmoothRep.hom f.1) (SmoothRep.hom f.2))
  map_id X := by
    change SmoothRep.ofHom (A := externalObj X) (B := externalObj X)
        (externalMap (Representation.IntertwiningMap.id X.1.representation)
          (Representation.IntertwiningMap.id X.2.representation)) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [externalMap_id]
    rfl
  map_comp {X Y Z} f g := by
    change SmoothRep.ofHom (A := externalObj X) (B := externalObj Z)
        (externalMap ((SmoothRep.hom g.1).comp (SmoothRep.hom f.1))
          ((SmoothRep.hom g.2).comp (SmoothRep.hom f.2))) =
      SmoothRep.ofHom ((externalMap (SmoothRep.hom g.1) (SmoothRep.hom g.2)).comp
        (externalMap (SmoothRep.hom f.1) (SmoothRep.hom f.2)))
    rw [externalMap_comp]

/-- Pullback of a smooth representation along a continuous homomorphism. -/
def pullbackObj (φ : K →* G) (hφ : Continuous φ) (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.{0, uK, uV} ℂ K :=
  SmoothRep.of (A.representation.comp φ) (isSmooth_comp φ hφ A.isSmooth)

/-- Pullback along a continuous homomorphism, as a functor with unchanged maps. -/
def pullbackFunctor (φ : K →* G) (hφ : Continuous φ) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uK, uV} ℂ K where
  obj A := pullbackObj φ hφ A
  map f := SmoothRep.ofHom (pullbackMap φ (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The lift of a smooth representation to the carrier `ULift V`. -/
def liftObj (A : SmoothRep.{0, uG, uV} ℂ G) : SmoothRep.{0, uG, max uV uY} ℂ G :=
  SmoothRep.of (lift.{uG, uV, uY} A.representation) (isSmooth_lift A.isSmooth)

/-- The carrier lift as a functor; maps are `up ∘ f ∘ down`. -/
def liftFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, max uV uY} ℂ G where
  obj A := liftObj.{uG, uV, uY} A
  map f := SmoothRep.ofHom (liftMap (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

end Functors

end MixedProductTensor

/-! ## The representations being induced -/

namespace GeneralLinear.Mirabolic.MixedProduct

section Inducing

variable {R : Type uR} [CommRing R] {k r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Case (II): `σ ⊠ τ` pulled back along `leftProjection`, so `h` acts by
`σ(a) ⊗ τ(p)` where `(a, p) = leftProjection h`. -/
def leftInducingRepresentation (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) :
    Representation ℂ (leftSubgroup k r R) (V ⊗[ℂ] W) :=
  (MixedProductTensor.external σ τ).comp leftProjection

theorem leftInducingRepresentation_apply (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) (h : leftSubgroup k r R) :
    leftInducingRepresentation σ τ h =
      TensorProduct.map (σ (leftProjection h).1) (τ (leftProjection h).2) := rfl

@[simp]
theorem leftInducingRepresentation_tmul (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) (h : leftSubgroup k r R) (v : V) (w : W) :
    leftInducingRepresentation σ τ h (v ⊗ₜ w) =
      σ (leftProjection h).1 v ⊗ₜ τ (leftProjection h).2 w := rfl

/-- The block matrix `[a Z; 0 p]` acts by `σ(a) ⊗ τ(p)`. -/
theorem leftInducingRepresentation_leftMatrix
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) (a : Langlands.GeneralLinear k R)
    (p : mirabolic r R) (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftInducingRepresentation σ τ (leftMatrix a p Z) = TensorProduct.map (σ a) (τ p) := by
  rw [leftInducingRepresentation_apply, leftProjection_matrix]

/-- The actual radical acts trivially. -/
theorem leftInducingRepresentation_of_mem_leftKernel
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) {h : leftSubgroup k r R}
    (hh : h ∈ leftKernel k r R) : leftInducingRepresentation σ τ h = 1 := by
  change MixedProductTensor.external σ τ (leftProjection h) = 1
  rw [show leftProjection h = 1 from hh, map_one]

theorem leftInducingRepresentation_leftUnipotent
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V)
    (τ : Representation ℂ (mirabolic r R) W) (Z : Matrix (Fin k) (Fin (r + 1)) R) :
    leftInducingRepresentation σ τ (leftUnipotent Z) = 1 :=
  leftInducingRepresentation_of_mem_leftKernel σ τ (leftProjection_unipotent Z)

/-- Case (III): `τ ⊠ σ` pulled back along `rightProjection`, so `h` acts by
`τ(p) ⊗ σ(a)` where `(p, a) = rightProjection h`. -/
def rightInducingRepresentation (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) :
    Representation ℂ (rightSubgroup k r R) (W ⊗[ℂ] V) :=
  (MixedProductTensor.external τ σ).comp rightProjection

theorem rightInducingRepresentation_apply (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) (h : rightSubgroup k r R) :
    rightInducingRepresentation τ σ h =
      TensorProduct.map (τ (rightProjection h).1) (σ (rightProjection h).2) := rfl

@[simp]
theorem rightInducingRepresentation_tmul (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) (h : rightSubgroup k r R)
    (w : W) (v : V) :
    rightInducingRepresentation τ σ h (w ⊗ₜ v) =
      τ (rightProjection h).1 w ⊗ₜ σ (rightProjection h).2 v := rfl

/-- The case (III) matrix with blocks `p` and `a` acts by `τ(p) ⊗ σ(a)`. -/
theorem rightInducingRepresentation_rightMatrix (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) (p : mirabolic r R)
    (a : Langlands.GeneralLinear k R) (X : Matrix (Fin r) (Fin k) R) :
    rightInducingRepresentation τ σ (rightMatrix p a X) = TensorProduct.map (τ p) (σ a) := by
  rw [rightInducingRepresentation_apply, rightProjection_matrix]

/-- The actual radical acts trivially. -/
theorem rightInducingRepresentation_of_mem_rightKernel (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) {h : rightSubgroup k r R}
    (hh : h ∈ rightKernel k r R) : rightInducingRepresentation τ σ h = 1 := by
  change MixedProductTensor.external τ σ (rightProjection h) = 1
  rw [show rightProjection h = 1 from hh, map_one]

theorem rightInducingRepresentation_rightUnipotent (τ : Representation ℂ (mirabolic r R) W)
    (σ : Representation ℂ (Langlands.GeneralLinear k R) V) (X : Matrix (Fin r) (Fin k) R) :
    rightInducingRepresentation τ σ (rightUnipotent X) = 1 :=
  rightInducingRepresentation_of_mem_rightKernel τ σ (rightProjection_unipotent X)

variable [TopologicalSpace R]

theorem isSmooth_leftInducingRepresentation
    {σ : Representation ℂ (Langlands.GeneralLinear k R) V}
    {τ : Representation ℂ (mirabolic r R) W} (hσ : IsSmooth σ) (hτ : IsSmooth τ) :
    IsSmooth (leftInducingRepresentation σ τ) :=
  isSmooth_comp _ continuous_leftProjection (MixedProductTensor.isSmooth_external hσ hτ)

theorem isSmooth_rightInducingRepresentation {τ : Representation ℂ (mirabolic r R) W}
    {σ : Representation ℂ (Langlands.GeneralLinear k R) V} (hτ : IsSmooth τ) (hσ : IsSmooth σ) :
    IsSmooth (rightInducingRepresentation τ σ) :=
  isSmooth_comp _ continuous_rightProjection (MixedProductTensor.isSmooth_external hτ hσ)

end Inducing

/-! ### The case `k = 0`: both inducing subgroups are the whole group -/

section RankZero

variable {R : Type uR} [CommRing R] {r : ℕ}

theorem mem_leftSubgroup_zero (g : mirabolic (0 + r) R) : g ∈ leftSubgroup 0 r R :=
  (mem_leftSubgroup_iff_entry g).mpr fun _ j => j.elim0

theorem mem_rightSubgroup_zero (g : mirabolic (0 + r) R) : g ∈ rightSubgroup 0 r R :=
  (mem_rightSubgroup_iff_entry g).mpr fun i _ => i.elim0

/-- For `k = 0`, the mirabolic component of `leftProjection` on the whole group. -/
def leftUnitProjection (r : ℕ) : mirabolic (0 + r) R →* mirabolic r R :=
  (MonoidHom.snd _ _).comp
    (leftProjection.comp (Induction.topHom (leftSubgroup 0 r R) mem_leftSubgroup_zero))

/-- For `k = 0`, the mirabolic component of `rightProjection` on the whole group. -/
def rightUnitProjection (r : ℕ) : mirabolic (0 + r) R →* mirabolic r R :=
  (MonoidHom.fst _ _).comp
    (rightProjection.comp (Induction.topHom (rightSubgroup 0 r R) mem_rightSubgroup_zero))

@[simp]
theorem leftUnitProjection_apply (g : mirabolic (0 + r) R) (i j : Fin (r + 1)) :
    (leftUnitProjection r g).val.val i j =
      g.val.val (leftIndex 0 r (Sum.inr i)) (leftIndex 0 r (Sum.inr j)) := rfl

@[simp]
theorem rightUnitProjection_apply (g : mirabolic (0 + r) R) (i j : Fin (r + 1)) :
    (rightUnitProjection r g).val.val i j =
      g.val.val (rightIndex 0 r (Sum.inl i)) (rightIndex 0 r (Sum.inl j)) := rfl

private theorem generalLinear_zero_eq_one (g : Langlands.GeneralLinear 0 R) : g = 1 :=
  Units.ext (Matrix.ext fun i => Fin.elim0 i)

theorem leftUnitProjection_bijective : Function.Bijective (leftUnitProjection (R := R) r) := by
  constructor
  · intro g h hgh
    have e₁ : (leftProjection (⟨g, mem_leftSubgroup_zero g⟩ : leftSubgroup 0 r R)).1 =
        (leftProjection (⟨h, mem_leftSubgroup_zero h⟩ : leftSubgroup 0 r R)).1 :=
      (generalLinear_zero_eq_one _).trans (generalLinear_zero_eq_one _).symm
    have e₂ : (leftProjection (⟨g, mem_leftSubgroup_zero g⟩ : leftSubgroup 0 r R)).2 =
        (leftProjection (⟨h, mem_leftSubgroup_zero h⟩ : leftSubgroup 0 r R)).2 := hgh
    have e₃ : leftOffDiagonal (⟨g, mem_leftSubgroup_zero g⟩ : leftSubgroup 0 r R) =
        leftOffDiagonal (⟨h, mem_leftSubgroup_zero h⟩ : leftSubgroup 0 r R) :=
      Matrix.ext fun i => Fin.elim0 i
    have := (leftMatrix_parts (⟨g, mem_leftSubgroup_zero g⟩ : leftSubgroup 0 r R)).symm.trans
      ((congrArg₂ (fun a b => leftMatrix a b _) e₁ e₂).trans
        ((congrArg (leftMatrix _ _) e₃).trans
          (leftMatrix_parts (⟨h, mem_leftSubgroup_zero h⟩ : leftSubgroup 0 r R))))
    exact congrArg Subtype.val this
  · intro p
    refine ⟨(leftSection (k := 0) (r := r) (R := R) (1, p)).val, ?_⟩
    change (leftProjection (Induction.topHom (leftSubgroup 0 r R) mem_leftSubgroup_zero
      (leftSection (k := 0) (r := r) (R := R) (1, p)).val)).2 = p
    rw [show Induction.topHom (leftSubgroup 0 r R) mem_leftSubgroup_zero
      (leftSection (k := 0) (r := r) (R := R) (1, p)).val = leftSection (1, p) from rfl,
      leftProjection_section]

theorem rightUnitProjection_bijective :
    Function.Bijective (rightUnitProjection (R := R) r) := by
  constructor
  · intro g h hgh
    have e₁ : (rightProjection (⟨g, mem_rightSubgroup_zero g⟩ : rightSubgroup 0 r R)).1 =
        (rightProjection (⟨h, mem_rightSubgroup_zero h⟩ : rightSubgroup 0 r R)).1 := hgh
    have e₂ : (rightProjection (⟨g, mem_rightSubgroup_zero g⟩ : rightSubgroup 0 r R)).2 =
        (rightProjection (⟨h, mem_rightSubgroup_zero h⟩ : rightSubgroup 0 r R)).2 :=
      (generalLinear_zero_eq_one _).trans (generalLinear_zero_eq_one _).symm
    have e₃ : rightOffDiagonal (⟨g, mem_rightSubgroup_zero g⟩ : rightSubgroup 0 r R) =
        rightOffDiagonal (⟨h, mem_rightSubgroup_zero h⟩ : rightSubgroup 0 r R) :=
      Matrix.ext fun _ j => Fin.elim0 j
    have := (rightMatrix_parts (⟨g, mem_rightSubgroup_zero g⟩ : rightSubgroup 0 r R)).symm.trans
      ((congrArg₂ (fun a b => rightMatrix a b _) e₁ e₂).trans
        ((congrArg (rightMatrix _ _) e₃).trans
          (rightMatrix_parts (⟨h, mem_rightSubgroup_zero h⟩ : rightSubgroup 0 r R))))
    exact congrArg Subtype.val this
  · intro p
    refine ⟨(rightSection (k := 0) (r := r) (R := R) (p, 1)).val, ?_⟩
    change (rightProjection (Induction.topHom (rightSubgroup 0 r R) mem_rightSubgroup_zero
      (rightSection (k := 0) (r := r) (R := R) (p, 1)).val)).1 = p
    rw [show Induction.topHom (rightSubgroup 0 r R) mem_rightSubgroup_zero
      (rightSection (k := 0) (r := r) (R := R) (p, 1)).val = rightSection (p, 1) from rfl,
      rightProjection_section]

variable [TopologicalSpace R]

theorem continuous_leftUnitProjection : Continuous (leftUnitProjection (R := R) r) :=
  continuous_snd.comp (continuous_leftProjection.comp (Induction.continuous_topHom _ _))

theorem continuous_rightUnitProjection : Continuous (rightUnitProjection (R := R) r) :=
  continuous_fst.comp (continuous_rightProjection.comp (Induction.continuous_topHom _ _))

end RankZero

end GeneralLinear.Mirabolic.MixedProduct

/-! ## Characters, products and their laws for a supplied p-adic realization -/

namespace PadicField.TopologicalData

open GeneralLinear GeneralLinear.Mirabolic.MixedProduct

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### The explicit total characters -/

/-- Case (II): `χ_L(a, p) = ν_k(a)^((r+1)/2) · ν_(r+1)(p)^(-k/2)` on `GL_k × P_(r+1)`,
with `ν_n = |det|_F` the residue-normalized determinant norm. -/
def leftLeviCharacter (k r : ℕ) :
    GeneralLinear k F.Carrier × mirabolic r F.Carrier →* ℂˣ :=
  (realPowerCharacter (T.determinantNorm k) (((r + 1 : ℕ) : ℝ) / 2)).comp
      (MonoidHom.fst _ _) *
    (realPowerCharacter ((T.determinantNorm (r + 1)).comp (mirabolic r F.Carrier).subtype)
      (-((k : ℝ) / 2))).comp (MonoidHom.snd _ _)

theorem leftLeviCharacter_apply (k r : ℕ)
    (q : GeneralLinear k F.Carrier × mirabolic r F.Carrier) :
    (T.leftLeviCharacter k r q : ℂ) =
      ((((T.determinantNorm k q.1 : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm (r + 1) q.2.val : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) :=
  rfl

/-- Case (III): `χ_R(p, a) = ν_r(d)^(k/2) · ν_k(a)^(-(r+1)/2)`, `d = projection p`. -/
def rightLeviCharacter (k r : ℕ) :
    mirabolic r F.Carrier × GeneralLinear k F.Carrier →* ℂˣ :=
  (realPowerCharacter ((T.determinantNorm r).comp Mirabolic.projection) ((k : ℝ) / 2)).comp
      (MonoidHom.fst _ _) *
    (realPowerCharacter (T.determinantNorm k) (-(((r + 1 : ℕ) : ℝ) / 2))).comp
      (MonoidHom.snd _ _)

theorem rightLeviCharacter_apply (k r : ℕ)
    (q : mirabolic r F.Carrier × GeneralLinear k F.Carrier) :
    (T.rightLeviCharacter k r q : ℂ) =
      ((((T.determinantNorm r (Mirabolic.projection q.1) : ℝ≥0) : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm k q.2 : ℝ≥0) : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) / 2)) : ℝ) : ℂ) :=
  rfl

/-- The half-power `ν(d)^(k/2) ν(a)^(-r/2)` of the determinant of `X ↦ d X a⁻¹` on
`r × k` matrices, the case (III) rectangle action. -/
def rightRectangleHalfCharacter (k r : ℕ) :
    mirabolic r F.Carrier × GeneralLinear k F.Carrier →* ℂˣ :=
  (realPowerCharacter ((T.determinantNorm r).comp Mirabolic.projection) ((k : ℝ) / 2)).comp
      (MonoidHom.fst _ _) *
    (realPowerCharacter (T.determinantNorm k) (-((r : ℝ) / 2))).comp (MonoidHom.snd _ _)

/-- The source's case (III) twist `ε(p, a) = ν_k(a)^(-1/2)`. -/
def rightEpsilonCharacter (k r : ℕ) :
    mirabolic r F.Carrier × GeneralLinear k F.Carrier →* ℂˣ :=
  (realPowerCharacter (T.determinantNorm k) (-(1 / 2 : ℝ))).comp (MonoidHom.snd _ _)

/-- `χ_R` is the rectangle half-power times the retained twist `ε`. -/
theorem rightLeviCharacter_eq_mul (k r : ℕ) :
    T.rightLeviCharacter k r = T.rightRectangleHalfCharacter k r * T.rightEpsilonCharacter k r := by
  have h : -(((r + 1 : ℕ) : ℝ) / 2) = -((r : ℝ) / 2) + -(1 / 2 : ℝ) := by
    push_cast
    ring
  rw [rightLeviCharacter, rightRectangleHalfCharacter, rightEpsilonCharacter, h,
    realPowerCharacter_add, MonoidHom.mul_comp]
  ext q
  simp only [MonoidHom.mul_apply, mul_assoc]

private theorem determinantNorm_zero (g : GeneralLinear 0 F.Carrier) :
    T.determinantNorm 0 g = 1 := by
  rw [show g = 1 from Units.ext (Matrix.ext fun i => Fin.elim0 i), map_one]

/-- For `k = 0` the left character is trivial. -/
theorem leftLeviCharacter_zero_left (r : ℕ) : T.leftLeviCharacter 0 r = 1 := by
  ext q
  rw [leftLeviCharacter_apply, T.determinantNorm_zero]
  simp

/-- For `k = 0` the right character is trivial. -/
theorem rightLeviCharacter_zero_left (r : ℕ) : T.rightLeviCharacter 0 r = 1 := by
  ext q
  rw [rightLeviCharacter_apply, T.determinantNorm_zero]
  simp

/-- For `r = 0`, `χ_L(a, p) = ν_k(a)^(1/2)`. -/
theorem leftLeviCharacter_zero_right_apply (k : ℕ)
    (q : GeneralLinear k F.Carrier × mirabolic 0 F.Carrier) :
    (T.leftLeviCharacter k 0 q : ℂ) =
      ((((T.determinantNorm k q.1 : ℝ≥0) : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [leftLeviCharacter_apply, show q.2 = 1 from Subsingleton.elim _ _]
  simp

/-- For `r = 0`, `χ_R(p, a) = ν_k(a)^(-1/2)`: only the retained twist survives. -/
theorem rightLeviCharacter_zero_right_apply (k : ℕ)
    (q : mirabolic 0 F.Carrier × GeneralLinear k F.Carrier) :
    (T.rightLeviCharacter k 0 q : ℂ) =
      ((((T.determinantNorm k q.2 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [rightLeviCharacter_apply, T.determinantNorm_zero]
  simp

theorem isOpen_ker_leftLeviCharacter_comp (k r : ℕ) :
    letI := T.topology
    IsOpen (((T.leftLeviCharacter k r).comp leftProjection).ker :
      Set (leftSubgroup k r F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let φ₁ : leftSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm k).comp ((MonoidHom.fst _ _).comp leftProjection)
  let φ₂ : leftSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    ((T.determinantNorm (r + 1)).comp (mirabolic r F.Carrier).subtype).comp
      ((MonoidHom.snd _ _).comp leftProjection)
  have h₁ : IsOpen (φ₁.ker : Set (leftSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm k).preimage
      (continuous_fst.comp continuous_leftProjection)
  have h₂ : IsOpen (φ₂.ker : Set (leftSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap, ← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact ((T.isOpen_ker_determinantNorm (r + 1)).preimage continuous_subtype_val).preimage
      (continuous_snd.comp continuous_leftProjection)
  refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
  · intro h hh
    obtain ⟨hh₁, hh₂⟩ := Subgroup.mem_inf.mp hh
    have e₁ : T.determinantNorm k (leftProjection h).1 = 1 := hh₁
    have e₂ : T.determinantNorm (r + 1) (leftProjection h).2.val = 1 := hh₂
    change T.leftLeviCharacter k r (leftProjection h) = 1
    simp [leftLeviCharacter, realPowerCharacter, e₁, e₂]
  · rw [Subgroup.coe_inf]
    exact h₁.inter h₂

theorem isOpen_ker_rightLeviCharacter_comp (k r : ℕ) :
    letI := T.topology
    IsOpen (((T.rightLeviCharacter k r).comp rightProjection).ker :
      Set (rightSubgroup k r F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let φ₁ : rightSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm r).comp (Mirabolic.projection.comp
      ((MonoidHom.fst _ _).comp rightProjection))
  let φ₂ : rightSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm k).comp ((MonoidHom.snd _ _).comp rightProjection)
  have h₁ : IsOpen (φ₁.ker : Set (rightSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm r).preimage
      (Mirabolic.continuous_projection.comp (continuous_fst.comp continuous_rightProjection))
  have h₂ : IsOpen (φ₂.ker : Set (rightSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm k).preimage
      (continuous_snd.comp continuous_rightProjection)
  refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
  · intro h hh
    obtain ⟨hh₁, hh₂⟩ := Subgroup.mem_inf.mp hh
    have e₁ : T.determinantNorm r (Mirabolic.projection (rightProjection h).1) = 1 := hh₁
    have e₂ : T.determinantNorm k (rightProjection h).2 = 1 := hh₂
    change T.rightLeviCharacter k r (rightProjection h) = 1
    simp [rightLeviCharacter, realPowerCharacter, e₁, e₂]
  · rw [Subgroup.coe_inf]
    exact h₁.inter h₂

/-- The case (II) smooth character `h ↦ χ_L(leftProjection h)` on the inducing subgroup. -/
def leftCharacter (k r : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (leftSubgroup k r F.Carrier) :=
  letI := T.topology
  { toMonoidHom := (T.leftLeviCharacter k r).comp leftProjection
    isOpen_ker := T.isOpen_ker_leftLeviCharacter_comp k r }

/-- The case (III) smooth character `h ↦ χ_R(rightProjection h)` on the inducing subgroup. -/
def rightCharacter (k r : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (rightSubgroup k r F.Carrier) :=
  letI := T.topology
  { toMonoidHom := (T.rightLeviCharacter k r).comp rightProjection
    isOpen_ker := T.isOpen_ker_rightLeviCharacter_comp k r }

theorem leftCharacter_apply (k r : ℕ) (h : leftSubgroup k r F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom h = T.leftLeviCharacter k r (leftProjection h) := rfl

theorem rightCharacter_apply (k r : ℕ) (h : rightSubgroup k r F.Carrier) :
    letI := T.topology
    (T.rightCharacter k r).toMonoidHom h = T.rightLeviCharacter k r (rightProjection h) := rfl

/-- The value on `[a Z; 0 p]`. -/
theorem leftCharacter_leftMatrix (k r : ℕ) (a : GeneralLinear k F.Carrier)
    (p : mirabolic r F.Carrier) (Z : Matrix (Fin k) (Fin (r + 1)) F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom (leftMatrix a p Z) = T.leftLeviCharacter k r (a, p) := by
  rw [leftCharacter_apply, leftProjection_matrix]

/-- The value on the case (III) matrix with blocks `p` and `a`. -/
theorem rightCharacter_rightMatrix (k r : ℕ) (p : mirabolic r F.Carrier)
    (a : GeneralLinear k F.Carrier) (X : Matrix (Fin r) (Fin k) F.Carrier) :
    letI := T.topology
    (T.rightCharacter k r).toMonoidHom (rightMatrix p a X) = T.rightLeviCharacter k r (p, a) := by
  rw [rightCharacter_apply, rightProjection_matrix]

theorem leftCharacter_leftSection (k r : ℕ)
    (q : GeneralLinear k F.Carrier × mirabolic r F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom (leftSection q) = T.leftLeviCharacter k r q := by
  rw [leftCharacter_apply, leftProjection_section]

theorem rightCharacter_rightSection (k r : ℕ)
    (q : mirabolic r F.Carrier × GeneralLinear k F.Carrier) :
    letI := T.topology
    (T.rightCharacter k r).toMonoidHom (rightSection q) = T.rightLeviCharacter k r q := by
  rw [rightCharacter_apply, rightProjection_section]

/-- The character is trivial on the actual radical. -/
theorem leftCharacter_of_mem_leftKernel (k r : ℕ) {h : leftSubgroup k r F.Carrier}
    (hh : h ∈ leftKernel k r F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom h = 1 := by
  rw [leftCharacter_apply, show leftProjection h = 1 from hh, map_one]

/-- The character is trivial on the actual radical. -/
theorem rightCharacter_of_mem_rightKernel (k r : ℕ) {h : rightSubgroup k r F.Carrier}
    (hh : h ∈ rightKernel k r F.Carrier) :
    letI := T.topology
    (T.rightCharacter k r).toMonoidHom h = 1 := by
  rw [rightCharacter_apply, show rightProjection h = 1 from hh, map_one]

theorem leftCharacter_zero_left (r : ℕ) :
    letI := T.topology
    (T.leftCharacter 0 r).toMonoidHom = 1 := by
  change (T.leftLeviCharacter 0 r).comp leftProjection = 1
  rw [T.leftLeviCharacter_zero_left, MonoidHom.one_comp]

theorem rightCharacter_zero_left (r : ℕ) :
    letI := T.topology
    (T.rightCharacter 0 r).toMonoidHom = 1 := by
  change (T.rightLeviCharacter 0 r).comp rightProjection = 1
  rw [T.rightLeviCharacter_zero_left, MonoidHom.one_comp]

/-! ### The two products -/

/-- BZ77 §4.12(II): the product `A × B` of `A ∈ Rep(GL_k)` and `B ∈ Rep(P_(r+1))`,
a smooth representation of `P_(k+r+1)`. It is the published normalized compact
induction, from `leftSubgroup k r`, of `A ⊠ B` pulled back along `leftProjection`,
twisted by `χ_L`. -/
def leftMixedProductFunctor (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  MixedProductTensor.externalFunctor ⋙
    MixedProductTensor.pullbackFunctor leftProjection continuous_leftProjection ⋙
      SmoothRep.toRep ⋙
        Induction.normalizedCompactInductionFunctor (leftSubgroup k r F.Carrier)
          (T.leftCharacter k r)

/-- BZ77 §4.12(III): the product `B × A` of `B ∈ Rep(P_(r+1))` and `A ∈ Rep(GL_k)`,
a smooth representation of `P_(k+r+1)`. It is the published normalized compact
induction, from `rightSubgroup k r`, of `B ⊠ A` pulled back along `rightProjection`,
twisted by `χ_R`. -/
def rightMixedProductFunctor (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  MixedProductTensor.externalFunctor ⋙
    MixedProductTensor.pullbackFunctor rightProjection continuous_rightProjection ⋙
      SmoothRep.toRep ⋙
        Induction.normalizedCompactInductionFunctor (rightSubgroup k r F.Carrier)
          (T.rightCharacter k r)

variable {k r : ℕ}

/-- The object is the actual normalized compact induction of the pulled-back tensor. -/
theorem leftMixedProductFunctor_obj
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    (T.leftMixedProductFunctor k r).obj X =
      SmoothRep.of
        (Induction.normalizedCompactInduced (leftSubgroup k r F.Carrier) (T.leftCharacter k r)
          (leftInducingRepresentation X.1.representation X.2.representation))
        (Induction.compactInduced_smooth _ _) := rfl

/-- The object is the actual normalized compact induction of the pulled-back tensor. -/
theorem rightMixedProductFunctor_obj
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    (T.rightMixedProductFunctor k r).obj X =
      SmoothRep.of
        (Induction.normalizedCompactInduced (rightSubgroup k r F.Carrier) (T.rightCharacter k r)
          (rightInducingRepresentation X.1.representation X.2.representation))
        (Induction.compactInduced_smooth _ _) := rfl

/-- Maps are compact induction of the twisted, pulled-back tensor `f ⊗ g`. -/
theorem leftMixedProductFunctor_map
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    SmoothRep.hom ((T.leftMixedProductFunctor k r).map φ) =
      Induction.compactInducedMap (leftSubgroup k r F.Carrier)
        (twistIntertwining (T.leftCharacter k r).toMonoidHom
          (MixedProductTensor.pullbackMap leftProjection
            (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))) := rfl

/-- Maps are compact induction of the twisted, pulled-back tensor `f ⊗ g`. -/
theorem rightMixedProductFunctor_map
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    SmoothRep.hom ((T.rightMixedProductFunctor k r).map φ) =
      Induction.compactInducedMap (rightSubgroup k r F.Carrier)
        (twistIntertwining (T.rightCharacter k r).toMonoidHom
          (MixedProductTensor.pullbackMap rightProjection
            (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))) := rfl

/-! ### Evaluation, covariance, right translation and maps -/

/-- The value `f(x) ∈ A ⊗ B` at `x ∈ P_(k+r+1)` of a vector `f` of `A × B`. -/
def leftMixedEval
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) : X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.eval (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation))
    (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
      (twist (T.leftCharacter k r).toMonoidHom
        (leftInducingRepresentation X.1.representation X.2.representation)) from f).1 x

/-- The value `f(x) ∈ B ⊗ A` at `x ∈ P_(k+r+1)` of a vector `f` of `B × A`. -/
def rightMixedEval
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) : X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.eval (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation))
    (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
      (twist (T.rightCharacter k r).toMonoidHom
        (rightInducingRepresentation X.1.representation X.2.representation)) from f).1 x

/-- Vectors of `A × B` are determined by their values. -/
theorem leftMixedEval_injective
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    Function.Injective (T.leftMixedEval X) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => congrFun h x)))

/-- Vectors of `B × A` are determined by their values. -/
theorem rightMixedEval_injective
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) :
    Function.Injective (T.rightMixedEval X) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => congrFun h x)))

/-- Covariance `f(h x) = χ_L(h) • (A ⊠ B)(leftProjection h) (f x)`. -/
theorem leftMixedEval_covariant
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (h : leftSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) =
      (T.leftLeviCharacter k r (leftProjection h) : ℂ) •
        leftInducingRepresentation X.1.representation X.2.representation h
          (T.leftMixedEval X f x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) from f).1.1.2 h x

/-- Covariance `f(h x) = χ_R(h) • (B ⊠ A)(rightProjection h) (f x)`. -/
theorem rightMixedEval_covariant
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (h : rightSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.rightMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) =
      (T.rightLeviCharacter k r (rightProjection h) : ℂ) •
        rightInducingRepresentation X.1.representation X.2.representation h
          (T.rightMixedEval X f x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)) from f).1.1.2 h x

/-- The source formula `f([a Z; 0 p] x) = χ_L(a, p) • (A(a) ⊗ B(p)) (f x)`. -/
theorem leftMixedEval_leftMatrix_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (a : GeneralLinear k F.Carrier) (q : mirabolic r F.Carrier)
    (Z : Matrix (Fin k) (Fin (r + 1)) F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((leftMatrix a q Z : mirabolic (k + r) F.Carrier) * x) =
      (T.leftLeviCharacter k r (a, q) : ℂ) •
        TensorProduct.map (X.1.representation a) (X.2.representation q)
          (T.leftMixedEval X f x) := by
  rw [T.leftMixedEval_covariant, leftInducingRepresentation_leftMatrix, leftProjection_matrix]

/-- The source formula `f(m x) = χ_R(p, a) • (B(p) ⊗ A(a)) (f x)` for the case (III)
matrix `m` with blocks `p`, `a` and rectangle `X`. -/
theorem rightMixedEval_rightMatrix_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (q : mirabolic r F.Carrier) (a : GeneralLinear k F.Carrier)
    (Y : Matrix (Fin r) (Fin k) F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.rightMixedEval X f ((rightMatrix q a Y : mirabolic (k + r) F.Carrier) * x) =
      (T.rightLeviCharacter k r (q, a) : ℂ) •
        TensorProduct.map (X.1.representation q) (X.2.representation a)
          (T.rightMixedEval X f x) := by
  rw [T.rightMixedEval_covariant, rightInducingRepresentation_rightMatrix,
    rightProjection_matrix]

/-- Left multiplication by the actual radical does not change values. -/
theorem leftMixedEval_of_mem_leftKernel_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    {h : leftSubgroup k r F.Carrier} (hh : h ∈ leftKernel k r F.Carrier)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) = T.leftMixedEval X f x := by
  rw [T.leftMixedEval_covariant, leftInducingRepresentation_of_mem_leftKernel _ _ hh,
    show leftProjection h = 1 from hh, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- Left multiplication by the actual radical does not change values. -/
theorem rightMixedEval_of_mem_rightKernel_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    {h : rightSubgroup k r F.Carrier} (hh : h ∈ rightKernel k r F.Carrier)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.rightMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) = T.rightMixedEval X f x := by
  rw [T.rightMixedEval_covariant, rightInducingRepresentation_of_mem_rightKernel _ _ hh,
    show rightProjection h = 1 from hh, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- The action is right translation: `(g · f)(x) = f(x g)`. -/
theorem leftMixedProductFunctor_action
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (g : mirabolic (k + r) F.Carrier)
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X (((T.leftMixedProductFunctor k r).obj X).representation g f) x =
      T.leftMixedEval X f (x * g) := rfl

/-- The action is right translation: `(g · f)(x) = f(x g)`. -/
theorem rightMixedProductFunctor_action
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (g : mirabolic (k + r) F.Carrier)
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.rightMixedEval X (((T.rightMixedProductFunctor k r).obj X).representation g f) x =
      T.rightMixedEval X f (x * g) := rfl

/-- Maps act by postcomposition with `f ⊗ g`. -/
theorem leftMixedProductFunctor_map_eval
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y)
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval Y (SmoothRep.hom ((T.leftMixedProductFunctor k r).map φ) f) x =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
        (T.leftMixedEval X f x) := rfl

/-- Maps act by postcomposition with `g ⊗ f`. -/
theorem rightMixedProductFunctor_map_eval
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y)
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.rightMixedEval Y (SmoothRep.hom ((T.rightMixedProductFunctor k r).map φ) f) x =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
        (T.rightMixedEval X f x) := rfl

/-- Each vector has a single open subgroup of right stabilizers. -/
theorem leftMixedEval_exists_openSubgroup
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X) :
    letI := T.topology
    ∃ K : OpenSubgroup (mirabolic (k + r) F.Carrier), ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
      T.leftMixedEval X f (x * (u : mirabolic (k + r) F.Carrier)) = T.leftMixedEval X f x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  obtain ⟨K, hK⟩ := (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) from f).1.2
  exact ⟨K, fun u x => congrArg (fun φ => φ.1 x) (hK u)⟩

/-- Each vector has a single open subgroup of right stabilizers. -/
theorem rightMixedEval_exists_openSubgroup
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X) :
    letI := T.topology
    ∃ K : OpenSubgroup (mirabolic (k + r) F.Carrier), ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
      T.rightMixedEval X f (x * (u : mirabolic (k + r) F.Carrier)) = T.rightMixedEval X f x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  obtain ⟨K, hK⟩ := (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)) from f).1.2
  exact ⟨K, fun u x => congrArg (fun φ => φ.1 x) (hK u)⟩

/-- The nonzero support, projected to `H \ P_(k+r+1)`, is compact. -/
theorem leftMixedEval_isCompact_quotientSupport
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    IsCompact (Induction.quotientSupport (leftSubgroup k r F.Carrier) (T.leftMixedEval X f)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) from f).2

/-- The nonzero support, projected to `H \ P_(k+r+1)`, is compact. -/
theorem rightMixedEval_isCompact_quotientSupport
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    IsCompact (Induction.quotientSupport (rightSubgroup k r F.Carrier)
      (T.rightMixedEval X f)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)) from f).2

/-- A vector of `A × B` from a covariant function with a single open subgroup of right
stabilizers and compact projected support. -/
def leftMixedMk
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : mirabolic (k + r) F.Carrier → X.1 ⊗[ℂ] X.2)
    (hcov : letI := T.topology
      ∀ (h : leftSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier),
        f ((h : mirabolic (k + r) F.Carrier) * x) =
          (T.leftLeviCharacter k r (leftProjection h) : ℂ) •
            leftInducingRepresentation X.1.representation X.2.representation h (f x))
    (K : letI := T.topology; OpenSubgroup (mirabolic (k + r) F.Carrier))
    (hK : letI := T.topology
      ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
        f (x * (u : mirabolic (k + r) F.Carrier)) = f x)
    (hc : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1)
      IsCompact (Induction.quotientSupport (leftSubgroup k r F.Carrier) f)) :
    letI := T.topology
    (T.leftMixedProductFunctor k r).obj X :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.compactFunctionOf (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) f hcov K hK hc

/-- A vector of `B × A` from a covariant function with a single open subgroup of right
stabilizers and compact projected support. -/
def rightMixedMk
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : mirabolic (k + r) F.Carrier → X.1 ⊗[ℂ] X.2)
    (hcov : letI := T.topology
      ∀ (h : rightSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier),
        f ((h : mirabolic (k + r) F.Carrier) * x) =
          (T.rightLeviCharacter k r (rightProjection h) : ℂ) •
            rightInducingRepresentation X.1.representation X.2.representation h (f x))
    (K : letI := T.topology; OpenSubgroup (mirabolic (k + r) F.Carrier))
    (hK : letI := T.topology
      ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
        f (x * (u : mirabolic (k + r) F.Carrier)) = f x)
    (hc : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1)
      IsCompact (Induction.quotientSupport (rightSubgroup k r F.Carrier) f)) :
    letI := T.topology
    (T.rightMixedProductFunctor k r).obj X :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.compactFunctionOf (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)) f hcov K hK hc

theorem leftMixedEval_mk
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : mirabolic (k + r) F.Carrier → X.1 ⊗[ℂ] X.2)
    (hcov : letI := T.topology
      ∀ (h : leftSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier),
        f ((h : mirabolic (k + r) F.Carrier) * x) =
          (T.leftLeviCharacter k r (leftProjection h) : ℂ) •
            leftInducingRepresentation X.1.representation X.2.representation h (f x))
    (K : letI := T.topology; OpenSubgroup (mirabolic (k + r) F.Carrier))
    (hK : letI := T.topology
      ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
        f (x * (u : mirabolic (k + r) F.Carrier)) = f x)
    (hc : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1)
      IsCompact (Induction.quotientSupport (leftSubgroup k r F.Carrier) f)) :
    T.leftMixedEval X (T.leftMixedMk X f hcov K hK hc) = f := rfl

theorem rightMixedEval_mk
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : mirabolic (k + r) F.Carrier → X.1 ⊗[ℂ] X.2)
    (hcov : letI := T.topology
      ∀ (h : rightSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier),
        f ((h : mirabolic (k + r) F.Carrier) * x) =
          (T.rightLeviCharacter k r (rightProjection h) : ℂ) •
            rightInducingRepresentation X.1.representation X.2.representation h (f x))
    (K : letI := T.topology; OpenSubgroup (mirabolic (k + r) F.Carrier))
    (hK : letI := T.topology
      ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
        f (x * (u : mirabolic (k + r) F.Carrier)) = f x)
    (hc : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1)
      IsCompact (Induction.quotientSupport (rightSubgroup k r F.Carrier) f)) :
    T.rightMixedEval X (T.rightMixedMk X f hcov K hK hc) = f := rfl

/-! ### The unit -/

/-- The genuine one-dimensional unit: `ULift ℂ` with the trivial action of `GL_0(F)`. -/
def mixedProductUnit :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  SmoothRep.of (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ))
    MixedProductTensor.isSmooth_trivial

theorem mixedProductUnit_representation :
    letI := T.topology
    (T.mixedProductUnit.{uF, uV}).representation =
      Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ) := rfl

theorem finrank_mixedProductUnit :
    letI := T.topology
    Module.finrank ℂ (T.mixedProductUnit.{uF, uV}) = 1 :=
  (ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq.trans (Module.finrank_self ℂ)

variable (r) in
/-- `1 × B ≃ B`: evaluation at `1`, the tensor unit and the lift of `B`, with `P_(0+r+1)`
acting on `B` through `leftUnitProjection`. -/
def leftMixedProductUnitEquiv
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    letI := T.topology
    ((T.leftMixedProductFunctor 0 r).obj (T.mixedProductUnit, B)).representation.Equiv
      (MixedProductTensor.lift.{uF, uV, uF} (B.representation.comp (leftUnitProjection r))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + r + 1)
  (Induction.compactInducedTopEquiv (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero _
      ((isSmooth_twist_iff _ _ (T.leftCharacter 0 r).isOpen_ker).mpr
        (isSmooth_leftInducingRepresentation MixedProductTensor.isSmooth_trivial
          B.isSmooth))).trans
    ((MixedProductTensor.compEquiv _
        (MixedProductTensor.twistOneEquiv _ (T.leftCharacter_zero_left r) _)).trans
      ((MixedProductTensor.compEquiv
          (leftProjection.comp (Induction.topHom (leftSubgroup 0 r F.Carrier)
            mem_leftSubgroup_zero))
          (MixedProductTensor.externalUnitLeftEquiv B.representation)).trans
        (MixedProductTensor.liftEquiv _)))

variable (r) in
/-- `B × 1 ≃ B`: evaluation at `1`, the tensor unit and the lift of `B`, with `P_(0+r+1)`
acting on `B` through `rightUnitProjection`. -/
def rightMixedProductUnitEquiv
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    letI := T.topology
    ((T.rightMixedProductFunctor 0 r).obj (B, T.mixedProductUnit)).representation.Equiv
      (MixedProductTensor.lift.{uF, uV, uF} (B.representation.comp (rightUnitProjection r))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + r + 1)
  (Induction.compactInducedTopEquiv (rightSubgroup 0 r F.Carrier) mem_rightSubgroup_zero _
      ((isSmooth_twist_iff _ _ (T.rightCharacter 0 r).isOpen_ker).mpr
        (isSmooth_rightInducingRepresentation B.isSmooth
          MixedProductTensor.isSmooth_trivial))).trans
    ((MixedProductTensor.compEquiv _
        (MixedProductTensor.twistOneEquiv _ (T.rightCharacter_zero_left r) _)).trans
      ((MixedProductTensor.compEquiv
          (rightProjection.comp (Induction.topHom (rightSubgroup 0 r F.Carrier)
            mem_rightSubgroup_zero))
          (MixedProductTensor.externalUnitRightEquiv B.representation)).trans
        (MixedProductTensor.liftEquiv _)))

theorem leftMixedProductUnitEquiv_apply
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor 0 r).obj (T.mixedProductUnit, B)) :
    letI := T.topology
    (T.leftMixedProductUnitEquiv r B f).down =
      MixedProductTensor.unitTensorLeft B (T.leftMixedEval (T.mixedProductUnit, B) f 1) := rfl

theorem rightMixedProductUnitEquiv_apply
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor 0 r).obj (B, T.mixedProductUnit)) :
    letI := T.topology
    (T.rightMixedProductUnitEquiv r B f).down =
      MixedProductTensor.unitTensorRight B (T.rightMixedEval (B, T.mixedProductUnit) f 1) := rfl

/-- The inverse sends `v` to the function whose value at `x` is
`1 ⊗ B(leftUnitProjection x) v`, stated after the tensor unit map. -/
theorem unitTensorLeft_leftMixedEval_symm
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (v : ULift.{uF} B) (x : mirabolic (0 + r) F.Carrier) :
    letI := T.topology
    MixedProductTensor.unitTensorLeft B
        (T.leftMixedEval (T.mixedProductUnit, B) ((T.leftMixedProductUnitEquiv r B).symm v) x) =
      B.representation (leftUnitProjection r x) v.down := by
  let := T.topology
  change MixedProductTensor.unitTensorLeft B
      (((T.leftCharacter 0 r).toMonoidHom
          (Induction.topHom (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero x) : ℂ) •
        MixedProductTensor.external
          (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ)) B.representation
          (leftProjection (Induction.topHom (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero x))
          ((MixedProductTensor.unitTensorLeft B).symm v.down)) = _
  rw [T.leftCharacter_zero_left, MonoidHom.one_apply, Units.val_one, one_smul]
  exact (Representation.IntertwiningMap.isIntertwining _ _
    (MixedProductTensor.externalUnitLeftEquiv B.representation).toIntertwiningMap _ _).trans
    (congrArg _ ((MixedProductTensor.unitTensorLeft B).apply_symm_apply v.down))

/-- The inverse sends `v` to the function whose value at `x` is
`B(rightUnitProjection x) v ⊗ 1`, stated after the tensor unit map. -/
theorem unitTensorRight_rightMixedEval_symm
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (v : ULift.{uF} B) (x : mirabolic (0 + r) F.Carrier) :
    letI := T.topology
    MixedProductTensor.unitTensorRight B
        (T.rightMixedEval (B, T.mixedProductUnit) ((T.rightMixedProductUnitEquiv r B).symm v) x) =
      B.representation (rightUnitProjection r x) v.down := by
  let := T.topology
  change MixedProductTensor.unitTensorRight B
      (((T.rightCharacter 0 r).toMonoidHom
          (Induction.topHom (rightSubgroup 0 r F.Carrier) mem_rightSubgroup_zero x) : ℂ) •
        MixedProductTensor.external B.representation
          (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ))
          (rightProjection (Induction.topHom (rightSubgroup 0 r F.Carrier) mem_rightSubgroup_zero x))
          ((MixedProductTensor.unitTensorRight B).symm v.down)) = _
  rw [T.rightCharacter_zero_left, MonoidHom.one_apply, Units.val_one, one_smul]
  exact (Representation.IntertwiningMap.isIntertwining _ _
    (MixedProductTensor.externalUnitRightEquiv B.representation).toIntertwiningMap _ _).trans
    (congrArg _ ((MixedProductTensor.unitTensorRight B).apply_symm_apply v.down))

theorem leftMixedProductUnitEquiv_naturality
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    (φ : letI := T.topology; B ⟶ B')
    (f : letI := T.topology; (T.leftMixedProductFunctor 0 r).obj (T.mixedProductUnit, B)) :
    letI := T.topology
    T.leftMixedProductUnitEquiv r B'
        (SmoothRep.hom ((T.leftMixedProductFunctor 0 r).map
          (CategoryTheory.Prod.mkHom (𝟙 T.mixedProductUnit) φ)) f) =
      ULift.up (SmoothRep.hom φ (T.leftMixedProductUnitEquiv r B f).down) := by
  let := T.topology
  apply ULift.ext
  rw [leftMixedProductUnitEquiv_apply, leftMixedProductUnitEquiv_apply,
    leftMixedProductFunctor_map_eval]
  exact MixedProductTensor.unitTensorLeft_naturality (SmoothRep.hom φ).toLinearMap _

theorem rightMixedProductUnitEquiv_naturality
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    (φ : letI := T.topology; B ⟶ B')
    (f : letI := T.topology; (T.rightMixedProductFunctor 0 r).obj (B, T.mixedProductUnit)) :
    letI := T.topology
    T.rightMixedProductUnitEquiv r B'
        (SmoothRep.hom ((T.rightMixedProductFunctor 0 r).map
          (CategoryTheory.Prod.mkHom φ (𝟙 T.mixedProductUnit))) f) =
      ULift.up (SmoothRep.hom φ (T.rightMixedProductUnitEquiv r B f).down) := by
  let := T.topology
  apply ULift.ext
  rw [rightMixedProductUnitEquiv_apply, rightMixedProductUnitEquiv_apply,
    rightMixedProductFunctor_map_eval]
  exact MixedProductTensor.unitTensorRight_naturality (SmoothRep.hom φ).toLinearMap _

variable (r) in
/-- The natural left unit isomorphism `1 × B ≅ B`, with `B` pulled back along
`leftUnitProjection` and lifted to the output carrier universe. -/
def leftMixedProductUnitIso :
    letI := T.topology
    Prod.sectR T.mixedProductUnit.{uF, uV} (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⋙
        T.leftMixedProductFunctor 0 r ≅
      MixedProductTensor.pullbackFunctor (leftUnitProjection r) continuous_leftUnitProjection ⋙
        MixedProductTensor.liftFunctor.{uF, uV, uF} :=
  letI := T.topology
  NatIso.ofComponents (fun B => SmoothRep.mkIso (T.leftMixedProductUnitEquiv r B))
    fun φ => MixedProductTensor.smoothRep_hom_ext fun f =>
      T.leftMixedProductUnitEquiv_naturality φ f

variable (r) in
/-- The natural right unit isomorphism `B × 1 ≅ B`, with `B` pulled back along
`rightUnitProjection` and lifted to the output carrier universe. -/
def rightMixedProductUnitIso :
    letI := T.topology
    Prod.sectL (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) T.mixedProductUnit.{uF, uV} ⋙
        T.rightMixedProductFunctor 0 r ≅
      MixedProductTensor.pullbackFunctor (rightUnitProjection r) continuous_rightUnitProjection ⋙
        MixedProductTensor.liftFunctor.{uF, uV, uF} :=
  letI := T.topology
  NatIso.ofComponents (fun B => SmoothRep.mkIso (T.rightMixedProductUnitEquiv r B))
    fun φ => MixedProductTensor.smoothRep_hom_ext fun f =>
      T.rightMixedProductUnitEquiv_naturality φ f

end PadicField.TopologicalData

end Langlands
