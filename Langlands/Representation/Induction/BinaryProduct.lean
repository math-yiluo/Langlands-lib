import Langlands.Representation.Tensor.OneFactor
import Langlands.Group.GL.MirabolicOppositeIntersection
import Langlands.Group.GL.RankReindex
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Products.Basic

/-!
# The binary normalized product in all ranks

For smooth complex representations `A` of `GL_a(F)` and `B` of `GL_b(F)`, the
bifunctor `T.binaryNormalizedProductFunctor a b` gives a smooth representation
`A × B` of `GL_{a+b}(F)` for all `a b : ℕ`. For positive ranks it is the
published upper-block normalized product on the published binary shape. If a
rank is zero, the corresponding carrier is kept as a tensor factor on which the
group acts trivially.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct NNReal

namespace Langlands

universe uR uK uG uF uV uW uX uY uZ uU

namespace GeneralLinear

/-- A general linear group of rank zero is trivial. -/
theorem subsingleton_of_rank_eq_zero {R : Type uR} [CommRing R] {n : ℕ} (hn : n = 0) :
    Subsingleton (GeneralLinear n R) := by
  subst hn
  exact ⟨fun g h => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩

/-- Every representation of a general linear group of rank zero is trivial. -/
theorem representation_apply_of_rank_eq_zero {R : Type uR} [CommRing R] {n : ℕ} (hn : n = 0)
    {k : Type uK} [CommSemiring k] {V : Type uV} [AddCommMonoid V] [Module k V]
    (ρ : Representation k (GeneralLinear n R) V) (g : GeneralLinear n R) : ρ g = 1 := by
  have := subsingleton_of_rank_eq_zero (R := R) hn
  rw [Subsingleton.elim g 1, map_one]

end GeneralLinear

namespace FiniteTensor

variable {R : Type uR} [CommRing R] {ι : Type uK} {H : ι → Type uG} [∀ i, Group (H i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

/-- The external tensor product of a family of intertwiners with one zero
member is zero. -/
theorem externalMap_eq_zero_of_eq_zero {ρ : ∀ i, Representation R (H i) (V i)}
    {σ : ∀ i, Representation R (H i) (W i)} (f : ∀ i, (ρ i).IntertwiningMap (σ i))
    (i₀ : ι) (h : f i₀ = 0) : externalMap f = 0 := by
  apply Representation.IntertwiningMap.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply]
  refine (externalMap_tprod f v).trans ?_
  exact (PiTensorProduct.tprod R).map_coord_zero i₀ (by simp [h])

end FiniteTensor

namespace BinaryTensor

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
variable {V'' : Type uZ} [AddCommGroup V''] [Module ℂ V'']
variable {W : Type uX} [AddCommGroup W] [Module ℂ W]
variable {W' : Type uY} [AddCommGroup W'] [Module ℂ W']
variable {W'' : Type uU} [AddCommGroup W''] [Module ℂ W'']

/-! ### Pullback along a group homomorphism and carrier lifts -/

/-- Pull back an intertwiner along a group homomorphism. -/
def compMap {H : Type uR} [Group H] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (φ : H →* G) :
    Representation.IntertwiningMap (ρ.comp φ) (ρ'.comp φ) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (φ h)

@[simp]
theorem compMap_apply {H : Type uR} [Group H] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ') (φ : H →* G) (v : V) :
    compMap f φ v = f v := rfl

/-- Pull back an equivalence along a group homomorphism. -/
def compEquiv {H : Type uR} [Group H] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (φ : H →* G) :
    Representation.Equiv (ρ.comp φ) (ρ'.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => e.isIntertwining' (φ h)

@[simp]
theorem compEquiv_apply {H : Type uR} [Group H] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (φ : H →* G) (v : V) :
    compEquiv e φ v = e v := rfl

/-- The literal carrier lift, conjugating the action by `ULift.up`. -/
def lift (ρ : Representation ℂ G V) : Representation ℂ G (ULift.{uY} V) :=
  (ULift.moduleEquiv (R := ℂ) (M := V)).symm.conjRingEquiv.toMonoidHom.comp ρ

@[simp]
theorem lift_apply (ρ : Representation ℂ G V) (g : G) (v : ULift.{uY} V) :
    lift ρ g v = ULift.up (ρ g v.down) := rfl

/-- The cross-universe equivalence between an action and its lift: forward
`ULift.up`, inverse `ULift.down`. -/
def liftEquiv (ρ : Representation ℂ G V) : ρ.Equiv (lift.{uG, uV, uY} ρ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun _ =>
    LinearMap.ext fun _ => rfl

@[simp]
theorem liftEquiv_apply (ρ : Representation ℂ G V) (v : V) :
    liftEquiv.{uG, uV, uY} ρ v = ULift.up v := rfl

@[simp]
theorem liftEquiv_symm_apply (ρ : Representation ℂ G V) (v : ULift.{uY} V) :
    (liftEquiv ρ).symm v = v.down := rfl

/-- The lift of an intertwiner: `up ∘ f ∘ down`. -/
def liftMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') :
    (lift.{uG, uV, uY} ρ).IntertwiningMap (lift.{uG, uW, uY} ρ') where
  toLinearMap := (ULift.moduleEquiv (R := ℂ) (M := V')).symm.toLinearMap ∘ₗ
    f.toLinearMap ∘ₗ (ULift.moduleEquiv (R := ℂ) (M := V)).toLinearMap
  isIntertwining' g := LinearMap.ext fun v =>
    congrArg ULift.up (LinearMap.congr_fun (f.isIntertwining' g) v.down)

@[simp]
theorem liftMap_apply {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (v : ULift.{uY} V) :
    liftMap.{uG, uV, uW, uY} f v = ULift.up (f v.down) := rfl

/-! ### The tensor unit -/

/-- `ULift ℂ ⊗ W ≃ W`, `c ⊗ w ↦ c.down • w`, for the second-factor action. -/
def secondFactorUnitEquiv (σ : Representation ℂ G W) :
    (secondFactor (ULift.{uV} ℂ) σ).Equiv σ :=
  Representation.Equiv.mk
    ((TensorProduct.congr (ULift.moduleEquiv (R := ℂ) (M := ℂ)) (LinearEquiv.refl ℂ W)).trans
      (TensorProduct.lid ℂ W))
    fun g => TensorProduct.ext' fun c w => by
      simp

@[simp]
theorem secondFactorUnitEquiv_tmul (σ : Representation ℂ G W) (c : ULift.{uV} ℂ) (w : W) :
    secondFactorUnitEquiv σ (c ⊗ₜ w) = c.down • w := by
  simp [secondFactorUnitEquiv]

theorem secondFactorUnitEquiv_naturality {σ : Representation ℂ G W}
    {σ' : Representation ℂ G W'} (g : σ.IntertwiningMap σ') (x : ULift.{uV} ℂ ⊗[ℂ] W) :
    secondFactorUnitEquiv σ' (TensorProduct.map LinearMap.id g.toLinearMap x) =
      g (secondFactorUnitEquiv σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `V ⊗ ULift ℂ ≃ V`, `v ⊗ c ↦ c.down • v`, for the first-factor action. -/
def firstFactorUnitEquiv (ρ : Representation ℂ G V) :
    (firstFactor ρ (ULift.{uX} ℂ)).Equiv ρ :=
  Representation.Equiv.mk
    ((TensorProduct.congr (LinearEquiv.refl ℂ V) (ULift.moduleEquiv (R := ℂ) (M := ℂ))).trans
      (TensorProduct.rid ℂ V))
    fun g => TensorProduct.ext' fun v c => by
      simp

@[simp]
theorem firstFactorUnitEquiv_tmul (ρ : Representation ℂ G V) (v : V) (c : ULift.{uX} ℂ) :
    firstFactorUnitEquiv ρ (v ⊗ₜ c) = c.down • v := by
  simp [firstFactorUnitEquiv]

theorem firstFactorUnitEquiv_naturality {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ') (x : V ⊗[ℂ] ULift.{uX} ℂ) :
    firstFactorUnitEquiv ρ' (TensorProduct.map f.toLinearMap LinearMap.id x) =
      f (firstFactorUnitEquiv ρ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The rank-zero tensor models -/

section Models

variable {R : Type uR} [CommRing R] {a b : ℕ}

/-- The `a = 0` tensor model: `GL_{a+b}` acts on `V ⊗ W` through the rank cast
to `GL_b` and the second factor. -/
def rankZeroLeft (ha : a = 0) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear b R) W) :
    Representation ℂ (GeneralLinear (a + b) R) (V ⊗[ℂ] W) :=
  (secondFactor V σ).comp
    (GeneralLinear.reindex (R := R) (finCongr (by omega : a + b = b))).toMonoidHom

@[simp]
theorem rankZeroLeft_tmul (ha : a = 0) (σ : Representation ℂ (GeneralLinear b R) W)
    (g : GeneralLinear (a + b) R) (v : V) (w : W) :
    rankZeroLeft ha V σ g (v ⊗ₜ w) =
      v ⊗ₜ σ (GeneralLinear.reindex (R := R) (finCongr (by omega : a + b = b)) g) w := rfl

/-- The `b = 0` tensor model: `GL_{a+b}` acts on `V ⊗ W` through the rank cast
to `GL_a` and the first factor. -/
def rankZeroRight (hb : b = 0) (ρ : Representation ℂ (GeneralLinear a R) V)
    (W : Type uX) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (GeneralLinear (a + b) R) (V ⊗[ℂ] W) :=
  (firstFactor ρ W).comp
    (GeneralLinear.reindex (R := R) (finCongr (by omega : a + b = a))).toMonoidHom

@[simp]
theorem rankZeroRight_tmul (hb : b = 0) (ρ : Representation ℂ (GeneralLinear a R) V)
    (g : GeneralLinear (a + b) R) (v : V) (w : W) :
    rankZeroRight hb ρ W g (v ⊗ₜ w) =
      ρ (GeneralLinear.reindex (R := R) (finCongr (by omega : a + b = a)) g) v ⊗ₜ w := rfl

/-- The map of lifted `a = 0` models induced by `f ⊗ g`. -/
def rankZeroLeftMap (ha : a = 0) {σ : Representation ℂ (GeneralLinear b R) W}
    {σ' : Representation ℂ (GeneralLinear b R) W'} (f : V →ₗ[ℂ] V')
    (g : σ.IntertwiningMap σ') :
    (lift.{uR, max uV uX, uR} (rankZeroLeft ha V σ)).IntertwiningMap
      (lift.{uR, max uW uY, uR} (rankZeroLeft ha V' σ')) :=
  liftMap (compMap (secondFactorMap f g) _)

@[simp]
theorem rankZeroLeftMap_apply (ha : a = 0) {σ : Representation ℂ (GeneralLinear b R) W}
    {σ' : Representation ℂ (GeneralLinear b R) W'} (f : V →ₗ[ℂ] V')
    (g : σ.IntertwiningMap σ') (x : ULift.{uR} (V ⊗[ℂ] W)) :
    rankZeroLeftMap ha f g x = ULift.up (TensorProduct.map f g.toLinearMap x.down) := rfl

theorem rankZeroLeftMap_id (ha : a = 0) (σ : Representation ℂ (GeneralLinear b R) W) :
    rankZeroLeftMap ha (LinearMap.id : V →ₗ[ℂ] V) (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (lift.{uR, max uV uX, uR} (rankZeroLeft ha V σ)) := by
  rw [rankZeroLeftMap, secondFactorMap_id]
  rfl

theorem rankZeroLeftMap_comp (ha : a = 0) {σ : Representation ℂ (GeneralLinear b R) W}
    {σ' : Representation ℂ (GeneralLinear b R) W'}
    {σ'' : Representation ℂ (GeneralLinear b R) W''} (f : V →ₗ[ℂ] V') (f' : V' →ₗ[ℂ] V'')
    (g : σ.IntertwiningMap σ') (g' : σ'.IntertwiningMap σ'') :
    rankZeroLeftMap ha (f' ∘ₗ f) (g'.comp g) =
      (rankZeroLeftMap ha f' g').comp (rankZeroLeftMap ha f g) := by
  rw [rankZeroLeftMap, secondFactorMap_comp]
  rfl

theorem rankZeroLeftMap_zero_left (ha : a = 0) {σ : Representation ℂ (GeneralLinear b R) W}
    {σ' : Representation ℂ (GeneralLinear b R) W'} (g : σ.IntertwiningMap σ') :
    rankZeroLeftMap ha (0 : V →ₗ[ℂ] V') g = 0 := by
  rw [rankZeroLeftMap, secondFactorMap_zero_left]
  rfl

theorem rankZeroLeftMap_zero_right (ha : a = 0) {σ : Representation ℂ (GeneralLinear b R) W}
    {σ' : Representation ℂ (GeneralLinear b R) W'} (f : V →ₗ[ℂ] V') :
    rankZeroLeftMap ha f (0 : σ.IntertwiningMap σ') = 0 := by
  rw [rankZeroLeftMap, secondFactorMap_zero_right]
  rfl

/-- The map of lifted `b = 0` models induced by `f ⊗ g`. -/
def rankZeroRightMap (hb : b = 0) {ρ : Representation ℂ (GeneralLinear a R) V}
    {ρ' : Representation ℂ (GeneralLinear a R) V'} (f : ρ.IntertwiningMap ρ')
    (g : W →ₗ[ℂ] W') :
    (lift.{uR, max uV uX, uR} (rankZeroRight hb ρ W)).IntertwiningMap
      (lift.{uR, max uW uY, uR} (rankZeroRight hb ρ' W')) :=
  liftMap (compMap (firstFactorMap f g) _)

@[simp]
theorem rankZeroRightMap_apply (hb : b = 0) {ρ : Representation ℂ (GeneralLinear a R) V}
    {ρ' : Representation ℂ (GeneralLinear a R) V'} (f : ρ.IntertwiningMap ρ')
    (g : W →ₗ[ℂ] W') (x : ULift.{uR} (V ⊗[ℂ] W)) :
    rankZeroRightMap hb f g x = ULift.up (TensorProduct.map f.toLinearMap g x.down) := rfl

theorem rankZeroRightMap_id (hb : b = 0) (ρ : Representation ℂ (GeneralLinear a R) V) :
    rankZeroRightMap hb (Representation.IntertwiningMap.id ρ) (LinearMap.id : W →ₗ[ℂ] W) =
      Representation.IntertwiningMap.id (lift.{uR, max uV uX, uR} (rankZeroRight hb ρ W)) := by
  rw [rankZeroRightMap, firstFactorMap_id]
  rfl

theorem rankZeroRightMap_comp (hb : b = 0) {ρ : Representation ℂ (GeneralLinear a R) V}
    {ρ' : Representation ℂ (GeneralLinear a R) V'}
    {ρ'' : Representation ℂ (GeneralLinear a R) V''} (f : ρ.IntertwiningMap ρ')
    (f' : ρ'.IntertwiningMap ρ'') (g : W →ₗ[ℂ] W') (g' : W' →ₗ[ℂ] W'') :
    rankZeroRightMap hb (f'.comp f) (g' ∘ₗ g) =
      (rankZeroRightMap hb f' g').comp (rankZeroRightMap hb f g) := by
  rw [rankZeroRightMap, firstFactorMap_comp]
  rfl

theorem rankZeroRightMap_zero_left (hb : b = 0) {ρ : Representation ℂ (GeneralLinear a R) V}
    {ρ' : Representation ℂ (GeneralLinear a R) V'} (g : W →ₗ[ℂ] W') :
    rankZeroRightMap hb (0 : ρ.IntertwiningMap ρ') g = 0 := by
  rw [rankZeroRightMap, firstFactorMap_zero_left]
  rfl

theorem rankZeroRightMap_zero_right (hb : b = 0) {ρ : Representation ℂ (GeneralLinear a R) V}
    {ρ' : Representation ℂ (GeneralLinear a R) V'} (f : ρ.IntertwiningMap ρ') :
    rankZeroRightMap hb f (0 : W →ₗ[ℂ] W') = 0 := by
  rw [rankZeroRightMap, firstFactorMap_zero_right]
  rfl

end Models

section Smooth

variable [TopologicalSpace G]

theorem isSmooth_lift {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    IsSmooth (lift.{uG, uV, uY} ρ) :=
  isSmooth_of_surjective (liftEquiv ρ).toIntertwiningMap (liftEquiv ρ).surjective hρ

theorem isSmooth_trivial : IsSmooth (Representation.trivial ℂ G V) :=
  fun _ => ⟨⊤, fun _ => rfl⟩

end Smooth

end BinaryTensor

namespace PadicField.TopologicalData

open GeneralLinear BinaryTensor

section SmoothHom

variable {G : Type uG} [Group G] [TopologicalSpace G]

private theorem smoothRep_hom_zero {A B : SmoothRep.{0, uG, uV} ℂ G} :
    SmoothRep.hom (0 : A ⟶ B) = 0 := rfl

private theorem smoothRep_eq_zero {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (h : SmoothRep.hom f = 0) : f = 0 :=
  calc f = SmoothRep.ofHom (SmoothRep.hom f) := rfl
    _ = SmoothRep.ofHom 0 := by rw [h]
    _ = 0 := rfl

end SmoothHom

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### Positive ranks: the published normalized product on the binary shape -/

/-- Normalized product induction of a family of intertwiners whose external
tensor product vanishes is zero. -/
theorem normalizedProductInducedMap_eq_zero {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) (h : FiniteTensor.externalMap f = 0) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedProductInducedMap B f = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  unfold normalizedProductInducedMap
  rw [h]
  ext φ x
  rfl

section Positive

variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The ordered pair `(A, B)` as the dependent factor family of the published
binary shape: block `0` is `A` and block `1` is `B`. -/
def binaryPairFamilyFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      (∀ i, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((BlockShape.binary a b ha hb).size i) F.Carrier)) :=
  letI := T.topology
  Functor.pi' (Fin.cases
    (motive := fun i : Fin 2 =>
      (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
        SmoothRep.{0, uF, uV} ℂ
          (GeneralLinear ((BlockShape.binary a b ha hb).size i) F.Carrier))
    (CategoryTheory.Prod.fst _ _) (fun _ => CategoryTheory.Prod.snd _ _))

theorem binaryPairFamilyFunctor_obj_zero
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    (T.binaryPairFamilyFunctor ha hb).obj X (0 : Fin 2) = X.1 := rfl

theorem binaryPairFamilyFunctor_obj_one
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    (T.binaryPairFamilyFunctor ha hb).obj X (1 : Fin 2) = X.2 := rfl

theorem binaryPairFamilyFunctor_map_zero
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    (T.binaryPairFamilyFunctor ha hb).map f (0 : Fin 2) = f.1 := rfl

theorem binaryPairFamilyFunctor_map_one
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    (T.binaryPairFamilyFunctor ha hb).map f (1 : Fin 2) = f.2 := rfl

/-- The published positive-block product on the binary shape `(a, b)`. -/
def binaryPositiveProductFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  T.binaryPairFamilyFunctor ha hb ⋙
    T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)

/-- The action is the normalized induction of the block tensor of `(A, B)`. -/
theorem binaryPositiveProductFunctor_obj
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryPositiveProductFunctor ha hb).obj X).representation =
      T.normalizedProductInduced (BlockShape.binary a b ha hb)
        (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation) := rfl

/-- Maps are induced by the external tensor product of the two input maps. -/
theorem binaryPositiveProductFunctor_map
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    SmoothRep.hom ((T.binaryPositiveProductFunctor ha hb).map f) =
      T.normalizedProductInducedMap (BlockShape.binary a b ha hb)
        (fun i => SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i)) := rfl

/-- The action is right translation: `(g · f)(x) = f(x g)`. -/
theorem binaryPositiveProductFunctor_apply
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (g x : GeneralLinear (a + b) F.Carrier)
    (f : letI := T.topology; (T.binaryPositiveProductFunctor ha hb).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (BlockShape.binary a b ha hb))
          (((BlockShape.binary a b ha hb).blockTensor
            (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)).comp
            ((BlockShape.binary a b ha hb).leviProjection F.Carrier)))
        (((T.binaryPositiveProductFunctor ha hb).obj X).representation g f) x =
      Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (BlockShape.binary a b ha hb))
          (((BlockShape.binary a b ha hb).blockTensor
            (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)).comp
            ((BlockShape.binary a b ha hb).leviProjection F.Carrier)))
        f (x * g) := rfl

/-- The covariance `f (p x) = δ_P(m)^(1/2) (A(m₀) ⊗ B(m₁)) (f x)`, with
`m = (m₀, m₁)` the Levi part of `p` in the upper block parabolic of the binary
shape. -/
theorem binaryPositiveProductFunctor_covariant
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (f : letI := T.topology; (T.binaryPositiveProductFunctor ha hb).obj X)
    (g : (BlockShape.binary a b ha hb).parabolic F.Carrier)
    (x : GeneralLinear (a + b) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (twist (T.parabolicHalfModulus (BlockShape.binary a b ha hb))
          (((BlockShape.binary a b ha hb).blockTensor
            (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)).comp
            ((BlockShape.binary a b ha hb).leviProjection F.Carrier)))
        f ((g : GeneralLinear (a + b) F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus (BlockShape.binary a b ha hb)
          ((BlockShape.binary a b ha hb).leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        (BlockShape.binary a b ha hb).blockTensor
          (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)
          ((BlockShape.binary a b ha hb).leviProjection F.Carrier g)
          (Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier)
            (twist (T.parabolicHalfModulus (BlockShape.binary a b ha hb))
              (((BlockShape.binary a b ha hb).blockTensor
                (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)).comp
                ((BlockShape.binary a b ha hb).leviProjection F.Carrier))) f x) :=
  T.normalizedProductInduced_covariant (BlockShape.binary a b ha hb) _ f g x

end Positive

/-! ### Rank-zero tensor models -/

section Zero

variable {a b : ℕ}

/-- The object of the `a = 0` model: the lift of `A ⊗ B`, on which `GL_{a+b}`
acts through the rank cast to `GL_b` and the second factor. -/
def binaryLeftZeroTensorObj (ha : a = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  SmoothRep.of (lift.{uF, uV, uF} (rankZeroLeft (R := F.Carrier) ha X.1 X.2.representation))
    (isSmooth_lift (isSmooth_comp _ (continuous_reindex_finCongr _)
      (isSmooth_secondFactor X.2.isSmooth)))

/-- The `a = 0` model as a bifunctor; maps are the lifts of `f ⊗ g`. -/
def binaryLeftZeroTensorFunctor (ha : a = 0) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  { obj X := T.binaryLeftZeroTensorObj ha X
    map f := SmoothRep.ofHom
      (rankZeroLeftMap ha (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2))
    map_id X := by
      change SmoothRep.ofHom (A := T.binaryLeftZeroTensorObj ha X)
          (B := T.binaryLeftZeroTensorObj ha X)
          (rankZeroLeftMap ha LinearMap.id
            (Representation.IntertwiningMap.id X.2.representation)) =
        SmoothRep.ofHom (Representation.IntertwiningMap.id _)
      rw [rankZeroLeftMap_id]
      rfl
    map_comp {X Y Z} f g := by
      change SmoothRep.ofHom (A := T.binaryLeftZeroTensorObj ha X)
          (B := T.binaryLeftZeroTensorObj ha Z)
          (rankZeroLeftMap ha ((SmoothRep.hom g.1).toLinearMap ∘ₗ (SmoothRep.hom f.1).toLinearMap)
            ((SmoothRep.hom g.2).comp (SmoothRep.hom f.2))) =
        SmoothRep.ofHom
          ((rankZeroLeftMap ha (SmoothRep.hom g.1).toLinearMap (SmoothRep.hom g.2)).comp
            (rankZeroLeftMap ha (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2)))
      rw [rankZeroLeftMap_comp] }

theorem binaryLeftZeroTensorFunctor_obj (ha : a = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryLeftZeroTensorFunctor ha).obj X).representation =
      lift.{uF, uV, uF} (rankZeroLeft (R := F.Carrier) ha X.1 X.2.representation) := rfl

theorem binaryLeftZeroTensorFunctor_map (ha : a = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    SmoothRep.hom ((T.binaryLeftZeroTensorFunctor ha).map f) =
      rankZeroLeftMap ha (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2) := rfl

theorem binaryLeftZeroTensorFunctor_map_apply (ha : a = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (v : letI := T.topology; (T.binaryLeftZeroTensorFunctor ha).obj X) :
    letI := T.topology
    SmoothRep.hom ((T.binaryLeftZeroTensorFunctor ha).map f) v =
      ULift.up (TensorProduct.map (SmoothRep.hom f.1).toLinearMap
        (SmoothRep.hom f.2).toLinearMap (ULift.down v)) := rfl

/-- The object of the `b = 0` model: the lift of `A ⊗ B`, on which `GL_{a+b}`
acts through the rank cast to `GL_a` and the first factor. -/
def binaryRightZeroTensorObj (hb : b = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  SmoothRep.of (lift.{uF, uV, uF} (rankZeroRight (R := F.Carrier) hb X.1.representation X.2))
    (isSmooth_lift (isSmooth_comp _ (continuous_reindex_finCongr _)
      (isSmooth_firstFactor X.1.isSmooth)))

/-- The `b = 0` model as a bifunctor; maps are the lifts of `f ⊗ g`. -/
def binaryRightZeroTensorFunctor (hb : b = 0) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  { obj X := T.binaryRightZeroTensorObj hb X
    map f := SmoothRep.ofHom
      (rankZeroRightMap hb (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap)
    map_id X := by
      change SmoothRep.ofHom (A := T.binaryRightZeroTensorObj hb X)
          (B := T.binaryRightZeroTensorObj hb X)
          (rankZeroRightMap hb (Representation.IntertwiningMap.id X.1.representation)
            LinearMap.id) =
        SmoothRep.ofHom (Representation.IntertwiningMap.id _)
      rw [rankZeroRightMap_id]
      rfl
    map_comp {X Y Z} f g := by
      change SmoothRep.ofHom (A := T.binaryRightZeroTensorObj hb X)
          (B := T.binaryRightZeroTensorObj hb Z)
          (rankZeroRightMap hb ((SmoothRep.hom g.1).comp (SmoothRep.hom f.1))
            ((SmoothRep.hom g.2).toLinearMap ∘ₗ (SmoothRep.hom f.2).toLinearMap)) =
        SmoothRep.ofHom
          ((rankZeroRightMap hb (SmoothRep.hom g.1) (SmoothRep.hom g.2).toLinearMap).comp
            (rankZeroRightMap hb (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap))
      rw [rankZeroRightMap_comp] }

theorem binaryRightZeroTensorFunctor_obj (hb : b = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryRightZeroTensorFunctor hb).obj X).representation =
      lift.{uF, uV, uF} (rankZeroRight (R := F.Carrier) hb X.1.representation X.2) := rfl

theorem binaryRightZeroTensorFunctor_map (hb : b = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    SmoothRep.hom ((T.binaryRightZeroTensorFunctor hb).map f) =
      rankZeroRightMap hb (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap := rfl

theorem binaryRightZeroTensorFunctor_map_apply (hb : b = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (v : letI := T.topology; (T.binaryRightZeroTensorFunctor hb).obj X) :
    letI := T.topology
    SmoothRep.hom ((T.binaryRightZeroTensorFunctor hb).map f) v =
      ULift.up (TensorProduct.map (SmoothRep.hom f.1).toLinearMap
        (SmoothRep.hom f.2).toLinearMap (ULift.down v)) := rfl

end Zero

/-! ### The binary product in all ranks -/

/-- The binary normalized product `A × B` of smooth representations of `GL_a(F)`
and `GL_b(F)`, for all ranks. For positive ranks it is the published normalized
product on the binary shape; if `a = 0` (respectively `b = 0`) it is the lifted
tensor product on which `GL_{a+b}(F)` acts through the second (respectively
first) factor. -/
def binaryNormalizedProductFunctor (a b : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  if ha : a = 0 then T.binaryLeftZeroTensorFunctor ha
  else if hb : b = 0 then T.binaryRightZeroTensorFunctor hb
  else T.binaryPositiveProductFunctor (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)

theorem binaryNormalizedProductFunctor_zero_left (b : ℕ) :
    T.binaryNormalizedProductFunctor.{uF, uV} 0 b = T.binaryLeftZeroTensorFunctor rfl := rfl

theorem binaryNormalizedProductFunctor_succ_zero (a : ℕ) :
    T.binaryNormalizedProductFunctor.{uF, uV} (a + 1) 0 = T.binaryRightZeroTensorFunctor rfl :=
  rfl

theorem binaryNormalizedProductFunctor_succ_succ (a b : ℕ) :
    T.binaryNormalizedProductFunctor.{uF, uV} (a + 1) (b + 1) =
      T.binaryPositiveProductFunctor (Nat.succ_pos a) (Nat.succ_pos b) := rfl

variable {a b : ℕ}

theorem binaryNormalizedProductFunctor_of_left_eq_zero (ha : a = 0) :
    T.binaryNormalizedProductFunctor.{uF, uV} a b = T.binaryLeftZeroTensorFunctor ha :=
  dite_eq_left ha

theorem binaryNormalizedProductFunctor_of_right_eq_zero (ha : a ≠ 0) (hb : b = 0) :
    T.binaryNormalizedProductFunctor.{uF, uV} a b = T.binaryRightZeroTensorFunctor hb := by
  rw [binaryNormalizedProductFunctor, dite_eq_right ha, dite_eq_left hb]

theorem binaryNormalizedProductFunctor_of_pos (ha : 0 < a) (hb : 0 < b) :
    T.binaryNormalizedProductFunctor.{uF, uV} a b = T.binaryPositiveProductFunctor ha hb := by
  rw [binaryNormalizedProductFunctor, dite_eq_right ha.ne', dite_eq_right hb.ne']

/-- The identification with the first-factor tensor model when `a = 0`. -/
def binaryNormalizedProductLeftZeroIso (ha : a = 0) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} a b ≅ T.binaryLeftZeroTensorFunctor ha :=
  letI := T.topology
  eqToIso (T.binaryNormalizedProductFunctor_of_left_eq_zero ha)

/-- The identification with the second-factor tensor model when `a ≠ 0` and
`b = 0`. -/
def binaryNormalizedProductRightZeroIso (ha : a ≠ 0) (hb : b = 0) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} a b ≅ T.binaryRightZeroTensorFunctor hb :=
  letI := T.topology
  eqToIso (T.binaryNormalizedProductFunctor_of_right_eq_zero ha hb)

/-- The identification with the published positive-block product. -/
def binaryNormalizedProductPositiveIso (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} a b ≅ T.binaryPositiveProductFunctor ha hb :=
  letI := T.topology
  eqToIso (T.binaryNormalizedProductFunctor_of_pos ha hb)

/-! ### Explicit tensor-model equivalences -/

/-- For `a = 0`, the product of `(A, B)` is `A ⊗ B` with `GL_{a+b}` acting
through the rank cast and `B`. The forward map is the component of
`binaryNormalizedProductLeftZeroIso` followed by `ULift.down`. -/
def binaryLeftZeroTensorEquiv (ha : a = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a b).obj X).representation.Equiv
      (rankZeroLeft (R := F.Carrier) ha X.1 X.2.representation) :=
  letI := T.topology
  (SmoothRep.equivOfIso ((T.binaryNormalizedProductLeftZeroIso ha).app X)).trans
    (liftEquiv _).symm

theorem binaryLeftZeroTensorEquiv_naturality (ha : a = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (v : letI := T.topology; (T.binaryNormalizedProductFunctor a b).obj X) :
    letI := T.topology
    T.binaryLeftZeroTensorEquiv ha Y
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor a b).map f) v) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (T.binaryLeftZeroTensorEquiv ha X v) := by
  let := T.topology
  exact congrArg ULift.down (congrArg (fun φ => SmoothRep.hom φ v)
    ((T.binaryNormalizedProductLeftZeroIso ha).hom.naturality f))

/-- If both ranks are zero, the product of `(A, B)` is `A ⊗ B` with the trivial
action of `GL_{a+b} = GL_0`. -/
def binaryZeroZeroTensorEquiv (ha : a = 0) (hb : b = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a b).obj X).representation.Equiv
      (Representation.trivial ℂ (GeneralLinear (a + b) F.Carrier) (X.1 ⊗[ℂ] X.2)) :=
  letI := T.topology
  (T.binaryLeftZeroTensorEquiv ha X).trans
    (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
      rw [representation_apply_of_rank_eq_zero (by omega : a + b = 0)
        (rankZeroLeft (R := F.Carrier) ha X.1 X.2.representation) g]
      rfl)

theorem binaryZeroZeroTensorEquiv_naturality (ha : a = 0) (hb : b = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (v : letI := T.topology; (T.binaryNormalizedProductFunctor a b).obj X) :
    letI := T.topology
    T.binaryZeroZeroTensorEquiv ha hb Y
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor a b).map f) v) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (T.binaryZeroZeroTensorEquiv ha hb X v) :=
  T.binaryLeftZeroTensorEquiv_naturality ha f v

/-- For `b = 0`, the product of `(A, B)` is `A ⊗ B` with `GL_{a+b}` acting
through the rank cast and `A`. If `a ≠ 0`, the forward map is the component of
`binaryNormalizedProductRightZeroIso` followed by `ULift.down`. If also `a = 0`,
it is `binaryZeroZeroTensorEquiv` followed by the identity of `A ⊗ B`, since all
actions of `GL_{a+b} = GL_0` are trivial. -/
def binaryRightZeroTensorEquiv (hb : b = 0)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a b).obj X).representation.Equiv
      (rankZeroRight (R := F.Carrier) hb X.1.representation X.2) :=
  letI := T.topology
  if ha : a = 0 then
    (T.binaryZeroZeroTensorEquiv ha hb X).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
        rw [representation_apply_of_rank_eq_zero (by omega : a + b = 0)
            (Representation.trivial ℂ (GeneralLinear (a + b) F.Carrier) (X.1 ⊗[ℂ] X.2)) g,
          representation_apply_of_rank_eq_zero (by omega : a + b = 0)
            (rankZeroRight (R := F.Carrier) hb X.1.representation X.2) g]
        rfl)
  else
    (SmoothRep.equivOfIso ((T.binaryNormalizedProductRightZeroIso ha hb).app X)).trans
      (liftEquiv _).symm

theorem binaryRightZeroTensorEquiv_naturality (hb : b = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (v : letI := T.topology; (T.binaryNormalizedProductFunctor a b).obj X) :
    letI := T.topology
    T.binaryRightZeroTensorEquiv hb Y
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor a b).map f) v) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (T.binaryRightZeroTensorEquiv hb X v) := by
  let := T.topology
  by_cases ha : a = 0
  · rw [binaryRightZeroTensorEquiv, dite_eq_left ha, binaryRightZeroTensorEquiv, dite_eq_left ha]
    exact T.binaryZeroZeroTensorEquiv_naturality ha hb f v
  · rw [binaryRightZeroTensorEquiv, dite_eq_right ha, binaryRightZeroTensorEquiv, dite_eq_right ha]
    exact congrArg ULift.down (congrArg (fun φ => SmoothRep.hom φ v)
      ((T.binaryNormalizedProductRightZeroIso ha hb).hom.naturality f))

/-! ### The unit -/

/-- The genuine one-dimensional unit: `ULift ℂ` with the trivial action of
`GL_0(F)`. -/
def binaryProductUnit :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  SmoothRep.of (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ))
    isSmooth_trivial

theorem binaryProductUnit_representation :
    letI := T.topology
    (T.binaryProductUnit.{uF, uV}).representation =
      Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ) := rfl

theorem finrank_binaryProductUnit :
    letI := T.topology
    Module.finrank ℂ (T.binaryProductUnit.{uF, uV}) = 1 :=
  (ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq.trans (Module.finrank_self ℂ)

/-- The left unit equivalence `1 × B ≃ B`, with the rank cast `GL_{0+b} = GL_b`
and the lift of `B` to the output universe. -/
def binaryProductLeftUnitEquiv
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor 0 b).obj (T.binaryProductUnit, B)).representation.Equiv
      (lift.{uF, uV, uF} (B.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.zero_add b))).toMonoidHom)) :=
  letI := T.topology
  (T.binaryLeftZeroTensorEquiv rfl (T.binaryProductUnit, B)).trans
    ((compEquiv (secondFactorUnitEquiv B.representation) _).trans (liftEquiv _))

theorem binaryProductLeftUnitEquiv_naturality
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; B ⟶ B')
    (v : letI := T.topology
      (T.binaryNormalizedProductFunctor 0 b).obj (T.binaryProductUnit, B)) :
    letI := T.topology
    T.binaryProductLeftUnitEquiv B'
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor 0 b).map
          (CategoryTheory.Prod.mkHom (𝟙 T.binaryProductUnit) f)) v) =
      ULift.up (SmoothRep.hom f (T.binaryProductLeftUnitEquiv B v).down) := by
  let := T.topology
  change ULift.up (secondFactorUnitEquiv B'.representation
      (T.binaryLeftZeroTensorEquiv rfl (T.binaryProductUnit, B')
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor 0 b).map
          (CategoryTheory.Prod.mkHom (𝟙 T.binaryProductUnit) f)) v))) = _
  rw [T.binaryLeftZeroTensorEquiv_naturality rfl]
  exact congrArg ULift.up (secondFactorUnitEquiv_naturality (SmoothRep.hom f) _)

/-- The right unit equivalence `A × 1 ≃ A`, with the rank cast `GL_{a+0} = GL_a`
and the lift of `A` to the output universe. -/
def binaryProductRightUnitEquiv
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a 0).obj (A, T.binaryProductUnit)).representation.Equiv
      (lift.{uF, uV, uF} (A.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_zero a))).toMonoidHom)) :=
  letI := T.topology
  (T.binaryRightZeroTensorEquiv rfl (A, T.binaryProductUnit)).trans
    ((compEquiv (firstFactorUnitEquiv A.representation) _).trans (liftEquiv _))

theorem binaryProductRightUnitEquiv_naturality
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; A ⟶ A')
    (v : letI := T.topology
      (T.binaryNormalizedProductFunctor a 0).obj (A, T.binaryProductUnit)) :
    letI := T.topology
    T.binaryProductRightUnitEquiv A'
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor a 0).map
          (CategoryTheory.Prod.mkHom f (𝟙 T.binaryProductUnit))) v) =
      ULift.up (SmoothRep.hom f (T.binaryProductRightUnitEquiv A v).down) := by
  let := T.topology
  change ULift.up (firstFactorUnitEquiv A'.representation
      (T.binaryRightZeroTensorEquiv rfl (A', T.binaryProductUnit)
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor a 0).map
          (CategoryTheory.Prod.mkHom f (𝟙 T.binaryProductUnit))) v))) = _
  rw [T.binaryRightZeroTensorEquiv_naturality rfl]
  exact congrArg ULift.up (firstFactorUnitEquiv_naturality (SmoothRep.hom f) _)

/-! ### Zero maps and zero objects -/

section ZeroMaps

variable {X Y : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}

private theorem map_eq_zero_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms E] {Φ Ψ : C × D ⥤ E} (e : Φ ≅ Ψ) {X Y : C × D} (f : X ⟶ Y)
    (h : Ψ.map f = 0) : Φ.map f = 0 := by
  rw [← NatIso.naturality_2 e f, h, zero_comp, comp_zero]

theorem binaryLeftZeroTensorFunctor_map_eq_zero (ha : a = 0)
    (f : letI := T.topology; X ⟶ Y) (hf : letI := T.topology; f.1 = 0 ∨ f.2 = 0) :
    letI := T.topology
    (T.binaryLeftZeroTensorFunctor ha).map f = 0 := by
  let := T.topology
  apply smoothRep_eq_zero
  refine (T.binaryLeftZeroTensorFunctor_map ha f).trans ?_
  rcases hf with hf | hf
  · rw [hf, smoothRep_hom_zero, Representation.IntertwiningMap.zero_toLinearMap,
      rankZeroLeftMap_zero_left]
    rfl
  · rw [hf, smoothRep_hom_zero, rankZeroLeftMap_zero_right]
    rfl

theorem binaryRightZeroTensorFunctor_map_eq_zero (hb : b = 0)
    (f : letI := T.topology; X ⟶ Y) (hf : letI := T.topology; f.1 = 0 ∨ f.2 = 0) :
    letI := T.topology
    (T.binaryRightZeroTensorFunctor hb).map f = 0 := by
  let := T.topology
  apply smoothRep_eq_zero
  refine (T.binaryRightZeroTensorFunctor_map hb f).trans ?_
  rcases hf with hf | hf
  · rw [hf, smoothRep_hom_zero, rankZeroRightMap_zero_left]
    rfl
  · rw [hf, smoothRep_hom_zero, Representation.IntertwiningMap.zero_toLinearMap,
      rankZeroRightMap_zero_right]
    rfl

theorem binaryPositiveProductFunctor_map_eq_zero (ha : 0 < a) (hb : 0 < b)
    (f : letI := T.topology; X ⟶ Y) (hf : letI := T.topology; f.1 = 0 ∨ f.2 = 0) :
    letI := T.topology
    (T.binaryPositiveProductFunctor ha hb).map f = 0 := by
  let := T.topology
  apply smoothRep_eq_zero
  refine (T.binaryPositiveProductFunctor_map ha hb f).trans ?_
  apply T.normalizedProductInducedMap_eq_zero
  rcases hf with hf | hf
  · exact FiniteTensor.externalMap_eq_zero_of_eq_zero _ (0 : Fin 2)
      ((congrArg SmoothRep.hom hf).trans smoothRep_hom_zero)
  · exact FiniteTensor.externalMap_eq_zero_of_eq_zero _ (1 : Fin 2)
      ((congrArg SmoothRep.hom hf).trans smoothRep_hom_zero)

/-- The product of a zero map with any map is zero, in all ranks. -/
theorem binaryNormalizedProductFunctor_map_eq_zero
    (f : letI := T.topology; X ⟶ Y) (hf : letI := T.topology; f.1 = 0 ∨ f.2 = 0) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a b).map f = 0 := by
  let := T.topology
  by_cases ha : a = 0
  · exact map_eq_zero_of_iso (T.binaryNormalizedProductLeftZeroIso ha) f
      (T.binaryLeftZeroTensorFunctor_map_eq_zero ha f hf)
  by_cases hb : b = 0
  · exact map_eq_zero_of_iso (T.binaryNormalizedProductRightZeroIso ha hb) f
      (T.binaryRightZeroTensorFunctor_map_eq_zero hb f hf)
  exact map_eq_zero_of_iso
    (T.binaryNormalizedProductPositiveIso (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)) f
    (T.binaryPositiveProductFunctor_map_eq_zero _ _ f hf)

/-- The product with a zero object is a zero object, in all ranks. -/
theorem isZero_binaryNormalizedProductFunctor_obj
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hX : letI := T.topology; IsZero X.1 ∨ IsZero X.2) :
    letI := T.topology
    IsZero ((T.binaryNormalizedProductFunctor a b).obj X) := by
  let := T.topology
  rw [IsZero.iff_id_eq_zero, ← (T.binaryNormalizedProductFunctor a b).map_id]
  apply T.binaryNormalizedProductFunctor_map_eq_zero
  rcases hX with hX | hX
  · exact Or.inl (hX.eq_of_src _ _)
  · exact Or.inr (hX.eq_of_src _ _)

end ZeroMaps

end PadicField.TopologicalData

end Langlands
