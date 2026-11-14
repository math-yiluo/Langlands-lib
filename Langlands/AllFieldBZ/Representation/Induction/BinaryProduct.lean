import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.BinaryProduct

/-!
# All-field port of `Langlands.Representation.Induction.BinaryProduct`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.BinaryProduct` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ
universe uR uK uG uF uV uW uX uY uZ uU

namespace GeneralLinear
open Langlands.GeneralLinear
end GeneralLinear
namespace FiniteTensor
open Langlands.FiniteTensor
variable {R : Type uR} [CommRing R] {ι : Type uK} {H : ι → Type uG} [∀ i, Group (H i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

end FiniteTensor
namespace BinaryTensor
open Langlands.BinaryTensor
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
variable {V'' : Type uZ} [AddCommGroup V''] [Module ℂ V'']
variable {W : Type uX} [AddCommGroup W] [Module ℂ W]
variable {W' : Type uY} [AddCommGroup W'] [Module ℂ W']
variable {W'' : Type uU} [AddCommGroup W''] [Module ℂ W'']

/-! ### Pullback along a group homomorphism and carrier lifts -/

/-! ### The tensor unit -/

/-! ### The rank-zero tensor models -/

section Models
variable {R : Type uR} [CommRing R] {a b : ℕ}

end Models
section Smooth
variable [TopologicalSpace G]

end Smooth
end BinaryTensor
namespace LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear
open Langlands.BinaryTensor
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
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

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

/-- The published positive-block product on the binary shape `(a, b)`. -/
def binaryPositiveProductFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier) :=
  letI := T.topology
  T.binaryPairFamilyFunctor ha hb ⋙
    T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)

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

theorem binaryLeftZeroTensorFunctor_map (ha : a = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    SmoothRep.hom ((T.binaryLeftZeroTensorFunctor ha).map f) =
      rankZeroLeftMap ha (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2) := rfl

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

theorem binaryRightZeroTensorFunctor_map (hb : b = 0)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    SmoothRep.hom ((T.binaryRightZeroTensorFunctor hb).map f) =
      rankZeroRightMap hb (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap := rfl

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
end LocalFieldPackage.TopologicalData
end Langlands.AllFieldBZ
