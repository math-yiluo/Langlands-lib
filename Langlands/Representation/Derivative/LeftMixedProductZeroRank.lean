import Langlands.Representation.Derivative.ZeroRankTensor
import Langlands.Group.GL.RankReindex

/-!
# Derivatives of left mixed products with a `GL_0` factor

For an arbitrary smooth representation `A` of `GL_0` and `B` of `P_(r+1)`, the left
mixed product `A × B` is `B ⊗ A`, with `P_(0+r+1)` acting on `B` through
`leftUnitProjection r` and trivially on `A`. The derivative functors commute with the
inert factor `A`, so the order-`i` derivative of `A × B` is `B^{(i)} ⊗ A`, which is the
binary product `A × B^{(i)}` with a `GL_0` factor. This is the `k = 0` case of BZ77
4.14(a).
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.LeftMixedProductZeroRank

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis
open ZeroRankTensor

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## The left mixed product with a `GL_0` factor as a tensor product -/

/-- `(A, B) ↦ (B ∘ leftUnitProjection r, ULift A)`. -/
abbrev leftZeroInput (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⥤
      (SmoothRep.{0, uF, uV} ℂ (mirabolic (0 + r) F.Carrier) ×
        SmoothRep.{0, uF, max uV uF} ℂ (GeneralLinear 0 F.Carrier)) :=
  letI := T.topology
  CategoryTheory.Prod.swap _ _ ⋙
    (MixedProductTensor.pullbackFunctor (leftUnitProjection r) continuous_leftUnitProjection).prod
      MixedProductTensor.liftFunctor.{uF, uV, uF}

/-- The model `(A, B) ↦ (B ∘ leftUnitProjection r) ⊗ ULift A` of `A × B`, with
`P_(0+r+1)` acting on the first factor only. -/
abbrev leftZeroModel (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (0 + r) F.Carrier) :=
  letI := T.topology
  leftZeroInput.{uF, uV} T r ⋙
    tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier) (GeneralLinear 0 F.Carrier)

/-- The swap `a ⊗ b ↦ b ⊗ ULift.up a`. -/
abbrev swapLift (A : Type uV) [AddCommGroup A] [Module ℂ A] (B : Type uV) [AddCommGroup B]
    [Module ℂ B] : A ⊗[ℂ] B ≃ₗ[ℂ] B ⊗[ℂ] ULift.{uF} A :=
  (TensorProduct.comm ℂ A B).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ B) ULift.moduleEquiv.symm)

/-- `A × B ≃ (B ∘ leftUnitProjection r) ⊗ ULift A`: evaluation at `1`, followed by
`a ⊗ b ↦ b ⊗ ULift.up a`. -/
def leftZeroEquiv (T : F.TopologicalData) (r : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    letI := T.topology
    ((T.leftMixedProductFunctor 0 r).obj X).representation.Equiv
      ((leftZeroModel.{uF, uV} T r).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + r + 1)
  (Induction.compactInducedTopEquiv (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero _
      ((isSmooth_twist_iff _ _ (T.leftCharacter 0 r).isOpen_ker).mpr
        (isSmooth_leftInducingRepresentation X.1.isSmooth X.2.isSmooth))).trans
    ((MixedProductTensor.compEquiv _
        (MixedProductTensor.twistOneEquiv _ (T.leftCharacter_zero_left r) _)).trans
      (Representation.Equiv.mk (swapLift.{uF, uV} X.1 X.2) fun g =>
        TensorProduct.ext' fun a b => by
          have h1 : (leftProjection (Induction.topHom (leftSubgroup 0 r F.Carrier)
              mem_leftSubgroup_zero g)).1 = 1 :=
            Units.ext (Matrix.ext fun i => Fin.elim0 i)
          change X.2.representation (leftProjection (Induction.topHom
                (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero g)).2 b ⊗ₜ
              ULift.up (X.1.representation (leftProjection (Induction.topHom
                (leftSubgroup 0 r F.Carrier) mem_leftSubgroup_zero g)).1 a) =
            X.2.representation (leftUnitProjection r g) b ⊗ₜ ULift.up a
          rw [h1, map_one, Module.End.one_apply]
          rfl))

theorem leftZeroEquiv_apply (T : F.TopologicalData) (r : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor 0 r).obj X) :
    letI := T.topology
    leftZeroEquiv T r X f = swapLift.{uF, uV} X.1 X.2 (T.leftMixedEval X f 1) := rfl

/-- `A × B ≅ (B ∘ leftUnitProjection r) ⊗ ULift A`, naturally in `(A, B)`. -/
def leftZeroIso (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} 0 r ≅ leftZeroModel.{uF, uV} T r :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (leftZeroEquiv T r X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun v =>
      LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (swapLift.{uF, uV} Y.1 Y.2).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.2).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.1)).toLinearMap ∘ₗ
            (swapLift.{uF, uV} X.1 X.2).toLinearMap)
        (T.leftMixedEval X v 1)

/-! ## The binary product with a `GL_0` factor as a tensor product -/

/-- `(A, Y) ↦ (Y ∘ reindex, ULift A)` for `A` on `GL_0`. -/
abbrev rightZeroInput (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) ⥤
      (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + m) F.Carrier) ×
        SmoothRep.{0, uF, max uV uF} ℂ (GeneralLinear 0 F.Carrier)) :=
  letI := T.topology
  CategoryTheory.Prod.swap _ _ ⋙
    (MixedProductTensor.pullbackFunctor
        (reindex (R := F.Carrier) (finCongr (Nat.zero_add m))).toMonoidHom
        (continuous_reindex_finCongr _)).prod
      MixedProductTensor.liftFunctor.{uF, uV, uF}

/-- The model `(A, Y) ↦ (Y ∘ reindex) ⊗ ULift A` of `A × Y` for `A` on `GL_0`. -/
abbrev rightZeroModel (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (0 + m) F.Carrier) :=
  letI := T.topology
  rightZeroInput.{uF, uV} T m ⋙
    tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear (0 + m) F.Carrier)
      (GeneralLinear 0 F.Carrier)

/-- `A × Y ≃ (Y ∘ reindex) ⊗ ULift A` for `A` on `GL_0`: the published `a = 0` tensor
model followed by `a ⊗ y ↦ y ⊗ ULift.up a`. -/
def rightZeroEquiv (T : F.TopologicalData) (m : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor 0 m).obj X).representation.Equiv
      ((rightZeroModel.{uF, uV} T m).obj X).representation :=
  letI := T.topology
  (T.binaryLeftZeroTensorEquiv rfl X).trans
    (Representation.Equiv.mk (swapLift.{uF, uV} X.1 X.2) fun _ =>
      TensorProduct.ext' fun _ _ => rfl)

/-- `A × Y ≅ (Y ∘ reindex) ⊗ ULift A`, naturally in `(A, Y)`, for `A` on `GL_0`. -/
def rightZeroIso (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} 0 m ≅ rightZeroModel.{uF, uV} T m :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (rightZeroEquiv T m X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun v =>
      (congrArg (swapLift.{uF, uV} Y.1 Y.2)
        (T.binaryLeftZeroTensorEquiv_naturality rfl f v)).trans
      (LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (swapLift.{uF, uV} Y.1 Y.2).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.2).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.1)).toLinearMap ∘ₗ
            (swapLift.{uF, uV} X.1 X.2).toLinearMap)
        _)

/-! ## Products of functors -/

section ProductFunctors

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
  [Category B₁] [Category B₂] [Category B₃]

/-- `(F₁ × G₁) ⋙ (F₂ × G₂) ≅ (F₁ ⋙ F₂) × (G₁ ⋙ G₂)`. -/
def prodCompProdIso (F₁ : A₁ ⥤ A₂) (F₂ : A₂ ⥤ A₃) (G₁ : B₁ ⥤ B₂) (G₂ : B₂ ⥤ B₃) :
    F₁.prod G₁ ⋙ F₂.prod G₂ ≅ (F₁ ⋙ F₂).prod (G₁ ⋙ G₂) :=
  Iso.refl _

/-- `(F × G) ⋙ swap ≅ swap ⋙ (G × F)`. -/
def prodCompSwapIso (F : A₁ ⥤ A₂) (G : B₁ ⥤ B₂) :
    F.prod G ⋙ CategoryTheory.Prod.swap A₂ B₂ ≅ CategoryTheory.Prod.swap A₁ B₁ ⋙ G.prod F :=
  Iso.refl _

end ProductFunctors

/-! ## Rank casts -/

/-- Pullback along a homomorphism that is pointwise the identity is the identity. -/
def pullbackIdIso {G : Type uF} [Group G] [TopologicalSpace G] (φ : G →* G)
    (hφ : Continuous φ) (h : ∀ g, φ g = g) :
    MixedProductTensor.pullbackFunctor.{uF, uF, uV} φ hφ ≅ 𝟭 (SmoothRep.{0, uF, uV} ℂ G) :=
  NatIso.ofComponents
    (fun X => SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g =>
      LinearMap.ext fun v => by
        change X.representation (φ g) v = X.representation g v
        rw [h]))
    fun _ => rfl

/-- The `GL` rank cast is the pullback along the entry-preserving reindex. -/
def generalLinearRankCastPullbackIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ≅
      MixedProductTensor.pullbackFunctor
        (reindex (R := F.Carrier) (finCongr h.symm)).toMonoidHom
        (continuous_reindex_finCongr _) := by
  letI := T.topology
  subst h
  exact (pullbackIdIso _ _ fun _ => Units.ext (Matrix.ext fun _ _ => rfl)).symm

/-- Pulling back along a mirabolic homomorphism that reads the entries at the cast
indices, then taking the order-`i` derivative and casting the `GL` rank, is the
order-`i` derivative followed by the pullback along the reindex. -/
def pullbackDerivativeCastIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N r : ℕ} (hN : N = r)
    (φ : mirabolic N F.Carrier →* mirabolic r F.Carrier)
    (hφc : letI := T.topology; Continuous φ)
    (hφ : ∀ g a b, (φ g).val.val a b =
      g.val.val (Fin.cast (by omega) a) (Fin.cast (by omega) b))
    (i : ℕ) (hi : 0 < i ∧ i ≤ r + 1) (hi' : 0 < i ∧ i ≤ N + 1)
    (h₁ : N + 1 - i = 0 + (r + 1 - i)) :
    letI := T.topology
    MixedProductTensor.pullbackFunctor.{uF, uF, uV} φ hφc ⋙
        mirabolicDerivativeOfOrder T ψ N i hi' ⋙ generalLinearRankCast T h₁ ≅
      mirabolicDerivativeOfOrder T ψ r i hi ⋙
        MixedProductTensor.pullbackFunctor
          (reindex (R := F.Carrier) (finCongr (Nat.zero_add (r + 1 - i)))).toMonoidHom
          (continuous_reindex_finCongr _) := by
  letI := T.topology
  subst hN
  exact Functor.isoWhiskerRight
      (pullbackIdIso φ hφc fun g => Subtype.ext (Units.ext (Matrix.ext fun a b => hφ g a b)))
      _ ≪≫ Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerLeft _ (generalLinearRankCastPullbackIso T h₁)

/-- `leftUnitProjection r` reads the entries at the cast indices. -/
theorem leftUnitProjection_entry (r : ℕ) (g : mirabolic (0 + r) F.Carrier)
    (a b : Fin (r + 1)) :
    (leftUnitProjection r g).val.val a b =
      g.val.val (Fin.cast (by omega) a) (Fin.cast (by omega) b) := by
  have h : ∀ c : Fin (r + 1), leftIndex 0 r (Sum.inr c) = Fin.cast (by omega) c :=
    fun c => Fin.ext (by simp)
  rw [leftUnitProjection_apply, h, h]

/-! ## The derivative of the left mixed product with a `GL_0` factor -/

/-- The order-`i` derivative on `P_(0+r+1)` and the rank cast commute with the inert
factor. -/
def tensorDerivativeCastIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r i : ℕ)
    (hi : 0 < i ∧ i ≤ r + 1) :
    letI := T.topology
    tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier)
          (GeneralLinear 0 F.Carrier) ⋙
        mirabolicDerivativeOfOrder T ψ (0 + r) i ⟨hi.1, by omega⟩ ⋙
          generalLinearRankCast T (show 0 + r + 1 - i = 0 + (r + 1 - i) by omega) ≅
      (mirabolicDerivativeOfOrder T ψ (0 + r) i ⟨hi.1, by omega⟩ ⋙
          generalLinearRankCast T (show 0 + r + 1 - i = 0 + (r + 1 - i) by omega)).prod
          (𝟭 _) ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear (0 + (r + 1 - i)) F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  prodCommIsoComp
    (mirabolicDerivativeOfOrderTensorIso (GeneralLinear 0 F.Carrier) T ψ (0 + r) i
      ⟨hi.1, by omega⟩)
    (generalLinearRankCastTensorIso (GeneralLinear 0 F.Carrier) T
      (show 0 + r + 1 - i = 0 + (r + 1 - i) by omega))

/-- On the inputs: the cast order-`i` derivative of `B ∘ leftUnitProjection r` is
`B^{(i)} ∘ reindex`, and the `GL_0` factor is unchanged. -/
def inputDerivativeIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r i : ℕ)
    (hi : 0 < i ∧ i ≤ r + 1) :
    letI := T.topology
    leftZeroInput.{uF, uV} T r ⋙
        (mirabolicDerivativeOfOrder T ψ (0 + r) i ⟨hi.1, by omega⟩ ⋙
          generalLinearRankCast T (show 0 + r + 1 - i = 0 + (r + 1 - i) by omega)).prod
          (𝟭 _) ≅
      (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
        rightZeroInput.{uF, uV} T (r + 1 - i) :=
  letI := T.topology
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap _ _) (prodCompProdIso _ _ _ _) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap _ _)
      (NatIso.prod
        (pullbackDerivativeCastIso T ψ (Nat.zero_add r) (leftUnitProjection r)
          continuous_leftUnitProjection (leftUnitProjection_entry r) i hi ⟨hi.1, by omega⟩
          (by omega))
        (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap _ _) (prodCompProdIso _ _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (prodCompSwapIso _ _).symm _ ≪≫
    Functor.associator _ _ _

/-- BZ77 4.14(a) for `GL` rank `0`: for every smooth representation `A` of `GL_0` and
`B` of `P_(r+1)` and every order `1 ≤ i ≤ r + 1`, the order-`i` derivative of `A × B`,
after the rank cast `GL_(0+r+1-i) = GL_(0+(r+1-i))`, is naturally `A × B^{(i)}`. -/
def leftMixedProductZeroRankIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r i : ℕ)
    (hi : 0 < i ∧ i ≤ r + 1) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF, uV} 0 r ⋙
        mirabolicDerivativeOfOrder T ψ (0 + r) i ⟨hi.1, by omega⟩ ⋙
          generalLinearRankCast T (show 0 + r + 1 - i = 0 + (r + 1 - i) by omega) ≅
      (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
        T.binaryNormalizedProductFunctor 0 (r + 1 - i) :=
  letI := T.topology
  Functor.isoWhiskerRight (leftZeroIso.{uF, uV} T r) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (leftZeroInput.{uF, uV} T r)
      (tensorDerivativeCastIso.{uF, uV} T ψ r i hi) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (inputDerivativeIso.{uF, uV} T ψ r i hi) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi))
      (rightZeroIso.{uF, uV} T (r + 1 - i)).symm

end Langlands.Derivative.LeftMixedProductZeroRank
