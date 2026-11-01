import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# Derivatives of tensor products with an inert factor

Character localization of the first factor of `V ⊗ W` is `V_{U,θ} ⊗ W`, compatibly
with the descended action. Hence `Φ⁻`, `Ψ⁻`, their iterates, the order-indexed
mirabolic derivative and the `GL` derivative commute with tensoring by a carrier on
which the group acts trivially. The binary product `A × B` with `B` on `GL_0` is such
a tensor product. These are the rank-zero ingredients of BZ77 4.14(b) and (c).
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative.ZeroRankTensor

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis

universe uF uG uH uK uV uW

/-! ## Localization of the first tensor factor -/

section Coinvariants

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `[v ⊗ w] ↦ [v] ⊗ w`, from the localization of `V ⊗ W` to `V_{U,θ} ⊗ W`. -/
def coinvariantsTensorForward (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] :
    Jacquet.Localization.Coinvariants (BinaryTensor.firstFactor ρ W) U θ →ₗ[ℂ]
      Jacquet.Localization.Coinvariants ρ U θ ⊗[ℂ] W :=
  Jacquet.Localization.lift _ U θ
    (TensorProduct.map (Jacquet.Localization.mk ρ U θ) LinearMap.id) (fun u x => by
      induction x using TensorProduct.inductionOn with
      | tmul v w =>
        change Jacquet.Localization.mk ρ U θ (ρ u v) ⊗ₜ w =
          (θ u : ℂ) • (Jacquet.Localization.mk ρ U θ v ⊗ₜ w)
        rw [Jacquet.Localization.mk_apply_subgroup, TensorProduct.smul_tmul']
      | add x y hx hy => simp only [map_add, hx, hy, smul_add])

/-- `[v] ⊗ w ↦ [v ⊗ w]`, the inverse of `coinvariantsTensorForward`. -/
def coinvariantsTensorBackward (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] :
    Jacquet.Localization.Coinvariants ρ U θ ⊗[ℂ] W →ₗ[ℂ]
      Jacquet.Localization.Coinvariants (BinaryTensor.firstFactor ρ W) U θ :=
  TensorProduct.lift (Jacquet.Localization.lift ρ U θ
    ((TensorProduct.mk ℂ V W).compr₂
      (Jacquet.Localization.mk (BinaryTensor.firstFactor ρ W) U θ)) (fun u v => by
        ext w
        exact Jacquet.Localization.mk_apply_subgroup (BinaryTensor.firstFactor ρ W) U θ u
          (v ⊗ₜ w)))

/-- Character localization of the first factor commutes with `⊗ W`. -/
def coinvariantsTensorEquiv (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] :
    Jacquet.Localization.Coinvariants (BinaryTensor.firstFactor ρ W) U θ ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants ρ U θ ⊗[ℂ] W :=
  LinearEquiv.ofLinearMap (coinvariantsTensorForward ρ U θ W) (coinvariantsTensorBackward ρ U θ W)
    (by
      apply TensorProduct.ext'
      intro a w
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ U θ a
      rfl)
    (by
      apply Jacquet.Localization.hom_ext
      apply TensorProduct.ext'
      intro v w
      rfl)

@[simp]
theorem coinvariantsTensorEquiv_mk (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] (v : V) (w : W) :
    coinvariantsTensorEquiv ρ U θ W
        (Jacquet.Localization.mk (BinaryTensor.firstFactor ρ W) U θ (v ⊗ₜ w)) =
      Jacquet.Localization.mk ρ U θ v ⊗ₜ w := rfl

end Coinvariants

/-! ## Tensoring with an inert factor -/

section TensorFunctor

variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (K : Type uK) [Group K] [TopologicalSpace K]

/-- `X ⊗ A` with `G` acting on `X` only; the action of `K` on `A` is forgotten. -/
abbrev tensorObj (X : SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uK, uW} ℂ K) :
    SmoothRep.{0, uG, max uV uW} ℂ G :=
  SmoothRep.of (BinaryTensor.firstFactor X.1.representation X.2)
    (BinaryTensor.isSmooth_firstFactor X.1.isSmooth)

/-- The bifunctor `(X, A) ↦ X ⊗ A`, with `G` acting on the first factor only. -/
def tensorFunctor :
    SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uK, uW} ℂ K ⥤ SmoothRep.{0, uG, max uV uW} ℂ G where
  obj X := tensorObj G K X
  map f := SmoothRep.ofHom
    (BinaryTensor.firstFactorMap (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap)
  map_id X := by
    change SmoothRep.ofHom (A := tensorObj G K X) (B := tensorObj G K X)
        (BinaryTensor.firstFactorMap (Representation.IntertwiningMap.id X.1.representation)
          LinearMap.id) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [BinaryTensor.firstFactorMap_id]
  map_comp {X Y Z} f g := by
    change SmoothRep.ofHom (A := tensorObj G K X) (B := tensorObj G K Z)
        (BinaryTensor.firstFactorMap ((SmoothRep.hom g.1).comp (SmoothRep.hom f.1))
          ((SmoothRep.hom g.2).toLinearMap ∘ₗ (SmoothRep.hom f.2).toLinearMap)) =
      SmoothRep.ofHom
        ((BinaryTensor.firstFactorMap (SmoothRep.hom g.1) (SmoothRep.hom g.2).toLinearMap).comp
          (BinaryTensor.firstFactorMap (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap))
    rw [BinaryTensor.firstFactorMap_comp]

@[simp]
theorem tensorFunctor_obj (X : SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uK, uW} ℂ K) :
    (tensorFunctor.{uG, uK, uV, uW} G K).obj X = tensorObj G K X := rfl

theorem tensorFunctor_map {X Y : SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uK, uW} ℂ K}
    (f : X ⟶ Y) :
    SmoothRep.hom ((tensorFunctor.{uG, uK, uV, uW} G K).map f) =
      BinaryTensor.firstFactorMap (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap := rfl

end TensorFunctor

/-- Morphisms of smooth representations agree when their linear maps agree. -/
theorem smoothRep_hom_ext {G : Type uG} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uG, uV} ℂ G} {f g : A ⟶ B}
    (h : (SmoothRep.hom f).toLinearMap = (SmoothRep.hom g).toLinearMap) : f = g :=
  MixedProductTensor.smoothRep_hom_ext fun x => LinearMap.congr_fun h x

/-! ## Localization functors commute with the inert tensor factor -/

section Localization

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {K : Type uK} [Group K] [TopologicalSpace K]
variable (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
  (hθ : Jacquet.Localization.IsInvariant U M hMU θ) (e : H →* M) (he : Continuous e)
  (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))

/-- Localize, restrict along `e`, and twist by `χ`: the shape of `Φ⁻` and `Ψ⁻`. -/
abbrev localizationFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H :=
  (Jacquet.Localization.smoothFunctor U θ M hMU hθ ⋙
      Mirabolic.continuousPullbackFunctor e he) ⋙ SmoothRep.twistFunctor χ hχ

/-- The component `L(X ⊗ A) ≃ L(X) ⊗ A`, `[v ⊗ a] ↦ [v] ⊗ a`. -/
def localizationTensorEquiv (X : SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uK, uW} ℂ K) :
    ((localizationFunctor U θ M hMU hθ e he χ hχ).obj
        ((tensorFunctor.{uG, uK, uV, uW} G K).obj X)).representation.Equiv
      ((tensorFunctor.{uH, uK, uV, uW} H K).obj
        ((localizationFunctor U θ M hMU hθ e he χ hχ).obj X.1, X.2)).representation :=
  Representation.Equiv.mk (coinvariantsTensorEquiv X.1.representation U θ X.2) fun h => by
    apply Jacquet.Localization.hom_ext
    apply TensorProduct.ext'
    intro v w
    change coinvariantsTensorEquiv X.1.representation U θ X.2
        ((χ h : ℂ) • Jacquet.Localization.mk _ U θ
          (X.1.representation (e h : G) v ⊗ₜ w)) =
      ((χ h : ℂ) • Jacquet.Localization.mk X.1.representation U θ
        (X.1.representation (e h : G) v)) ⊗ₜ w
    rw [map_smul, ← TensorProduct.smul_tmul']
    rfl

/-- `L ∘ (· ⊗ ·) ≅ (· ⊗ ·) ∘ (L × 𝟭)` for every localization functor `L`. -/
def localizationTensorIso :
    tensorFunctor.{uG, uK, uV, uW} G K ⋙ localizationFunctor U θ M hMU hθ e he χ hχ ≅
      (localizationFunctor U θ M hMU hθ e he χ hχ).prod (𝟭 _) ⋙
        tensorFunctor.{uH, uK, uV, uW} H K :=
  NatIso.ofComponents
    (fun X => SmoothRep.mkIso (localizationTensorEquiv U θ M hMU hθ e he χ hχ X))
    (fun {X Y} f => smoothRep_hom_ext (by
      apply Jacquet.Localization.hom_ext
      apply TensorProduct.ext'
      intro v w
      rfl))

end Localization

/-- Restriction along a continuous homomorphism commutes with the inert tensor factor. -/
def pullbackTensorIso {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] (K : Type uK) [Group K] [TopologicalSpace K]
    (e : H →* G) (he : Continuous e) :
    tensorFunctor.{uG, uK, uV, uW} G K ⋙ Mirabolic.continuousPullbackFunctor e he ≅
      (Mirabolic.continuousPullbackFunctor e he).prod (𝟭 _) ⋙
        tensorFunctor.{uH, uK, uV, uW} H K :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-! ## Pasting commutation squares -/

section Pasting

variable {A₁ A₂ A₃ B C₁ C₂ C₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B]
  [Category C₁] [Category C₂] [Category C₃]

/-- Two squares `T ⋙ M ≅ (L × 𝟭) ⋙ T'` paste along the middle bifunctor. -/
def prodCommIsoComp {T₁ : A₁ × B ⥤ C₁} {T₂ : A₂ × B ⥤ C₂} {T₃ : A₃ × B ⥤ C₃}
    {L : A₁ ⥤ A₂} {M : C₁ ⥤ C₂} {L' : A₂ ⥤ A₃} {M' : C₂ ⥤ C₃}
    (α : T₁ ⋙ M ≅ L.prod (𝟭 B) ⋙ T₂) (β : T₂ ⋙ M' ≅ L'.prod (𝟭 B) ⋙ T₃) :
    T₁ ⋙ M ⋙ M' ≅ (L ⋙ L').prod (𝟭 B) ⋙ T₃ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α M' ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ β ≪≫ (Functor.associator _ _ _).symm

end Pasting

/-! ## Minus functors and derivatives -/

section Derivatives

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (K : Type uK) [Group K] [TopologicalSpace K]

/-- `Φ⁻(X ⊗ A) ≅ Φ⁻(X) ⊗ A`, naturally in `(X, A)`. -/
def phiMinusTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + 1) F.Carrier) K ⋙ Mirabolic.phiMinus T ψ n ≅
      (Mirabolic.phiMinus T ψ n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K := by
  letI := T.topology
  exact localizationTensorIso (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)
    (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
    (Mirabolic.theta_isInvariant ψ n)
    (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (Mirabolic.phiMinusCharacter T n) (Mirabolic.isOpen_ker_phiMinusCharacter T n)

/-- `Ψ⁻(X ⊗ A) ≅ Ψ⁻(X) ⊗ A`, naturally in `(X, A)`. -/
def psiMinusTensorIso (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K ⋙ Mirabolic.psiMinus T n ≅
      (Mirabolic.psiMinus T n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K := by
  letI := T.topology
  exact localizationTensorIso (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
    leviSubgroup_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer)
    (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (Mirabolic.psiMinusCharacter T n) (Mirabolic.isOpen_ker_psiMinusCharacter T n)

/-- `(Φ⁻)^k(X ⊗ A) ≅ (Φ⁻)^k(X) ⊗ A`. -/
def phiMinusIterateTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + k) F.Carrier) K ⋙
          phiMinusIterate T ψ n k ≅
        (phiMinusIterate T ψ n k).prod (𝟭 _) ⋙
          tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K
  | 0 => letI := T.topology; Iso.refl _
  | k + 1 => letI := T.topology
      prodCommIsoComp (phiMinusTensorIso K T ψ (n + k)) (phiMinusIterateTensorIso T ψ n k)

/-- The mirabolic derivative `Ψ⁻ ∘ (Φ⁻)^k` commutes with the inert tensor factor. -/
def mirabolicDerivativeTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + k) F.Carrier) K ⋙
        mirabolicDerivative T ψ n k ≅
      (mirabolicDerivative T ψ n k).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (phiMinusIterateTensorIso K T ψ n k) (psiMinusTensorIso K T n)

/-- The mirabolic rank transport commutes with the inert tensor factor. -/
def mirabolicRankCastTensorIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic a F.Carrier) K ⋙ mirabolicRankCast T h ≅
      (mirabolicRankCast T h).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic b F.Carrier) K := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-- The order-indexed mirabolic derivative commutes with the inert tensor factor. -/
def mirabolicDerivativeOfOrderTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ)
    (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic N F.Carrier) K ⋙
        mirabolicDerivativeOfOrder T ψ N k hk ≅
      (mirabolicDerivativeOfOrder T ψ N k hk).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (N + 1 - k) F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (mirabolicRankCastTensorIso K T (mirabolic_rank_eq_of_order hk))
    (mirabolicDerivativeTensorIso K T ψ (N + 1 - k) (k - 1))

/-- The `GL` rank transport commutes with the inert tensor factor. -/
def generalLinearRankCastTensorIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear a F.Carrier) K ⋙ generalLinearRankCast T h ≅
      (generalLinearRankCast T h).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear b F.Carrier) K := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-- Restriction from `GL_(n+1)` to `P_(n+1)` commutes with the inert tensor factor. -/
def generalLinearRestrictionTensorIso (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (n + 1) F.Carrier) K ⋙
        generalLinearRestriction T n ≅
      (generalLinearRestriction T n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K := by
  letI := T.topology
  exact pullbackTensorIso K (mirabolic n F.Carrier).subtype continuous_subtype_val

/-- The positive-order `GL` derivative commutes with the inert tensor factor. -/
def generalLinearDerivativePositiveTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (n + k + 1) F.Carrier) K ⋙
        generalLinearDerivativePositive T ψ n k ≅
      (generalLinearDerivativePositive T ψ n k).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (generalLinearRestrictionTensorIso K T (n + k))
    (mirabolicDerivativeTensorIso K T ψ n k)

/-- The `k`-th `GL` derivative commutes with the inert tensor factor. -/
def generalLinearDerivativeTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) :
    (k : ℕ) → (hk : k ≤ N) →
      letI := T.topology
      tensorFunctor.{uF, uK, uV, uW} (GeneralLinear N F.Carrier) K ⋙
          generalLinearDerivative T ψ N k hk ≅
        (generalLinearDerivative T ψ N k hk).prod (𝟭 _) ⋙
          tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (N - k) F.Carrier) K
  | 0, _ => letI := T.topology; Iso.refl _
  | k + 1, hk => letI := T.topology
      prodCommIsoComp (generalLinearRankCastTensorIso K T (rank_eq_of_succ_le hk))
        (generalLinearDerivativePositiveTensorIso K T ψ (N - (k + 1)) k)

end Derivatives

/-! ## The binary product with a `GL_0` factor -/

section BinaryZero

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `A × B ≃ A ⊗ ULift B` for a representation `B` of `GL_0`: the published `b = 0`
model followed by `ULift.up` on the second factor. -/
def binaryRightZeroEquiv (T : F.TopologicalData) (a : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a 0).obj X).representation.Equiv
      ((tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear a F.Carrier)
        (GeneralLinear 0 F.Carrier)).obj
          (X.1, MixedProductTensor.liftFunctor.{uF, uV, uF}.obj X.2)).representation :=
  letI := T.topology
  (T.binaryRightZeroTensorEquiv rfl X).trans
    (Representation.Equiv.mk
      (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm)
      fun g => TensorProduct.ext' fun v w => by
        change X.1.representation (GeneralLinear.reindex (finCongr _) g) v ⊗ₜ ULift.up w =
          X.1.representation g v ⊗ₜ ULift.up w
        rfl)

/-- `A × B ≅ A ⊗ ULift B`, naturally in `(A, B)`, when `B` is a representation of `GL_0`. -/
def binaryRightZeroIso (T : F.TopologicalData) (a : ℕ) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} a 0 ≅
      (𝟭 _).prod MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear a F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (binaryRightZeroEquiv T a X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun v =>
      (congrArg (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm)
        (T.binaryRightZeroTensorEquiv_naturality rfl f v)).trans
      (LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.1).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.2)).toLinearMap ∘ₗ
            (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm).toLinearMap)
        _)

end BinaryZero

end Langlands.Derivative.ZeroRankTensor
