import Langlands.Representation.Derivative.ZeroRankTensor
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
import Langlands.Representation.Filtration.QuotientFirstIso

/-!
# The right mixed-product derivative filtration with a `GL_0` factor

BZ77 4.14(b) when the general linear factor has rank zero. Then `B × A` is
`B ⊗ A` on `P_(0+r+1)`, with the group acting on `B` through the rank cast
`P_(0+r+1) = P_(r+1)`, so its `d`-th derivative is `B^(d) ⊗ A`. The only feasible
order pair is `(d, 0)`, and the filtration is `0 ⊆ (B × A)^(d)`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis
open ZeroRankTensor

universe uF uV

namespace RightMixedZeroRank

/-! ## One-step filtrations -/

section OneStep

universe uR uG uW uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G] {C : Type uC} [Category.{vC} C]

/-- The zero subfunctor. -/
def botSubfunctor (M : C ⥤ Rep.{uW} R G) : RepSubfunctor M where
  obj _ := ⊥
  map_mem {X Y} f {v} hv := by
    change v ∈ (⊥ : Submodule R (M.obj X)) at hv
    change (M.map f).hom v ∈ (⊥ : Submodule R (M.obj Y))
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]

/-- The whole functor as a subfunctor of itself. -/
def topSubfunctor (M : C ⥤ Rep.{uW} R G) : RepSubfunctor M where
  obj _ := ⊤
  map_mem {X Y} f {v} _ := by
    change (M.map f).hom v ∈ (⊤ : Submodule R (M.obj Y))
    exact Submodule.mem_top

/-- The filtration `0 ⊆ M` with one step. -/
def oneStepFiltration (M : C ⥤ Rep.{uW} R G) : RepFunctorFiltration M 1 where
  step i := Fin.cases (motive := fun _ => RepSubfunctor M) (botSubfunctor M)
    (fun _ => topSubfunctor M) i
  monotone X := by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact bot_le
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (not_le.mpr (Fin.succ_pos i))
      | succ j => exact le_rfl
  zero _ := rfl
  top _ := rfl

/-- The only graded piece of `0 ⊆ M` is `M`. -/
def oneStepGradedIso (M : C ⥤ Rep.{uW} R G) : (oneStepFiltration M).graded 0 ≅ M :=
  (botSubfunctor M).quotientNatIsoOfSurjective (topSubfunctor M) (topSubfunctor M).inclusion
    (fun X v => by
      change (Subtype.val v : M.obj X) ∈ (⊥ : Submodule R (M.obj X)) ↔
        (Subtype.val v : M.obj X) = 0
      exact Submodule.mem_bot R)
    (fun X v => ⟨(⟨v, Submodule.mem_top⟩ : ((topSubfunctor M).obj X).toSubmodule), rfl⟩)

/-- A functor isomorphic to every member of a one-element family is glued from it. -/
theorem isGluedFrom_of_iso {M : C ⥤ Rep.{uW} R G} {n : ℕ} (hn : n = 1)
    {pieces : Fin n → C ⥤ Rep.{uW} R G} (a : ∀ i, Nonempty (M ≅ pieces i)) :
    IsGluedFrom M pieces := by
  subst hn
  refine ⟨Equiv.refl _, oneStepFiltration M, fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain ⟨a⟩ := a 0
  exact ⟨oneStepGradedIso M ≪≫ a⟩

end OneStep

/-! ## The rank cast `P_(b+1) = P_(a+1)` -/

section RankCast

variable {R : Type*} [CommRing R]

/-- The identity `P_(b+1) → P_(a+1)` along a rank equality `a = b`. -/
def castHom {a b : ℕ} (h : a = b) : mirabolic b R →* mirabolic a R := by
  subst h
  exact MonoidHom.id _

theorem castHom_apply {a b : ℕ} (h : a = b) (x : mirabolic b R) (i j : Fin (a + 1)) :
    (castHom h x).val.val i j =
      x.val.val (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := by
  subst h
  rfl

theorem continuous_castHom [TopologicalSpace R] {a b : ℕ} (h : a = b) :
    Continuous (castHom (R := R) h) := by
  subst h
  exact continuous_id

theorem rightIndex_zero_inl_val (r : ℕ) (i : Fin (r + 1)) :
    (rightIndex 0 r (Sum.inl i)).val = i.val := by
  induction i using Fin.lastCases with
  | last => rw [rightIndex_last]; simp
  | cast i => simp [rightIndex_first_val]

/-- For `k = 0` the mirabolic block of the case (III) projection is the rank cast. -/
theorem rightUnitProjection_eq_castHom (r : ℕ) :
    rightUnitProjection (R := R) r = castHom (Nat.zero_add r).symm := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e : ∀ m : Fin (r + 1),
      rightIndex 0 r (Sum.inl m) = Fin.cast (by omega) m :=
    fun m => Fin.ext (by simp [rightIndex_zero_inl_val])
  rw [rightUnitProjection_apply, castHom_apply, e, e]

end RankCast

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Restriction along the rank cast is the published mirabolic rank transport. -/
def pullbackCastIso (T : F.TopologicalData) {a b : ℕ} (h : a = b)
    (φ : mirabolic b F.Carrier →* mirabolic a F.Carrier)
    (hφ : letI := T.topology; Continuous φ) (heq : φ = castHom h) :
    letI := T.topology
    Mirabolic.continuousPullbackFunctor φ hφ ≅ mirabolicRankCast.{uF, uV} T h := by
  letI := T.topology
  subst h heq
  exact NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => LinearMap.ext fun _ => rfl))
    fun _ => MixedProductTensor.smoothRep_hom_ext fun _ => rfl

/-- The order-`d` derivative commutes with the mirabolic rank transport. -/
def rankCastDerivativeIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) (d : ℕ)
    (ha : 0 < d ∧ d ≤ a + 1) (hb : 0 < d ∧ d ≤ b + 1) (h' : a + 1 - d = b + 1 - d) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivativeOfOrder T ψ b d hb ≅
      mirabolicDerivativeOfOrder T ψ a d ha ⋙ generalLinearRankCast T h' := by
  letI := T.topology
  subst h
  exact Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

/-! ## The product `B × A` with `A` on `GL_0` -/

/-- `B × A ≃ B ⊗ ULift A` for `A` on `GL_0`: evaluation at `1`, the trivial twist,
and `id ⊗ ULift.up`, with `P_(0+r+1)` acting on `B` through `rightUnitProjection`. -/
def rightMixedProductZeroEquiv (T : F.TopologicalData) (r : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :
    letI := T.topology
    ((T.rightMixedProductFunctor 0 r).obj X).representation.Equiv
      ((tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier)
        (GeneralLinear 0 F.Carrier)).obj
          ((Mirabolic.continuousPullbackFunctor (rightUnitProjection r)
              continuous_rightUnitProjection).obj X.1,
            MixedProductTensor.liftFunctor.{uF, uV, uF}.obj X.2)).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + r + 1)
  (Induction.compactInducedTopEquiv (rightSubgroup 0 r F.Carrier) mem_rightSubgroup_zero _
      ((isSmooth_twist_iff _ _ (T.rightCharacter 0 r).isOpen_ker).mpr
        (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth))).trans
    ((MixedProductTensor.compEquiv _
        (MixedProductTensor.twistOneEquiv _ (T.rightCharacter_zero_left r) _)).trans
      (Representation.Equiv.mk
        (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm)
        fun g => TensorProduct.ext' fun v w => by
          change X.1.representation (rightUnitProjection r g) v ⊗ₜ
              ULift.up (X.2.representation _ w) =
            X.1.representation (rightUnitProjection r g) v ⊗ₜ ULift.up w
          rw [representation_apply_of_rank_eq_zero rfl X.2.representation]
          rfl))

/-- `B × A ≅ B ⊗ ULift A`, naturally in `(B, A)`, when `A` is a representation of `GL_0`. -/
def rightMixedProductZeroIso (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    T.rightMixedProductFunctor.{uF, uV} 0 r ≅
      (Mirabolic.continuousPullbackFunctor (rightUnitProjection r)
          continuous_rightUnitProjection).prod MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (rightMixedProductZeroEquiv T r X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun φ =>
      LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.1).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.2)).toLinearMap ∘ₗ
            (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm).toLinearMap)
        (T.rightMixedEval X φ 1)

/-! ## Pasting -/

section Pasting

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : Type*} [Category X₁] [Category X₂] [Category Y₁]
  [Category Y₂] [Category Z₁] [Category Z₂] [Category W₁] [Category W₂]

/-- Paste `S ≅ (P × Q) ⋙ T₁`, a square `T₁ ⋙ M ≅ (L × 𝟭) ⋙ T₂` and `P ⋙ L ≅ L₂`. -/
def sourcePaste {S : X₁ × X₂ ⥤ W₁} {P : X₁ ⥤ Y₁} {Q : X₂ ⥤ Y₂} {T₁ : Y₁ × Y₂ ⥤ W₁}
    {M : W₁ ⥤ W₂} {L : Y₁ ⥤ Z₁} {T₂ : Z₁ × Y₂ ⥤ W₂} {L₂ : X₁ ⥤ Z₁}
    (α : S ≅ P.prod Q ⋙ T₁) (β : T₁ ⋙ M ≅ L.prod (𝟭 Y₂) ⋙ T₂) (γ : P ⋙ L ≅ L₂) :
    S ⋙ M ≅ L₂.prod Q ⋙ T₂ :=
  Functor.isoWhiskerRight α M ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ β ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.prod γ (Functor.rightUnitor Q)) T₂

/-- Paste `B ≅ (𝟭 × Q) ⋙ T₁`, a square `T₁ ⋙ M ≅ (L × 𝟭) ⋙ T₂` and `D₂ ⋙ Q ≅ Q'`. -/
def piecePaste {D₁ : X₁ ⥤ Y₁} {D₂ : X₂ ⥤ Y₂} {B : Y₁ × Y₂ ⥤ W₁} {Q : Y₂ ⥤ Z₂}
    {T₁ : Y₁ × Z₂ ⥤ W₁} {M : W₁ ⥤ W₂} {L : Y₁ ⥤ Z₁} {T₂ : Z₁ × Z₂ ⥤ W₂} {Q' : X₂ ⥤ Z₂}
    (α : B ≅ (𝟭 Y₁).prod Q ⋙ T₁) (β : T₁ ⋙ M ≅ L.prod (𝟭 Z₂) ⋙ T₂) (δ : D₂ ⋙ Q ≅ Q') :
    (D₁.prod D₂ ⋙ B) ⋙ M ≅ (D₁ ⋙ L).prod Q' ⋙ T₂ :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (D₁.prod D₂) α ≪≫ (Functor.associator _ _ _).symm) M ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ β ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.prod (Iso.refl (D₁ ⋙ L)) δ) T₂

end Pasting

/-! ## Source and grade -/

/-- The derivative of `B × A` is `(B^(d) ⊗ A)` after the rank cast. -/
def sourceIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) (hd' : 0 < d ∧ d ≤ r + 1)
    (h' : r + 1 - d = (0 + r) + 1 - d) :
    letI := T.topology
    T.rightMixedProductFunctor.{uF, uV} 0 r ⋙ mirabolicDerivativeOfOrder T ψ (0 + r) d hd ≅
      (mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h').prod
          MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear ((0 + r) + 1 - d) F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  sourcePaste (rightMixedProductZeroIso T r)
    (mirabolicDerivativeOfOrderTensorIso (GeneralLinear 0 F.Carrier) T ψ (0 + r) d hd)
    (Functor.isoWhiskerRight
        (pullbackCastIso T (Nat.zero_add r).symm (rightUnitProjection r)
          continuous_rightUnitProjection (rightUnitProjection_eq_castHom r))
        (mirabolicDerivativeOfOrder T ψ (0 + r) d hd) ≪≫
      rankCastDerivativeIso T ψ (Nat.zero_add r).symm d hd' hd h')

/-- The `(d, 0)` grade `B^(d) × A^(0)` is `(B^(d) ⊗ A)` after the rank cast. -/
def pieceIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d N : ℕ)
    (hd' : 0 < d ∧ d ≤ r + 1) (h0 : 0 ≤ 0) (h : r + 1 - d = N) :
    letI := T.topology
    ((mirabolicDerivativeOfOrder T ψ r d hd').prod (generalLinearDerivative T ψ 0 0 h0) ⋙
        T.binaryNormalizedProductFunctor.{uF, uV} (r + 1 - d) 0) ⋙ generalLinearRankCast T h ≅
      (mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h).prod
          MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear N F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  piecePaste (binaryRightZeroIso T (r + 1 - d))
    (generalLinearRankCastTensorIso (GeneralLinear 0 F.Carrier) T h)
    (Functor.leftUnitor MixedProductTensor.liftFunctor.{uF, uV, uF} :
      generalLinearDerivative T ψ 0 0 h0 ⋙ MixedProductTensor.liftFunctor.{uF, uV, uF} ≅ _)

/-- The source is isomorphic to the unique feasible grade. -/
theorem nonempty_sourceIso_piece (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) (x : RightMixedDerivativeIndex 0 r d) :
    letI := T.topology
    Nonempty (rightMixedDerivativeSource.{uF, uV} T ψ 0 r d hd ≅
      rightMixedDerivativePiece T ψ 0 r d x) := by
  let _ := T.topology
  obtain ⟨⟨j, t⟩, hx⟩ := x
  obtain ⟨hj, ht⟩ : j = d ∧ t = 0 := by
    simp only [mem_rightMixedDerivativeIndices] at hx
    omega
  subst j t
  have hd' : 0 < d ∧ d ≤ r + 1 := ⟨hd.1, by omega⟩
  have h' : r + 1 - d = (0 + r) + 1 - d := by omega
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sourceIso T ψ r d hd hd' h') SmoothRep.toRep ≪≫
    (Functor.isoWhiskerRight (pieceIso T ψ r d _ hd' le_rfl h') SmoothRep.toRep).symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.associator _ _ _⟩

end RightMixedZeroRank

open RightMixedZeroRank

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- BZ77 4.14(b) for `k = 0`: the derivative of `B × A`, with `A` on `GL_0`, is glued
from the single feasible grade `B^(d) × A^(0)`. -/
theorem rightMixedProductDerivativeFiltration_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) :
    letI := T.topology
    ∃ e : Fin (rightMixedDerivativeIndices 0 r d).card ≃ RightMixedDerivativeIndex 0 r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ 0 r d hd)
        (fun i => rightMixedDerivativePiece T ψ 0 r d (e i)) := by
  let _ := T.topology
  have hd' : 0 < d ∧ d ≤ r + 1 := ⟨hd.1, by omega⟩
  refine ⟨(rightMixedDerivativeIndices 0 r d).equivFin.symm, ?_⟩
  refine isGluedFrom_of_iso ?_ fun i => nonempty_sourceIso_piece T ψ r d hd _
  rw [rightMixedDerivativeIndices_zero_gl r d hd', Finset.card_singleton]

end Langlands.Derivative
