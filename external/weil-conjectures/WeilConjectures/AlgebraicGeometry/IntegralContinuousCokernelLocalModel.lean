/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.IntegralContinuousPresentationMatrix
public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import all WeilConjectures.AlgebraicGeometry.IntegralContinuousPresentationMatrix
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.LinearAlgebra.ContinuousIntegralMatrixLocalSmith

/-!
# Integral continuous cokernels of locally constant scalar type

Source: HRS Example 3.1; local Smith argument of the parent comparison, step 5.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal
open scoped CategoryTheory.Obj
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse
namespace AlgebraicGeometry.ProEtale.ContinuousRingUniverse

open scoped Topology
open Filter Metric

private theorem unitBall_isAdic {K : Type u} [NormedField K]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1)
    (π : A) (hπ0 : π ≠ 0) (hπ : ‖π‖ < 1) :
    IsAdic (Ideal.span ({π} : Set A)) := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    apply AddSubgroup.isOpen_of_mem_nhds (Submodule.toAddSubgroup _)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : A) (pow_pos (norm_pos_iff.mpr hπ0) n))
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Ideal.span_singleton_pow]
    change x ∈ Ideal.span ({π ^ n} : Set A)
    rw [Ideal.mem_span_singleton]
    have hp : (π.val ^ n : K) ≠ 0 := pow_ne_zero n (by exact_mod_cast hπ0)
    let y : A := ⟨x.val / π.val ^ n, (hA _).mpr (by
      rw [norm_div, norm_pow]
      exact (div_lt_one (pow_pos (norm_pos_iff.mpr (by exact_mod_cast hπ0)) n)).mpr hx |>.le)⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (mul_div_cancel₀ x.val hp).symm
  · intro s hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ
    refine ⟨n, fun x hx ↦ hεs ?_⟩
    rw [Ideal.span_singleton_pow] at hx
    change x ∈ Ideal.span ({π ^ n} : Set A) at hx
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg π) n) ((hA _).mp a.property)).trans_lt hn

private noncomputable def integerEquiv (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
  RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
    (latticeCoefficientIntegers l E) (Padic.coefficientExtensionIntegers l E)
    (fun _ ↦ Iff.rfl)

private instance equivInvPair {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : RingHomInvPair e.toRingHom e.symm.toRingHom where
  comp_eq := by ext x; exact e.symm_apply_apply x
  comp_eq₂ := by ext x; exact e.apply_symm_apply x

private instance equivInvPairSymm {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.symm _ _

private noncomputable def vectorEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (n : ℕ) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) (Fin n → A) (Fin n → B) where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := by ext i; exact e.symm_apply_apply _
  right_inv x := by ext i; exact e.apply_symm_apply _
  map_add' x y := by ext i; exact e.map_add _ _
  map_smul' a x := by ext i; exact e.map_mul _ _

private theorem vectorEquiv_range {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {m n : ℕ} (F : Matrix (Fin n) (Fin m) A) :
    (LinearMap.range F.mulVecLin).map (vectorEquiv e n).toLinearMap =
      LinearMap.range (F.map e).mulVecLin := by
  classical
  have hm (x : Fin m → A) : vectorEquiv e n (F.mulVecLin x) =
      (F.map e).mulVecLin (vectorEquiv e m x) := by
    ext i
    simp [vectorEquiv, Matrix.mulVec, dotProduct, map_sum, map_mul]
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨vectorEquiv e m x, (hm x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨F.mulVecLin ((vectorEquiv e m).symm x), ⟨_, rfl⟩, ?_⟩
    change vectorEquiv e n (F.mulVecLin ((vectorEquiv e m).symm x)) = _
    rw [hm, LinearEquiv.apply_symm_apply]

private noncomputable def quotientEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {m n : ℕ} (F : Matrix (Fin n) (Fin m) A) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((Fin n → A) ⧸ LinearMap.range F.mulVecLin)
      ((Fin n → B) ⧸ LinearMap.range (F.map e).mulVecLin) :=
  Submodule.Quotient.equiv _ _ (vectorEquiv e n) (vectorEquiv_range e F)

private noncomputable def transportQuotientIso {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {m n : ℕ} (F G : Matrix (Fin n) (Fin m) A)
    (a : ((Fin n → A) ⧸ LinearMap.range F.mulVecLin) ≃ₗ[A]
      ((Fin n → A) ⧸ LinearMap.range G.mulVecLin)) :
    ((Fin n → B) ⧸ LinearMap.range (F.map e).mulVecLin) ≃ₗ[B]
      ((Fin n → B) ⧸ LinearMap.range (G.map e).mulVecLin) := by
  let ez := quotientEquiv e F
  let ey := quotientEquiv e G
  refine { (ez.symm.toAddEquiv.trans a.toAddEquiv).trans ey.toAddEquiv with
    map_smul' := ?_ }
  intro b x
  change ey (a (ez.symm (b • x))) = b • ey (a (ez.symm x))
  rw [map_smulₛₗ, map_smul, map_smulₛₗ]
  simp

private theorem integer_adic (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsAdic ((Padic.coefficientExtensionMaximalIdeal l E).comap
      (integerEquiv l E).toRingHom) := by
  let a := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let π := Padic.coefficientExtensionUniformizer l E
  have hgen : Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let q := (integerEquiv l E).symm π
  have hq0 : q ≠ 0 := by
    intro hq
    have hz : π = 0 := by simpa [q] using congrArg (integerEquiv l E) hq
    have := h.2.2.2.2.2.2.2.2.2.1
    apply this
    change Padic.coefficientExtensionMaximalIdeal l E = ⊥
    rw [← hgen, hz]
    simp
  have hq : ‖q‖ < 1 := by
    apply (h.2.1 π).mp
    change π ∈ Padic.coefficientExtensionMaximalIdeal l E
    rw [← hgen]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hA (x : WithAbs a) : x ∈ latticeCoefficientIntegers l E ↔ ‖x‖ ≤ 1 :=
    h.1 x.ofAbs
  have hspan : (Padic.coefficientExtensionMaximalIdeal l E).comap
      (integerEquiv l E).toRingHom = Ideal.span ({q} : Set (latticeCoefficientIntegers l E)) := by
    rw [← hgen]
    change Ideal.comap (integerEquiv l E) _ = _
    rw [← Ideal.map_symm (integerEquiv l E), Ideal.map_span]
    congr 1
    ext x
    simp [q]
  rw [hspan]
  exact unitBall_isAdic _ hA q hq0 hq

private theorem smith_transport {A B Y : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A]
    [TopologicalSpace Y] (e : A ≃+* B) (hci : Continuous e.symm)
    {m n : ℕ} (F : Y → Matrix (Fin n) (Fin m) A) (U : TopologicalSpace.Opens Y)
    (L : U → Matrix.GeneralLinearGroup (Fin n) B)
    (R : U → Matrix.GeneralLinearGroup (Fin m) B)
    (D : Matrix (Fin n) (Fin m) B)
    (hL : ∀ i j, Continuous (fun z ↦ L z i j))
    (hLi : ∀ i j, Continuous (fun z ↦ (L z)⁻¹ i j))
    (hR : ∀ i j, Continuous (fun z ↦ R z i j))
    (hRi : ∀ i j, Continuous (fun z ↦ (R z)⁻¹ i j))
    (hred : ∀ z : U, (L z : Matrix (Fin n) (Fin n) B) * (F z.val).map e *
      (R z : Matrix (Fin m) (Fin m) B) = D) :
    ∃ (a ai : Matrix (Fin n) (Fin n) C(U, A))
      (b bi : Matrix (Fin m) (Fin m) C(U, A)) (d : Matrix (Fin n) (Fin m) A),
      a * ai = 1 ∧ ai * a = 1 ∧ b * bi = 1 ∧ bi * b = 1 ∧
      ∀ z : U, a.map (fun f ↦ f z) * F z.val * b.map (fun f ↦ f z) = d := by
  classical
  let a : Matrix (Fin n) (Fin n) C(U, A) :=
    fun i j ↦ ⟨fun z ↦ e.symm (L z i j), hci.comp (hL i j)⟩
  let ai : Matrix (Fin n) (Fin n) C(U, A) :=
    fun i j ↦ ⟨fun z ↦ e.symm ((L z)⁻¹ i j), hci.comp (hLi i j)⟩
  let b : Matrix (Fin m) (Fin m) C(U, A) :=
    fun i j ↦ ⟨fun z ↦ e.symm (R z i j), hci.comp (hR i j)⟩
  let bi : Matrix (Fin m) (Fin m) C(U, A) :=
    fun i j ↦ ⟨fun z ↦ e.symm ((R z)⁻¹ i j), hci.comp (hRi i j)⟩
  have hprod {k : ℕ} (M N : Matrix (Fin k) (Fin k) C(U, A))
      (h : ∀ z : U, M.map (fun f ↦ f z) * N.map (fun f ↦ f z) = 1) : M * N = 1 := by
    apply Matrix.ext
    intro i j
    apply ContinuousMap.ext
    intro z
    have hz := congrArg (fun P : Matrix (Fin k) (Fin k) A ↦ P i j) (h z)
    by_cases hij : i = j <;>
      simpa only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
        Matrix.map_apply, Matrix.one_apply, hij, ite_true, ite_false, ContinuousMap.one_apply,
        ContinuousMap.zero_apply] using hz
  have hunit {k : ℕ} (M : Matrix.GeneralLinearGroup (Fin k) B) :
      M.val.map e.symm * (M⁻¹).val.map e.symm = 1 ∧
        (M⁻¹).val.map e.symm * M.val.map e.symm = 1 := by
    constructor
    · rw [← Matrix.map_mul, M.mul_inv, Matrix.map_one] <;> simp only [map_zero, map_one]
    · rw [← Matrix.map_mul, M.inv_mul, Matrix.map_one] <;> simp only [map_zero, map_one]
  refine ⟨a, ai, b, bi, D.map e.symm,
    hprod a ai (fun z ↦ (hunit (L z)).1),
    hprod ai a (fun z ↦ (hunit (L z)).2),
    hprod b bi (fun z ↦ (hunit (R z)).1),
    hprod bi b (fun z ↦ (hunit (R z)).2), ?_⟩
  intro z
  have hz := congrArg (fun M : Matrix (Fin n) (Fin m) B ↦ M.map e.symm) (hred z)
  change ((L z).val.map e.symm * F z.val * (R z).val.map e.symm) = D.map e.symm
  rw [Matrix.map_mul, Matrix.map_mul] at hz
  have hf : ((F z.val).map e).map e.symm = F z.val := by
    apply Matrix.ext
    intro i j
    change e.symm (e (F z.val i j)) = F z.val i j
    exact e.symm_apply_apply _
  rw [hf] at hz
  exact hz

private theorem integral_local_smith (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y : Type u} [TopologicalSpace Y] {m n : ℕ}
    (F : Y → Matrix (Fin n) (Fin m) (latticeCoefficientIntegers l E))
    (hF : ∀ i j, Continuous (fun y ↦ F y i j))
    (ht : ∀ y, ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧ ∀ z ∈ W, Nonempty
      (((Fin n → latticeCoefficientIntegers l E) ⧸ LinearMap.range (F z).mulVecLin)
        ≃ₗ[latticeCoefficientIntegers l E]
        ((Fin n → latticeCoefficientIntegers l E) ⧸ LinearMap.range (F y).mulVecLin))) :
    ∃ W : Y → TopologicalSpace.Opens Y, (∀ y, y ∈ W y) ∧ ∀ y,
      ∃ (L Li : Matrix (Fin n) (Fin n) C(W y, latticeCoefficientIntegers l E))
        (R Ri : Matrix (Fin m) (Fin m) C(W y, latticeCoefficientIntegers l E))
        (D : Matrix (Fin n) (Fin m) (latticeCoefficientIntegers l E)),
        L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
        ∀ z : W y, (L.map (fun a ↦ a z)) * F z.val * (R.map (fun a ↦ a z)) = D := by
  classical
  let A := latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let J := Padic.coefficientExtensionMaximalIdeal l E
  let e := integerEquiv l E
  let I := J.comap e.toRingHom
  let topA : TopologicalSpace A := inferInstance
  let : WithIdeal A := ⟨I⟩
  let : WithIdeal B := ⟨J⟩
  have heI : I.map e.toRingHom = J := Ideal.map_comap_of_surjective e.toRingHom e.surjective J
  have hadic : topA = I.adicTopology := integer_adic l E
  have hc : @Continuous A B topA J.adicTopology e := by
    rw [hadic]
    let : UniformSpace A := WithIdeal.instUniformSpace A
    let : UniformSpace B := WithIdeal.instUniformSpace B
    exact (WithIdeal.uniformEquiv e heI).continuous
  have hci : @Continuous B A J.adicTopology topA e.symm := by
    rw [hadic]
    let : UniformSpace A := WithIdeal.instUniformSpace A
    let : UniformSpace B := WithIdeal.instUniformSpace B
    exact (WithIdeal.uniformEquiv e heI).symm.continuous
  let G : Y → Matrix (Fin n) (Fin m) B := fun y ↦ (F y).map e
  have hG : ∀ i j, @Continuous Y B _ J.adicTopology (fun y ↦ G y i j) :=
    fun i j ↦ hc.comp (hF i j)
  have htG (y : Y) : ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧ ∀ z ∈ W, Nonempty
      (((Fin n → B) ⧸ LinearMap.range (G z).mulVecLin) ≃ₗ[B]
        ((Fin n → B) ⧸ LinearMap.range (G y).mulVecLin)) := by
    obtain ⟨W, hy, hW⟩ := ht y
    refine ⟨W, hy, fun z hz ↦ ?_⟩
    obtain ⟨a⟩ := hW z hz
    exact ⟨transportQuotientIso e (F z) (F y) a⟩
  let π := Padic.coefficientExtensionUniformizer l E
  have hp : Ideal.span ({π} : Set B) = J :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
        |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  obtain ⟨W, hW, hred⟩ :=
    Padic.continuous_integral_matrix_local_smith l E π hp Y m n G hG htG
  refine ⟨W, hW, fun y ↦ ?_⟩
  obtain ⟨L, R, r, hr, ex, D, he, hD, hL, hLi, hR, hRi, hred⟩ := hred y
  let : TopologicalSpace B := J.adicTopology
  exact smith_transport e hci F (W y) L R D hL hLi hR hRi hred

open MatrixCalculus

@[irreducible] private noncomputable def coeffPullbackIso (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    (upperStar AddCommGrpCat.{u + 1} g).obj (coeff E V) ≅ coeff E W :=
  (restrictionIso g hg).app (coeff E V)

private lemma coeffPullbackIso_mon (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    IsMonHom (coeffPullbackIso E g hg).hom := by
  unfold coeffPullbackIso
  have := restriction_monoidal g hg
  have he := CategoryTheory.pushforwardRingMonObj (MorphismProperty.Over.map ⊤ hg)
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology V) (continuousCoefficientRingSheaf V E)
  change @IsMonHom _ _ _ _ _ ((upperStar AddCommGrpCat.{u + 1} g).monObjObj (coeff E V))
    (Sheaf.monObj_sheafCompose_obj (Scheme.ProEt.topology W)
      (continuousCoefficientRingSheaf W E)) ((restrictionIso g hg).hom.app (coeff E V))
  erw [he]
  exact NatTrans.isMonHom_app (restrictionIso g hg).hom (coeff E V)

attribute [local instance] coeffPullbackIso_mon
attribute [local instance] comparison_isIso

@[irreducible] private noncomputable def pulledRealization (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R] [IsCommMonObj R]
    (e : R ⟶ coeff E V) :
    (upperStar AddCommGrpCat.{u + 1} g).obj R ⟶ coeff E W :=
  (upperStar AddCommGrpCat.{u + 1} g).map e ≫ (coeffPullbackIso E g hg).hom

private lemma pulledRealization_isIso (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R] [IsCommMonObj R]
    (e : R ⟶ coeff E V) [IsIso e] : IsIso (pulledRealization E g hg e) := by
  unfold pulledRealization
  infer_instance

attribute [local instance] pulledRealization_isIso

private lemma pulledRealization_isMonHom (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R] [IsCommMonObj R]
    (e : R ⟶ coeff E V) [IsMonHom e] : IsMonHom (pulledRealization E g hg e) := by
  unfold pulledRealization
  infer_instance

attribute [local instance] pulledRealization_isMonHom

private theorem conjugate_naturalIso {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (α : F ≅ G) {A B : C} (e : A ⟶ B) [IsIso e] (f : A ⟶ A) :
    inv (F.map e ≫ α.hom.app B) ≫ F.map f ≫ (F.map e ≫ α.hom.app B) =
      G.map (inv e ≫ f ≫ e) := by
  rw [IsIso.inv_comp, ← F.map_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  rw [Category.assoc (inv e) f e]
  rw [α.hom.naturality, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types true in
private lemma endFun_pullback {E : Type u} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R] [IsCommMonObj R]
    (e : R ⟶ coeff E V) [IsIso e] [IsMonHom e]
    (f : Mod.regular R ⟶ Mod.regular R) :
    MatrixCalculus.endFun (pulledRealization E g hg e)
      (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f) =
      (MatrixCalculus.endFun e f).comp g.base.hom := by
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := (MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)
  let a : coeff E V ⟶ coeff E V := inv e ≫ f.hom ≫ e
  rw [MatrixCalculus.endFun_eq, MatrixCalculus.endFun_eq]
  have hc : inv (pulledRealization E g hg (R := R) e) ≫ F.map f.hom ≫
      pulledRealization E g hg (R := R) e = G.map a := by
    unfold pulledRealization coeffPullbackIso
    exact conjugate_naturalIso F G (restrictionIso g hg) e f.hom
  change coeffEndFun (inv (pulledRealization E g hg (R := R) e) ≫ F.map f.hom ≫
    pulledRealization E g hg (R := R) e) = _
  rw [hc]
  change ((a.hom.app _ (ULift.up 1)).down) = _
  erw [MatrixCalculus.coeff_app_one a]
  rfl

@[irreducible] private noncomputable def freePullbackIso {V W : Scheme.{u}} (g : W ⟶ V)
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R] [IsCommMonObj R]
    (n : ℕ) :
    ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj (Mod.finiteFree R n) ≅
      Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) n :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).mapBiproduct
    (fun _ : Fin n ↦ Mod.regular R)

private lemma freeMatrix_pullback {E : Type u} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R] [IsCommMonObj R]
    (e : R ⟶ coeff E V) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    MatrixCalculus.freeMatrix (pulledRealization E g hg e)
      ((freePullbackIso g R m).inv ≫ ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f ≫
        (freePullbackIso g R n).hom) =
      (MatrixCalculus.freeMatrix e f).map
        (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [MatrixCalculus.freeMatrix, freePullbackIso, Functor.mapBiproduct_inv,
    Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, Category.assoc]
  erw [biproduct.lift_π]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  exact endFun_pullback g hg e _

private instance point_colimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

private instance point_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

@[irreducible] private noncomputable def scalarMul {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (a : T) : baseRing T ⟶ baseRing T :=
  ⟨{ app S := AddCommGrpCat.ofHom
      { toFun f := ULift.up (f.down * ContinuousMap.const S.unop a)
        map_zero' := by
          change ULift.up (0 * _) = ULift.up (0 : C(S.unop, T))
          rw [zero_mul]
        map_add' f g := by exact congrArg ULift.up (add_mul _ _ _) }
     naturality S S' g := by
       apply ConcreteCategory.hom_ext
       intro f
       rfl }⟩

private theorem scalarMul_linear {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (a : T) :
    (MonObj.mul : baseRing T ⊗ baseRing T ⟶ _) ≫ scalarMul a =
      baseRing T ◁ scalarMul a ≫ MonObj.mul := by
  unfold scalarMul
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    Sheaf.μ_comp_map_mul]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext
  ext f g : 2
  change ULift.up ((f.down * g.down) * _) = ULift.up (f.down * (g.down * _))
  rw [mul_assoc]

@[irreducible] private noncomputable def scalarEnd {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (a : T) : Mod.regular (baseRing T) ⟶ Mod.regular (baseRing T) :=
  Mod.homMk (scalarMul a) (scalarMul_linear a)

private theorem adjoint_intertwines {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B : D}
    (η : A ⟶ R.obj B) (f : A ⟶ A) (g : B ⟶ B)
    (h : f ≫ η = η ≫ R.map g) :
    L.map f ≫ (adj.homEquiv A B).symm η = (adj.homEquiv A B).symm η ≫ g := by
  apply (adj.homEquiv A B).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  exact h

private theorem scalarMul_comparison {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (X : Scheme.{u}) (a : T) :
    (upperStarFromPoint X).map (scalarMul a) ≫ comparison X T =
      comparison X T ≫ MatrixCalculus.coeffMul (ContinuousMap.const X a) := by
  unfold comparison
  apply adjoint_intertwines
  unfold scalarMul
  apply Sheaf.hom_ext
  ext S : 2
  rfl

private theorem endFun_mapMod
    {C : Type*} [Category C] [MonoidalCategory C]
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    {X : Scheme.{u}} (F : C ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [F.LaxMonoidal] (R : C) [MonObj R]
    (e : F.obj R ⟶ coeff T X) [IsIso e] [IsMonHom e]
    (f : Mod.regular R ⟶ Mod.regular R) :
    MatrixCalculus.endFun e ((F.mapMod R).map f) =
      coeffEndFun (inv e ≫ F.map f.hom ≫ e) := by
  rfl

section
attribute [local irreducible] upperStarFromPoint

set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarEnd_matrix {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T] (X : Scheme.{u}) (a : T) :
    MatrixCalculus.endFun (R := baseCoeff T X) (comparison X T)
      (((upperStarFromPoint X).mapMod (baseRing T)).map (scalarEnd (T := T) a)) =
        ContinuousMap.const X a := by
  have := comparison_isIso X T
  rw [endFun_mapMod]
  unfold scalarEnd
  change coeffEndFun (inv (comparison X T) ≫
    (upperStarFromPoint X).map (scalarMul a) ≫ comparison X T) = _
  rw [scalarMul_comparison, IsIso.inv_hom_id_assoc]
  exact MatrixCalculus.coeffEndFun_mul _

@[irreducible] private noncomputable def scalarMatrix {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {m n : ℕ} (D : Matrix (Fin n) (Fin m) T) :
    Mod.finiteFree (baseRing T) m ⟶ Mod.finiteFree (baseRing T) n :=
  biproduct.matrix fun j i ↦ scalarEnd (D i j)

@[irreducible] private noncomputable def pointFreeIso (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod (baseRing T)).obj
      (Mod.finiteFree (baseRing T) n) ≅ Mod.finiteFree (baseCoeff T X) n :=
  ((upperStarFromPoint X).mapMod (baseRing T)).mapBiproduct
    (fun _ : Fin n ↦ Mod.regular (baseRing T))

set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarMatrix_matrix {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (X : Scheme.{u}) {m n : ℕ} (D : Matrix (Fin n) (Fin m) T) :
    MatrixCalculus.freeMatrix (comparison X T)
      ((pointFreeIso T X m).inv ≫
        ((upperStarFromPoint X).mapMod (baseRing T)).map (scalarMatrix D) ≫
          (pointFreeIso T X n).hom) = D.map (ContinuousMap.const X) := by
  have := comparison_isIso X T
  apply Matrix.ext
  intro i j
  simp only [MatrixCalculus.freeMatrix, pointFreeIso, Functor.mapBiproduct_inv,
    Functor.mapBiproduct_hom, biproduct.ι_desc_assoc, Category.assoc]
  erw [biproduct.lift_π]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [scalarMatrix, biproduct.ι_matrix, biproduct.lift_π]
  exact scalarEnd_matrix (T := T) X (D i j)

end

-- Keep the point functor folded when constructing and using its module objects.
attribute [local irreducible] upperStarFromPoint

@[irreducible] private noncomputable def pointScalarMatrix
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (Y : Scheme.{u}) {m n : ℕ} (D : Matrix (Fin n) (Fin m) T) :
    Mod.finiteFree (baseCoeff T Y) m ⟶ Mod.finiteFree (baseCoeff T Y) n :=
  (pointFreeIso T Y m).inv ≫
    ((upperStarFromPoint Y).mapMod (baseRing T)).map (scalarMatrix D) ≫
      (pointFreeIso T Y n).hom

private theorem pointScalarMatrix_coordinates
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (Y : Scheme.{u}) {m n : ℕ}
    (D : Matrix (Fin n) (Fin m) T) :
    MatrixCalculus.freeMatrix (comparison Y T) (pointScalarMatrix T Y D) =
      D.map (ContinuousMap.const Y) := by
  unfold pointScalarMatrix
  exact scalarMatrix_matrix Y D

private theorem freeMatrix_eq_private {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (e : R ⟶ coeff T X) [IsIso e] [IsMonHom e] {m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    ContinuousRingUniverse.freeMatrix e f = MatrixCalculus.freeMatrix e f := by
  funext i j
  rw [ContinuousRingUniverse.freeMatrix_apply]
  exact (MatrixCalculus.endFun_eq e _).symm

set_option backward.isDefEq.respectTransparency.types true in
private theorem freeMatrix_comap {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    (φ : S ⟶ R) [IsIso φ] [IsMonHom φ]
    (e : R ⟶ coeff T X) [IsIso e] [IsMonHom e] {m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    MatrixCalculus.freeMatrix (φ ≫ e)
      ((Mod.finiteFreeIsoComap φ m).inv ≫ (Mod.comap φ).map f ≫
        (Mod.finiteFreeIsoComap φ n).hom) = MatrixCalculus.freeMatrix e f := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [MatrixCalculus.freeMatrix, Mod.finiteFreeIsoComap,
    Iso.trans_inv, Iso.trans_hom, Functor.mapBiproduct_inv,
    Functor.mapBiproduct_hom,
    biproduct.mapIso_inv, biproduct.mapIso_hom, Category.assoc,
    biproduct.ι_map_assoc, biproduct.ι_desc_assoc]
  erw [biproduct.map_π]
  erw [biproduct.lift_π_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [MatrixCalculus.endFun_eq, MatrixCalculus.endFun_eq]
  apply congrArg coeffEndFun
  simp only [Iso.symm_inv, Iso.symm_hom, Mod.regularIsoComapRegular, Mod.isoMk_hom_hom,
    Mod.isoMk_inv_hom, asIso_hom, asIso_inv, Mod.comp_hom', Mod.comap_map_hom]
  simp only [IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id_assoc]

private theorem freeMatrix_congr {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (e e' : R ⟶ coeff T X) [IsIso e] [IsIso e'] [IsMonHom e] [IsMonHom e']
    {m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) (h : e = e') :
    MatrixCalculus.freeMatrix e f = MatrixCalculus.freeMatrix e' f := by
  subst e'
  rfl

private theorem freeMatrix_comap_eq {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]
    (φ : S ⟶ R) [IsIso φ] [IsMonHom φ]
    (e : R ⟶ coeff T X) [IsIso e] [IsMonHom e]
    (e' : S ⟶ coeff T X) [IsIso e'] [IsMonHom e']
    (h : φ ≫ e = e') {m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    MatrixCalculus.freeMatrix e'
      ((Mod.finiteFreeIsoComap φ m).inv ≫ (Mod.comap φ).map f ≫
        (Mod.finiteFreeIsoComap φ n).hom) = ContinuousRingUniverse.freeMatrix e f := by
  exact (freeMatrix_congr e' (φ ≫ e) _ h.symm).trans
    ((freeMatrix_comap φ e f).trans (freeMatrix_eq_private e f).symm)

@[irreducible] private noncomputable def matrixIso {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (e : R ⟶ coeff T X) [IsIso e] [IsMonHom e] {n : ℕ}
    (L Li : Matrix (Fin n) (Fin n) C(X, T)) (h : L * Li = 1) (hi : Li * L = 1) :
    Mod.finiteFree R n ≅ Mod.finiteFree R n where
  hom := MatrixCalculus.ofFreeMatrix e L
  inv := MatrixCalculus.ofFreeMatrix e Li
  hom_inv_id := by
    rw [← MatrixCalculus.ofFreeMatrix_mul, hi, MatrixCalculus.ofFreeMatrix_one]
  inv_hom_id := by
    rw [← MatrixCalculus.ofFreeMatrix_mul, h, MatrixCalculus.ofFreeMatrix_one]

private theorem matrix_conjugation {T : Type u} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X : Scheme.{u}}
    {S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj S]
    (e : S ⟶ coeff T X) [IsIso e] [IsMonHom e] {m n : ℕ}
    (f d : Mod.finiteFree S m ⟶ Mod.finiteFree S n)
    (L Li : Matrix (Fin n) (Fin n) C(X, T))
    (R Ri : Matrix (Fin m) (Fin m) C(X, T))
    (hL : L * Li = 1) (hLi : Li * L = 1) (hR : R * Ri = 1) (hRi : Ri * R = 1)
    (h : L * MatrixCalculus.freeMatrix e f * R = MatrixCalculus.freeMatrix e d) :
    (matrixIso e R Ri hR hRi).hom ≫ f ≫ (matrixIso e L Li hL hLi).hom = d := by
  apply MatrixCalculus.freeMatrix_injective e
  rw [MatrixCalculus.freeMatrix_comp, MatrixCalculus.freeMatrix_comp]
  simpa only [matrixIso, MatrixCalculus.freeMatrix_ofFreeMatrix, Matrix.mul_assoc] using h

@[irreducible] private noncomputable def extend_comap_cancel
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsIso φ] [IsMonHom φ] (N : Mod C S) :
    (Mod.extendScalars φ).obj ((Mod.comap φ).obj N) ≅ N :=
  (Mod.extendScalarsIsoComapInv φ).app _ ≪≫
    (Mod.comapComp (inv φ) φ).symm.app N ≪≫
      (Mod.comapCongr (by simp)).app N ≪≫ (Mod.comapId S).app N

@[irreducible] private noncomputable def normalizedCokernelIso
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasFiniteColimits C] [HasFiniteColimits D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F]
    {A B : C} {U V : D} (f : A ⟶ B) (p : F.obj A ≅ U) (q : F.obj B ≅ V) :
    F.obj (cokernel f) ≅ cokernel (p.inv ≫ F.map f ≫ q.hom) :=
  PreservesCokernel.iso F f ≪≫ cokernel.mapIso _ _ p q (by simp)

@[irreducible] private noncomputable def pointScalarCokernelIso
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (Y : Scheme.{u}) {m n : ℕ} (D : Matrix (Fin n) (Fin m) T) :
    cokernel (pointScalarMatrix T Y D) ≅
      ((upperStarFromPoint Y).mapMod (baseRing T)).obj (cokernel (scalarMatrix D)) := by
  unfold pointScalarMatrix
  exact (normalizedCokernelIso ((upperStarFromPoint Y).mapMod (baseRing T))
    (scalarMatrix D) (pointFreeIso T Y m) (pointFreeIso T Y n)).symm

@[irreducible] private noncomputable def mappedCokernelIso
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasFiniteColimits C] [HasFiniteColimits D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F]
    {A B : C} {U V : D} (f d : A ⟶ B) (p : F.obj A ≅ U) (q : F.obj B ≅ V)
    (a : U ≅ U) (b : V ≅ V)
    (h : a.hom ≫ (p.inv ≫ F.map f ≫ q.hom) ≫ b.hom =
      p.inv ≫ F.map d ≫ q.hom) : F.obj (cokernel f) ≅ F.obj (cokernel d) := by
  let fw := p.inv ≫ F.map f ≫ q.hom
  let dw := p.inv ≫ F.map d ≫ q.hom
  have h' : a.hom ≫ fw ≫ b.hom = dw := h
  let k : cokernel fw ≅ cokernel dw :=
    cokernel.mapIso fw dw a.symm b (by
      rw [← h']
      simp only [Iso.symm_hom, Iso.inv_hom_id_assoc])
  let cf : F.obj (cokernel f) ≅ cokernel fw :=
    PreservesCokernel.iso F f ≪≫ cokernel.mapIso _ _ p q (by simp [fw])
  let cd : F.obj (cokernel d) ≅ cokernel dw :=
    PreservesCokernel.iso F d ≪≫ cokernel.mapIso _ _ p q (by simp [dw])
  exact cf ≪≫ k ≪≫ cd.symm

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStar

private theorem cokernelIso_of_restricted_matrices
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    {Y W : Scheme.{u}} (g : W ⟶ Y) (hg : WeaklyEtale g)
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (e : S ⟶ coeff T Y) [IsIso e] [IsMonHom e] {m n : ℕ}
    (f d : Mod.finiteFree S m ⟶ Mod.finiteFree S n)
    (L Li : Matrix (Fin n) (Fin n) C(W, T))
    (R Ri : Matrix (Fin m) (Fin m) C(W, T))
    (hL : L * Li = 1) (hLi : Li * L = 1) (hR : R * Ri = 1) (hRi : Ri * R = 1)
    (h : L * (MatrixCalculus.freeMatrix e f).map
        (ContinuousMap.compRightAlgHom ℤ T ⟨g.base.hom, g.continuous⟩) * R =
      (MatrixCalculus.freeMatrix e d).map
        (ContinuousMap.compRightAlgHom ℤ T ⟨g.base.hom, g.continuous⟩)) :
    Nonempty (((upperStar Ab.{u + 1} g).mapMod S).obj (cokernel f) ≅
      ((upperStar Ab.{u + 1} g).mapMod S).obj (cokernel d)) := by
  let F := (upperStar Ab.{u + 1} g).mapMod S
  let ew := pulledRealization T g hg e
  let fw := (freePullbackIso g S m).inv ≫ F.map f ≫ (freePullbackIso g S n).hom
  let dw := (freePullbackIso g S m).inv ≫ F.map d ≫ (freePullbackIso g S n).hom
  let a := matrixIso ew R Ri hR hRi
  let b := matrixIso ew L Li hL hLi
  have heq : a.hom ≫ fw ≫ b.hom = dw := by
    apply matrix_conjugation (T := T) ew fw dw L Li R Ri hL hLi hR hRi
    rw [freeMatrix_pullback (E := T), freeMatrix_pullback (E := T)]
    exact h
  exact ⟨mappedCokernelIso F f d (freePullbackIso g S m) (freePullbackIso g S n) a b heq⟩

private theorem model_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (C.f i)).mapIso e ≪≫ eP⟩⟩

private theorem continuous_matrix_restrict_eq
    {T Z : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TopologicalSpace Z] (U : TopologicalSpace.Opens Z) {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) C(Z, T))
    (L : Matrix (Fin n) (Fin n) C(U, T))
    (R : Matrix (Fin m) (Fin m) C(U, T)) (D : Matrix (Fin n) (Fin m) T)
    (h : ∀ z : U, L.map (fun a ↦ a z) * A.map (fun a ↦ a z.val) *
      R.map (fun a ↦ a z) = D) :
    L * A.map (ContinuousMap.compRightAlgHom ℤ T
      ⟨Subtype.val, continuous_subtype_val⟩) * R = D.map (ContinuousMap.const U) := by
  ext i j z
  have hz := congrFun (congrFun (h z) i) j
  simpa [Matrix.mul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.mul_apply] using hz

private theorem open_inclusion_base {Y : Scheme.{u}} (U : Y.Opens) :
    (⟨U.ι.base.hom, U.ι.continuous⟩ : C(U, Y)) =
      ⟨Subtype.val, continuous_subtype_val⟩ := rfl

private theorem exists_open_cover {Y : Scheme.{u}}
    (P : ∀ {Z : Scheme.{u}}, (Z ⟶ Y) → Prop)
    (W : Y → TopologicalSpace.Opens Y) (hW : ∀ y, y ∈ W y)
    (h : ∀ y, P (Scheme.Opens.ι (X := Y) (W y))) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i, P (C.f i) := by
  classical
  let O := Y.openCoverOfIsOpenCover W (by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hW x⟩)
  exact ⟨O.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage, h⟩

private theorem localModelIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y W : Scheme.{u}} (g : W ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (c : ((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ Y)).obj M ≅
      ((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ Y)).obj N)
    (e : N ≅ ((upperStarFromPoint Y).mapMod Λ).obj P) :
    Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
      ((upperStarFromPoint W).mapMod Λ).obj P) :=
  ⟨(Mod.extendScalars (condensedPullbackHom Λ g)).mapIso
      (c ≪≫ ((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ Y)).mapIso e) ≪≫
    (Mod.extendScalars (condensedPullbackHom Λ g)).mapIso
      ((Functor.mapModCompIso (upperStarFromPoint Y) (upperStar Ab.{u + 1} g)
        (upperStarFromPointComp g).hom Λ).app P) ≪≫
      extend_comap_cancel (condensedPullbackHom Λ g) _⟩

@[irreducible] private noncomputable def changeCoefficientCokernelIso
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [Abelian C] [MonoidalPreadditive C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] {m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    (Mod.extendScalars φ).obj (cokernel f) ≅
      cokernel ((Mod.finiteFreeIsoComap (inv φ) m).inv ≫
        (Mod.comap (inv φ)).map f ≫ (Mod.finiteFreeIsoComap (inv φ) n).hom) :=
  (Mod.extendScalarsIsoComapInv φ).app _ ≪≫
    normalizedCokernelIso (Mod.comap (inv φ)) f
      (Mod.finiteFreeIsoComap (inv φ) m) (Mod.finiteFreeIsoComap (inv φ) n)

attribute [local irreducible] CondensedRing.upperStar MatrixCalculus.freeMatrix

set_option backward.isDefEq.respectTransparency.types true in
private theorem local_model_of_smith_aux
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} {m n : ℕ}
    (e : condensedRingObj Λ Y ⟶ coeff T Y) [IsIso e] [IsMonHom e]
    (f : Mod.finiteFree (condensedRingObj Λ Y) m ⟶
      Mod.finiteFree (condensedRingObj Λ Y) n)
    (hscalar : ∀ D : Matrix (Fin n) (Fin m) T,
      ∃ d : Mod.finiteFree (condensedRingObj Λ Y) m ⟶
        Mod.finiteFree (condensedRingObj Λ Y) n,
        MatrixCalculus.freeMatrix (E := T) e d = D.map (ContinuousMap.const Y) ∧
        ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
          Mod.IsFinitelyPresented Λ P ∧
          Nonempty (cokernel d ≅ ((upperStarFromPoint Y).mapMod Λ).obj P))
    (W : Y → TopologicalSpace.Opens Y) (hW : ∀ y, y ∈ W y)
    (hs : ∀ y, ∃ (L Li : Matrix (Fin n) (Fin n) C(W y, T))
      (R Ri : Matrix (Fin m) (Fin m) C(W y, T)) (D : Matrix (Fin n) (Fin m) T),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧ ∀ z : W y,
      (L.map (fun a ↦ a z)) *
        ((MatrixCalculus.freeMatrix (E := T) e f).map (fun a ↦ a z.val)) *
          (R.map (fun a ↦ a z)) = D) :
    HasFiniteConstantLocalModel Λ Y (cokernel f) := by
  classical
  choose LL LLi RR RRi DD hLL hLLi hRR hRRi hDD using hs
  apply exists_open_cover
    (fun {Z} g ↦ ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((CondensedRing.upperStar Λ g).obj (cokernel f) ≅
        ((upperStarFromPoint Z).mapMod Λ).obj P)) W hW
  intro y
  let L := LL y
  let Li := LLi y
  let R := RR y
  let Ri := RRi y
  let D := DD y
  have hL := hLL y
  have hLi := hLLi y
  have hR := hRR y
  have hRi := hRRi y
  have hD := hDD y
  obtain ⟨d, hd, P, hP, ⟨model⟩⟩ := hscalar D
  have hg : WeaklyEtale (Scheme.Opens.ι (X := Y) (W y)) := inferInstance
  have hmatrix : L * (MatrixCalculus.freeMatrix (E := T) e f).map
      (ContinuousMap.compRightAlgHom ℤ T
        ⟨(Scheme.Opens.ι (X := Y) (W y)).base.hom,
          (Scheme.Opens.ι (X := Y) (W y)).continuous⟩) * R =
      (MatrixCalculus.freeMatrix (E := T) e d).map
        (ContinuousMap.compRightAlgHom ℤ T
        ⟨(Scheme.Opens.ι (X := Y) (W y)).base.hom,
          (Scheme.Opens.ι (X := Y) (W y)).continuous⟩) := by
    rw [hd]
    rw [open_inclusion_base (W y)]
    exact continuous_matrix_restrict_eq (W y) _ L R D hD
  obtain ⟨c⟩ := cokernelIso_of_restricted_matrices T
    (Scheme.Opens.ι (X := Y) (W y)) hg
    (condensedRingObj Λ Y)
    e f d L Li R Ri hL hLi hR hRi hmatrix
  exact ⟨P, hP, localModelIso Λ (Scheme.Opens.ι (X := Y) (W y))
    (cokernel f) (cokernel d) P c model⟩

private theorem local_model_of_change_smith
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}}
    {R₀ : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R₀] [IsCommMonObj R₀]
    (α : R₀ ⟶ condensedRingObj Λ Y) [IsIso α] [IsMonHom α]
    (e : R₀ ⟶ coeff T Y) [IsIso e] [IsMonHom e]
    (eS : condensedRingObj Λ Y ⟶ coeff T Y) [IsIso eS] [IsMonHom eS]
    (he : inv α ≫ e = eS) {m n : ℕ}
    (f : Mod.finiteFree R₀ m ⟶ Mod.finiteFree R₀ n)
    (hscalar : ∀ D : Matrix (Fin n) (Fin m) T,
      ∃ d : Mod.finiteFree (condensedRingObj Λ Y) m ⟶
        Mod.finiteFree (condensedRingObj Λ Y) n,
        MatrixCalculus.freeMatrix (E := T) eS d = D.map (ContinuousMap.const Y) ∧
        ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
          Mod.IsFinitelyPresented Λ P ∧
          Nonempty (cokernel d ≅ ((upperStarFromPoint Y).mapMod Λ).obj P))
    (W : Y → TopologicalSpace.Opens Y) (hW : ∀ y, y ∈ W y)
    (hs : ∀ y, ∃ (L Li : Matrix (Fin n) (Fin n) C(W y, T))
      (R Ri : Matrix (Fin m) (Fin m) C(W y, T)) (D : Matrix (Fin n) (Fin m) T),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧ ∀ z : W y,
      L.map (fun a ↦ a z) *
        ((ContinuousRingUniverse.freeMatrix (E := T) e f).map
          (fun a ↦ a z.val)) * R.map (fun a ↦ a z) = D) :
    HasFiniteConstantLocalModel Λ Y
      ((Mod.extendScalars α).obj (cokernel f)) := by
  have hmatrix := freeMatrix_comap_eq (inv α) e eS he f
  have hmodel := local_model_of_smith_aux T Λ eS
    ((Mod.finiteFreeIsoComap (inv α) m).inv ≫
    (Mod.comap (inv α)).map f ≫ (Mod.finiteFreeIsoComap (inv α) n).hom) hscalar W hW (by
    rw [hmatrix]
    exact hs)
  exact model_of_iso Λ (changeCoefficientCokernelIso α f) hmodel

set_option backward.isDefEq.respectTransparency.types true in
private theorem cokernel_model_of_local_smith
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] {X Y : Scheme.{u}} (p : Y ⟶ X) {m n : ℕ}
    (f : Mod.finiteFree ((upperStar Ab.{u + 1} p).obj (baseCoeff T X)) m ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} p).obj (baseCoeff T X)) n)
    (W : Y → TopologicalSpace.Opens Y) (hW : ∀ y, y ∈ W y)
    (hs : ∀ y, ∃ (L Li : Matrix (Fin n) (Fin n) C(W y, T))
      (R Ri : Matrix (Fin m) (Fin m) C(W y, T)) (D : Matrix (Fin n) (Fin m) T),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧ ∀ z : W y,
      L.map (fun a ↦ a z) *
        ((ContinuousRingUniverse.freeMatrix (E := T) (pullbackComparison T p) f).map
          (fun a ↦ a z.val)) * R.map (fun a ↦ a z) = D) :
    HasFiniteConstantLocalModel (baseRing T) Y
      ((Mod.extendScalars (condensedPullbackHom (baseRing T) p)).obj (cokernel f)) := by
  have : IsMonHom (pullbackComparison T p) := by
    rw [pullbackComparison_eq, coefficientComparison_eq]
    infer_instance
  have he : inv (condensedPullbackHom (baseRing T) p) ≫
      pullbackComparison T p = comparison Y T := by
    rw [pullbackComparison_eq, coefficientComparison_eq]
    simp only [IsIso.inv_hom_id_assoc]
  apply local_model_of_change_smith T (baseRing T)
    (condensedPullbackHom (baseRing T) p) (pullbackComparison T p) (comparison Y T)
    he f (fun D ↦ ?_) W hW hs
  exact ⟨pointScalarMatrix T Y D, pointScalarMatrix_coordinates T Y D,
    cokernel (scalarMatrix D), ⟨n, m, scalarMatrix D, ⟨Iso.refl _⟩⟩,
    ⟨pointScalarCokernelIso T Y D⟩⟩

set_option backward.isDefEq.respectTransparency.types true in
/-- A single continuous integral presentation with locally constant full scalar cokernel
type admits finite constant local models. There is no Noetherian hypothesis and no
compatibility or descent assumption on a presentation cover.
Source: HRS Example 3.1 and Theorem 6.12(2), local pivot/division argument; parent step 5.

Proof: restrict to an open neighborhood on which the scalar cokernel class is fixed.
The valuation ring is a DVR. Transport continuous integral matrix local Smith reduction
from the original spectral-valuation ring to the WithAbs subring, using their canonical
ring equivalence and equality of valuation and adic topologies. The fixed cokernel class
fixes the complete Smith list, including the free rank and positive torsion exponents.
Thus on a further open cover there are mutually inverse continuous row and column
matrices with L F R a fixed scalar diagonal D. Multiplication by these matrices is an
isomorphism of finite free coefficient sheaves, and the equality holds entrywise as
continuous functions. Hence their cokernels are isomorphic. The scalar diagonal defines
a morphism of finite free modules over the condensed ring on the point; take its
cokernel P, which is finitely presented by construction. Pullback from the point
preserves this cokernel and identifies its presentation with D. Extension of scalars
along the canonical pullback comparison preserves cokernels too. These identifications
give the required local models. Open-immersion covers are pro-etale covers. For zero
rows or columns the diagonal is empty; empty schemes use the empty cover. No choice
of arbitrary module data from an unproved existence assertion is required.
(auxiliary; not a blueprint node) -/
theorem integral_cokernel_hasFiniteConstantLocalModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace (latticeCoefficientIntegers l E)]
    {X Y : Scheme.{u}} (p : Y ⟶ X) {m n : ℕ}
    (f : Mod.finiteFree ((upperStar Ab.{u + 1} p).obj
      (baseCoeff (latticeCoefficientIntegers l E) X)) m ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} p).obj
      (baseCoeff (latticeCoefficientIntegers l E) X)) n)
    (h : IsLocallyConstant (presentationFiberType (latticeCoefficientIntegers l E) p f)) :
    HasFiniteConstantLocalModel
      (baseRing (latticeCoefficientIntegers l E)) Y
      ((Mod.extendScalars (condensedPullbackHom
        (baseRing (latticeCoefficientIntegers l E)) p)).obj
          (cokernel f)) := by
  classical
  -- Spell out the subring: a local subring alias makes coefficient-instance comparison
  -- unfold the valuation and point inverse-image constructions.
  obtain ⟨W, hW, hs⟩ := integral_local_smith l E
    (fun y ↦ (ContinuousRingUniverse.freeMatrix
      (E := latticeCoefficientIntegers l E)
      (pullbackComparison (latticeCoefficientIntegers l E) p) f).map (fun a ↦ a y))
    (fun i j ↦ (ContinuousRingUniverse.freeMatrix
      (E := latticeCoefficientIntegers l E)
      (pullbackComparison (latticeCoefficientIntegers l E) p) f i j).continuous)
    (presentationFiberType_local_cokernel_iso (latticeCoefficientIntegers l E) p f h)
  exact cokernel_model_of_local_smith (latticeCoefficientIntegers l E) p f W hW hs

end AlgebraicGeometry.ProEtale.ContinuousRingUniverse
