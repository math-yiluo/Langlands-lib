import Langlands.AlgebraicGeometry.ProjectiveSpace.EvaluationBracketAtlas
import Langlands.AlgebraicGeometry.Modules.SpecQuasicoherentHoms
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.LinearAlgebra.PoweredMinorFiniteness
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection

/-! # Finitely many evaluation configurations in the fibres of the bracket map -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EvaluationBracket

open Langlands.Scheme.Modules
open Langlands.LinearAlgebra
open Langlands.AlgebraicGeometry.Modules.TensorPowerGauge

variable {X : Scheme.{u}} {E : X.Modules} {Λ : Type v} {Q : Λ → X.Modules}
  {ev : ∀ r, E ⟶ Q r} {M : ℕ} {K : Type u} [Field K]

variable (ev M) in
/-- Evaluation data over a field-valued point, identified with the pullback of the given
evaluation data. -/
structure FieldModel (t : Spec (CommRingCat.of K) ⟶ X) where
  /-- The source module over the field. -/
  E' : (Spec (CommRingCat.of K)).Modules
  /-- The target modules over the field. -/
  Q' : Λ → (Spec (CommRingCat.of K)).Modules
  /-- The evaluations over the field. -/
  ev' : ∀ r, E' ⟶ Q' r
  /-- Comparison of the source with the pullback. -/
  α : (Scheme.Modules.pullback t).obj E ≅ E'
  /-- Comparison of the targets with the pullbacks. -/
  β : ∀ r, (Scheme.Modules.pullback t).obj (Q r) ≅ Q' r
  comm : ∀ r, α.hom ≫ ev' r = (Scheme.Modules.pullback t).map (ev r) ≫ (β r).hom
  qcE : E'.IsQuasicoherent
  qcQ : ∀ r, (Q' r).IsQuasicoherent
  rankE : Module.finrank K (moduleSpecΓFunctor.obj E') = M
  rankQ : ∀ r, Module.finrank K (moduleSpecΓFunctor.obj (Q' r)) = 1

/-- Two field models have equivalent evaluation configurations: one isomorphism of the
sources intertwines every evaluation with the corresponding evaluation, up to isomorphisms
of the targets. -/
def FieldModel.Equivalent {t t' : Spec (CommRingCat.of K) ⟶ X} (F : FieldModel ev M t)
    (F' : FieldModel ev M t') : Prop :=
  ∃ φ : F.E' ≅ F'.E', ∀ r, ∃ ψ : F.Q' r ≅ F'.Q' r, φ.hom ≫ F'.ev' r = F.ev' r ≫ ψ.hom

/-- The evaluation coefficients of a chart frame at a field-valued point of the chart. -/
def Chart.fieldCoef (C : Chart ev M) {t : Spec (CommRingCat.of K) ⟶ X} (ht : ∀ z, t z ∈ C.W)
    (r : Λ) (k : Fin M) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (CoordinateAtlas.pull t ht (C.coef le_rfl r (C.eV le_rfl k)))

lemma Chart.fieldCoef_frame (C : Chart ev M) {t : Spec (CommRingCat.of K) ⟶ X}
    (ht : ∀ z, t z ∈ C.W) (l k : Fin M) :
    C.fieldCoef ht (C.ρ l) k = if l = k then 1 else 0 := by
  rw [Chart.fieldCoef, C.coef_frame]
  split_ifs <;> simp

namespace FieldModel

variable {t : Spec (CommRingCat.of K) ⟶ X} (F : FieldModel ev M t) (C : Chart ev M)
  (ht : ∀ z, t z ∈ C.W)

/-- The image over the field of the `k`-th chart frame vector. -/
def ε (k : Fin M) : Γ(F.E', ⊤) :=
  F.α.hom.app ⊤ (sectionPullbackLE t E (U := ⊤) (fun z _ => ht z) (C.eV le_rfl k))

/-- The image over the field of the chart generator of the `r`-th target. -/
def κ (r : Λ) : Γ(F.Q' r, ⊤) :=
  (F.β r).hom.app ⊤ (sectionPullbackLE t (Q r) (U := ⊤) (fun z _ => ht z) (C.q r))

lemma ev'_ε (r : Λ) (k : Fin M) :
    (F.ev' r).app ⊤ (F.ε C ht k) =
      CoordinateAtlas.pull t ht (C.coef le_rfl r (C.eV le_rfl k)) • F.κ C ht r := by
  unfold ε κ
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, F.comm r,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Langlands.Scheme.Modules.pullback_map_app_sectionPullbackLE, ← C.coef_spec le_rfl r, sectionPullbackLE_smul,
    sectionPullbackLE_restrict, Scheme.Modules.Hom.app_smul]
  rfl

lemma κ_ne_zero (r : Λ) : F.κ C ht r ≠ 0 := by
  have hnt : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  intro h0
  have hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ t ⁻¹ᵁ C.W := fun z _ => ht z
  have h1 : sectionPullbackLE t (Q r) hle (C.q r) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso ((F.β r).hom.app ⊤)).1
    rw [map_zero]
    exact h0
  have hfr := (C.isFrame r).pullbackLocalSection t
  have hb := (hfr hle hle).1
  have h2 : (1 : Γ(Spec (CommRingCat.of K), ⊤)) = 0 := by
    apply hb
    change (1 : Γ(Spec (CommRingCat.of K), ⊤)) • sectionPullbackLE t (Q r) hle (C.q r) =
      (0 : Γ(Spec (CommRingCat.of K), ⊤)) • sectionPullbackLE t (Q r) hle (C.q r)
    rw [h1, smul_zero, smul_zero]
  exact one_ne_zero h2

omit [Field K] in
/-- Global sections of a module on the spectrum of a field, viewed as a vector space. -/
def ofΓ {K : Type u} [Field K] {N : (Spec (CommRingCat.of K)).Modules} (x : Γ(N, ⊤)) :
    moduleSpecΓFunctor.obj N := x

omit [Field K] in
lemma smul_eq_ψK {K : Type u} [Field K] (N : (Spec (CommRingCat.of K)).Modules)
    (c : Γ(Spec (CommRingCat.of K), ⊤)) (x : Γ(N, ⊤)) :
    ofΓ (c • x) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c • ofΓ x := by
  have h := Scheme.Modules.smul_Spec_def (M := N) (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c) x
  refine Eq.trans ?_ h.symm
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ((Scheme.ΓSpecIso (CommRingCat.of K)).hom c)
      = c := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  erw [h1]
  rfl

/-- The `r`-th evaluation on global sections as a linear map over the field. -/
def ℓ (r : Λ) : moduleSpecΓFunctor.obj F.E' →ₗ[K] moduleSpecΓFunctor.obj (F.Q' r) :=
  (moduleSpecΓFunctor.map (F.ev' r)).hom

lemma ℓ_apply (r : Λ) (x : moduleSpecΓFunctor.obj F.E') : F.ℓ r x = (F.ev' r).app ⊤ x := rfl

lemma ℓ_ε (r : Λ) (k : Fin M) :
    F.ℓ r (ofΓ (F.ε C ht k)) = C.fieldCoef ht r k • ofΓ (F.κ C ht r) := by
  exact (congrArg ofΓ (F.ev'_ε C ht r k)).trans (smul_eq_ψK _ _ _)

lemma linearIndependent_ε : LinearIndependent K (fun k => ofΓ (F.ε C ht k)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (F.ℓ (C.ρ l)) hg
  rw [map_sum, map_zero] at h
  simp only [map_smul, ℓ_ε, Chart.fieldCoef_frame, ite_smul, one_smul, zero_smul, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  exact (smul_eq_zero.mp h).resolve_right (F.κ_ne_zero C ht (C.ρ l))

variable [NeZero M]

instance finiteDimensional_E' : FiniteDimensional K (moduleSpecΓFunctor.obj F.E') :=
  Module.finite_of_finrank_pos (by rw [F.rankE]; exact Nat.pos_of_ne_zero (NeZero.ne M))

/-- The images of the chart frame form a basis of the global sections over the field. -/
def εB : Module.Basis (Fin M) K (moduleSpecΓFunctor.obj F.E') :=
  basisOfLinearIndependentOfCardEqFinrank' _ (F.linearIndependent_ε C ht)
    (by rw [Fintype.card_fin, F.rankE])

lemma εB_apply (k : Fin M) : F.εB C ht k = ofΓ (F.ε C ht k) := by
  simp [εB]

end FieldModel

namespace Chart

variable (C : Chart ev M) {t : Spec (CommRingCat.of K) ⟶ X} (ht : ∀ z, t z ∈ C.W)
  {n : ℕ} (τ : ∀ r, (Q r).tensorPow n ≅ 𝟙_ X.Modules) (hn : 0 < n) [IsAlgClosed K]

/-- The value at the field point of the gauge of the chart generator. -/
def gaugeVal (r : Λ) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (CoordinateAtlas.pull t ht (gauge (τ r) (C.q r)))

omit [IsAlgClosed K] in
lemma gaugeVal_ne_zero (r : Λ) : C.gaugeVal ht τ r ≠ 0 :=
  (((isUnit_gauge (τ r) (C.isFrame r)).map (CoordinateAtlas.pull t ht)).map
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero

/-- An `n`-th root of the gauge value. -/
def root (r : Λ) : K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (C.gaugeVal ht τ r) hn)

lemma root_pow (r : Λ) : C.root ht τ hn r ^ n = C.gaugeVal ht τ r :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (C.gaugeVal ht τ r) hn)

lemma root_ne_zero (r : Λ) : C.root ht τ hn r ≠ 0 := by
  intro h
  have := C.root_pow ht τ hn r
  rw [h, zero_pow hn.ne'] at this
  exact C.gaugeVal_ne_zero ht τ r this.symm

/-- The normalized evaluation matrix at the field point. -/
def normA (r : Λ) (k : Fin M) : K := C.fieldCoef ht r k * C.root ht τ hn r

lemma poweredMinor_normA (σ : Fin M → Λ) :
    PoweredMinors.poweredMinor n (C.normA ht τ hn) σ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (CoordinateAtlas.pull t ht (C.coord τ σ)) := by
  let φ : Γ(X, C.W) →+* K :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).comp (CoordinateAtlas.pull t ht)
  have hpiv : PoweredMinors.pivot (C.normA ht τ hn) σ =
      Matrix.diagonal (fun l => C.root ht τ hn (σ l)) * φ.mapMatrix (C.mat le_rfl σ) := by
    ext l k
    rw [Matrix.diagonal_mul]
    simp only [PoweredMinors.pivot, normA, RingHom.mapMatrix_apply, Matrix.map_apply, mat,
      Matrix.of_apply, fieldCoef, φ, RingHom.comp_apply]
    exact mul_comm _ _
  change PoweredMinors.poweredMinor n (C.normA ht τ hn) σ = φ (C.coord τ σ)
  rw [PoweredMinors.poweredMinor, hpiv, Matrix.det_mul, Matrix.det_diagonal, coord, map_mul,
    map_pow, map_prod, RingHom.map_det, mul_pow, ← Finset.prod_pow]
  simp only [C.root_pow ht τ hn]
  rw [mul_comm]
  rfl

end Chart

namespace FieldModel

variable {t : Spec (CommRingCat.of K) ⟶ X} (F : FieldModel ev M t) (C : Chart ev M)
  (ht : ∀ z, t z ∈ C.W) {n : ℕ} (τ : ∀ r, (Q r).tensorPow n ≅ 𝟙_ X.Modules) (hn : 0 < n)
  [IsAlgClosed K]

/-- The normalized generator of the `r`-th target at the field point. -/
def normκ (r : Λ) : moduleSpecΓFunctor.obj (F.Q' r) :=
  (C.root ht τ hn r)⁻¹ • ofΓ (F.κ C ht r)

lemma normκ_ne_zero (r : Λ) : F.normκ C ht τ hn r ≠ 0 :=
  smul_ne_zero (inv_ne_zero (C.root_ne_zero ht τ hn r)) (F.κ_ne_zero C ht r)

variable [NeZero M]

lemma ℓ_εB (r : Λ) (k : Fin M) :
    F.ℓ r (F.εB C ht k) = C.normA ht τ hn r k • F.normκ C ht τ hn r := by
  rw [εB_apply, ℓ_ε, normκ, smul_smul, Chart.normA, mul_assoc,
    mul_inv_cancel₀ (C.root_ne_zero ht τ hn r), mul_one]

end FieldModel

/-- An isomorphism of quasi-coherent modules on the spectrum of a field with prescribed linear
equivalence of global sections. -/
def specIso {N N' : (Spec (CommRingCat.of K)).Modules} [N.IsQuasicoherent]
    [N'.IsQuasicoherent] (Φ : moduleSpecΓFunctor.obj N ≃ₗ[K] moduleSpecΓFunctor.obj N') :
    N ≅ N' :=
  Modules.SpecQuasicoherentHoms.isoOfIso (LinearEquiv.toModuleIso (R := CommRingCat.of K) Φ)

lemma specIso_hom_app {N N' : (Spec (CommRingCat.of K)).Modules} [N.IsQuasicoherent]
    [N'.IsQuasicoherent] (Φ : moduleSpecΓFunctor.obj N ≃ₗ[K] moduleSpecΓFunctor.obj N')
    (x : Γ(N, ⊤)) : (specIso Φ).hom.app ⊤ x = Φ x :=
  (Modules.SpecQuasicoherentHoms.isoOfIso_hom_app _ x).trans rfl

/-- A linear equivalence of one-dimensional spaces sending one nonzero vector to another. -/
def lineEquiv {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (hV : Module.finrank K V = 1) (hV' : Module.finrank K V' = 1) (x : V) (x' : V')
    (hx : x ≠ 0) (hx' : x' ≠ 0) : V ≃ₗ[K] V' :=
  haveI : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  haveI : FiniteDimensional K V' := Module.finite_of_finrank_eq_succ hV'
  (basisOfLinearIndependentOfCardEqFinrank' (fun _ : Fin 1 => x)
      (linearIndependent_unique_iff.mpr hx) (by rw [Fintype.card_fin, hV])).equiv
    (basisOfLinearIndependentOfCardEqFinrank' (fun _ : Fin 1 => x')
      (linearIndependent_unique_iff.mpr hx') (by rw [Fintype.card_fin, hV'])) (Equiv.refl _)

lemma lineEquiv_apply {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (hV : Module.finrank K V = 1) (hV' : Module.finrank K V' = 1) (x : V) (x' : V')
    (hx : x ≠ 0) (hx' : x' ≠ 0) : lineEquiv hV hV' x x' hx hx' x = x' := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have : FiniteDimensional K V' := Module.finite_of_finrank_eq_succ hV'
  have := Module.Basis.equiv_apply (b := basisOfLinearIndependentOfCardEqFinrank'
      (K := K) (fun _ : Fin 1 => x) (linearIndependent_unique_iff.mpr hx)
      (by rw [Fintype.card_fin, hV]))
    (0 : Fin 1) (basisOfLinearIndependentOfCardEqFinrank' (fun _ : Fin 1 => x')
      (linearIndependent_unique_iff.mpr hx') (by rw [Fintype.card_fin, hV'])) (Equiv.refl _)
  simpa only [lineEquiv, coe_basisOfLinearIndependentOfCardEqFinrank'] using this

/-- Evaluation data over two field points are equivalent once their normalized evaluation
matrices in bases of the sources differ by one invertible matrix acting on the right. -/
theorem FieldModel.equivalent_of_vecMul {t t' : Spec (CommRingCat.of K) ⟶ X}
    (F : FieldModel ev M t) (F' : FieldModel ev M t')
    (b : Module.Basis (Fin M) K (moduleSpecΓFunctor.obj F.E'))
    (b' : Module.Basis (Fin M) K (moduleSpecΓFunctor.obj F'.E'))
    (κ : ∀ r, moduleSpecΓFunctor.obj (F.Q' r)) (κ' : ∀ r, moduleSpecΓFunctor.obj (F'.Q' r))
    (hκ : ∀ r, κ r ≠ 0) (hκ' : ∀ r, κ' r ≠ 0) (A A' : Λ → Fin M → K)
    (hA : ∀ r k, F.ℓ r (b k) = A r k • κ r) (hA' : ∀ r k, F'.ℓ r (b' k) = A' r k • κ' r)
    (G : (Matrix (Fin M) (Fin M) K)ˣ) (hG : ∀ r, A r ᵥ* (G : Matrix (Fin M) (Fin M) K) = A' r) :
    F.Equivalent F' := by
  classical
  have := F.qcE
  have := F'.qcE
  let Φ : moduleSpecΓFunctor.obj F.E' ≃ₗ[K] moduleSpecΓFunctor.obj F'.E' :=
    LinearEquiv.ofLinearMap (Matrix.toLin b b' (↑G⁻¹ : Matrix (Fin M) (Fin M) K))
      (Matrix.toLin b' b (G : Matrix (Fin M) (Fin M) K))
      (by rw [← Matrix.toLin_mul, Units.inv_mul, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul, Units.mul_inv, Matrix.toLin_one])
  refine ⟨specIso Φ, fun r => ?_⟩
  have := F.qcQ r
  have := F'.qcQ r
  let Ψ := lineEquiv (F.rankQ r) (F'.rankQ r) (κ r) (κ' r) (hκ r) (hκ' r)
  have hΨ : Ψ (κ r) = κ' r := lineEquiv_apply _ _ _ _ _ _
  refine ⟨specIso Ψ, ?_⟩
  have hk : ∀ k, ∑ j, (↑G⁻¹ : Matrix (Fin M) (Fin M) K) j k * A' r j = A r k := by
    intro k
    have h := congrFun (show A' r ᵥ* (↑G⁻¹ : Matrix (Fin M) (Fin M) K) = A r by
      rw [← hG r, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]) k
    simpa [Matrix.vecMul, dotProduct, mul_comm] using h
  have key : ∀ x, F'.ℓ r (Φ x) = Ψ (F.ℓ r x) := by
    intro x
    have hlin : (F'.ℓ r).comp Φ.toLinearMap = Ψ.toLinearMap.comp (F.ℓ r) := by
      apply b.ext
      intro k
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
      have hΦ : Φ (b k) = ∑ j, (↑G⁻¹ : Matrix (Fin M) (Fin M) K) j k • b' j :=
        Matrix.toLin_self b b' _ k
      rw [hΦ, map_sum]
      simp only [map_smul, hA', smul_smul]
      rw [← Finset.sum_smul, hk, hA, map_smul, hΨ]
    exact LinearMap.congr_fun hlin x
  apply Modules.SpecQuasicoherentHoms.hom_ext
  intro x
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, specIso_hom_app, specIso_hom_app]
  exact key x

/-- **Finiteness in the fibres of the bracket map.** Glue the powered bracket coordinates of
covering charts into a morphism to projective space. Over an algebraically closed field, the
field-valued points with a given image have only finitely many classes of evaluation
configurations. -/
theorem exists_finset_equivalent [Finite Λ] [NeZero M] [IsAlgClosed K] {R : Type u}
    [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {ι : Type*} (chart : ι → Chart ev M)
    (hcov : ∀ x, ∃ i, x ∈ (chart i).W) {n : ℕ} (hn : 0 < n)
    (τ : ∀ r, (Q r).tensorPow n ≅ 𝟙_ X.Modules) {m : ℕ} (eqv : Fin (m + 1) ≃ (Fin M → Λ))
    (model : ∀ t : Spec (CommRingCat.of K) ⟶ X, FieldModel ev M t)
    (y : Spec (CommRingCat.of K) ⟶ ProjectiveSpace R m) :
    ∃ s : Finset (Spec (CommRingCat.of K) ⟶ X), ∀ t,
      t ≫ CoordinateAtlas.atlasMap p (isAtlas chart hcov τ eqv) = y →
        ∃ t' ∈ s, (model t).Equivalent (model t') := by
  classical
  set hc := isAtlas chart hcov τ eqv
  have hpt : ∀ t : Spec (CommRingCat.of K) ⟶ X, ∃ i, ∀ z, t z ∈ (chart i).W := by
    intro t
    obtain ⟨i, hi⟩ := hcov (t (IsLocalRing.closedPoint K))
    exact ⟨i, fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint K)]⟩
  choose ix hix using hpt
  by_cases hne : ∃ t0, t0 ≫ CoordinateAtlas.atlasMap p hc = y
  swap
  · exact ⟨∅, fun t ht => (hne ⟨t, ht⟩).elim⟩
  obtain ⟨t0, ht0⟩ := hne
  let A : {t // t ≫ CoordinateAtlas.atlasMap p hc = y} → Λ → Fin M → K :=
    fun t => (chart (ix t.1)).normA (hix t.1) τ hn
  obtain ⟨a0, ha0⟩ := CoordinateAtlas.exists_isUnit_pull hc t0 (hix t0)
  let c : (Fin M → Λ) → K := fun σ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (CoordinateAtlas.pull t0 (hix t0) ((chart (ix t0)).coord τ σ))
  have hcp : c (eqv a0) ≠ 0 := (ha0.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero
  have hA : ∀ tt, ∃ a : K, a ≠ 0 ∧ ∀ σ, PoweredMinors.poweredMinor n (A tt) σ = a * c σ := by
    intro tt
    obtain ⟨α, hα, hαeq⟩ := CoordinateAtlas.exists_unit_of_comp_eq hc (hix t0) (hix tt.1)
      (ht0.trans tt.2.symm)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom α,
      (hα.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero, fun σ => ?_⟩
    have h := hαeq (eqv.symm σ)
    simp only [Equiv.apply_symm_apply] at h
    rw [Chart.poweredMinor_normA, h, map_mul]
  obtain ⟨Rs, hRs⟩ :=
    PoweredMinors.exists_finset_of_projectively_equal_poweredMinors A n hn (eqv a0) c hcp hA
  refine ⟨Rs.map (Function.Embedding.subtype _), fun t ht => ?_⟩
  obtain ⟨t', ht'R, G, hG⟩ := hRs ⟨t, ht⟩
  refine ⟨t'.1, Finset.mem_map_of_mem _ ht'R, ?_⟩
  exact FieldModel.equivalent_of_vecMul (model t) (model t'.1)
    ((model t).εB (chart (ix t)) (hix t)) ((model t'.1).εB (chart (ix t'.1)) (hix t'.1))
    ((model t).normκ (chart (ix t)) (hix t) τ hn)
    ((model t'.1).normκ (chart (ix t'.1)) (hix t'.1) τ hn)
    ((model t).normκ_ne_zero (chart (ix t)) (hix t) τ hn)
    ((model t'.1).normκ_ne_zero (chart (ix t'.1)) (hix t'.1) τ hn)
    (A ⟨t, ht⟩) (A t') ((model t).ℓ_εB (chart (ix t)) (hix t) τ hn)
    ((model t'.1).ℓ_εB (chart (ix t'.1)) (hix t'.1) τ hn) G hG

end Langlands.AlgebraicGeometry.EvaluationBracket
