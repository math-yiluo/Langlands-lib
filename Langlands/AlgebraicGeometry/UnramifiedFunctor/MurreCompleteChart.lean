import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteFibre

/-! # The closed-fibre charts of Step 2a of Murre's induction

For Step 2a of Murre's induction (Bourbaki exp. 294): condition (F3) in terms of `ovR`, the
complete local rings `B_y = lim_k 𝒪_{Y_k, y}` and their elements of `F`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Adic

variable (A : Type u) [CommRing A] [Algebra R A]

lemma map_comp_op_apply {X Y Z : Over (Spec R)} (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj (op Z)) :
    F.map (a ≫ b).op x = F.map a.op (F.map b.op x) := by
  rw [op_comp, Functor.map_comp_apply]

lemma algebraOverBase_eq (I : Ideal A) :
    algebraOverBase (ovR R A).hom (A ⧸ I) =
      (towerIso A (A ⧸ I)).hom ≫ homR (Ideal.Quotient.mkₐ R I) := by
  ext1
  simp only [Over.comp_left, towerIso_hom_left, homR_left]
  rfl

lemma algHomOver_towerIso {I J : Ideal A} (h : I ≤ J) :
    algHomOver (ovR R A).hom (Ideal.Quotient.factorₐ A h) ≫ (towerIso A (A ⧸ I)).hom =
      (towerIso A (A ⧸ J)).hom ≫ homR (Ideal.Quotient.factorₐ R h) := by
  ext1
  simp only [Over.comp_left, towerIso_hom_left, homR_left]
  rfl

lemma map_towerIso_injective (T : Type u) [CommRing T] [Algebra A T] [Algebra R T]
    [IsScalarTower R A T] :
    Function.Injective (F.map (towerIso A T).hom.op) := by
  intro x y h
  have := congrArg (F.map (towerIso A T).inv.op) h
  rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
    Iso.inv_hom_id, op_id, Functor.map_id_apply, Functor.map_id_apply] at this

omit [Algebra R A] in
/-- Every morphism `ovR R T' ⟶ ovR R T` is `homR` of an `R`-algebra map. -/
lemma exists_homR {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (h : ovR R T' ⟶ ovR R T) : ∃ ψ : T →ₐ[R] T', h = homR ψ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective h.left
  have hc : CommRingCat.ofHom (algebraMap R T) ≫ φ = CommRingCat.ofHom (algebraMap R T') := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w h
  refine ⟨{ φ.hom with commutes' := fun r ↦ congrArg (fun f ↦ f.hom r) hc }, ?_⟩
  ext1
  rw [homR_left, ← hφ]
  rfl

variable [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

/-- (F3), uniqueness, for `ovR`: elements over a complete local ring are determined by their
restrictions to the quotients by the powers of the maximal ideal. -/
lemma adic_unique (hF : AdicLimits F) {x y : F.obj (op (ovR R A))}
    (h : ∀ n, F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal A ^ n))).op x =
      F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal A ^ n))).op y) : x = y := by
  refine (hF A (ovR R A).hom).1 x y fun n ↦ ?_
  rw [algebraOverBase_eq, map_comp_op_apply, map_comp_op_apply, h n]

/-- (F3), existence, for `ovR`: a compatible family of elements over the quotients by the
powers of the maximal ideal comes from an element over the complete local ring. -/
lemma adic_exists (hF : AdicLimits F)
    (s : ∀ n, F.obj (op (ovR R (A ⧸ maximalIdeal A ^ n))))
    (hs : ∀ n, F.map (homR (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal A) n.le_succ))).op (s (n + 1)) = s n) :
    ∃ x : F.obj (op (ovR R A)), ∀ n,
      F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal A ^ n))).op x = s n := by
  obtain ⟨x, hx⟩ := (hF A (ovR R A).hom).2
    (fun n ↦ F.map (towerIso A (A ⧸ maximalIdeal A ^ n)).hom.op (s n)) (fun n ↦ by
      dsimp only
      rw [← map_comp_op_apply, algHomOver_towerIso, map_comp_op_apply, hs n])
  refine ⟨x, fun n ↦ map_towerIso_injective A _ ?_⟩
  rw [← hx n, algebraOverBase_eq, map_comp_op_apply]

end Adic

section Limit

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {Y : ℕ → Scheme.{u}} {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
  (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))
  [hfu : ∀ k, FormallyUnramified (q k)] [hlft : ∀ k, LocallyOfFiniteType (q k)]

/-- The chart ring `B_y = lim_k 𝒪_{Y k, y}`. -/
abbrev ChartRing (y : Y 0) : Type u := limitAlg (Bk e y) (transition e y)

/-- The projection `B_y → 𝒪_{Y k, y}`. -/
abbrev chartProj (y : Y 0) (k : ℕ) : ChartRing e y →ₐ[R] Bk e y k := limitProj _ _ k

include hfu hlft in
lemma chart_spec (y : Y 0) :
    Module.Finite R (ChartRing e y) ∧ (∀ n, Function.Surjective (chartProj e y n)) ∧
      ∀ n, LinearMap.ker (chartProj e y n).toLinearMap =
        (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R (ChartRing e y)) :=
  limit_spec _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

instance (y : Y 0) : IsLocalRing (ChartRing e y) :=
  limit_isLocalRing _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y) (B0_isField e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

instance (y : Y 0) : IsNoetherianRing (ChartRing e y) :=
  limit_isNoetherianRing _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

instance (y : Y 0) : Module.Finite R (ChartRing e y) := (chart_spec e y).1

include hfu hlft in
lemma chart_maximalIdeal (y : Y 0) :
    maximalIdeal (ChartRing e y) = (maximalIdeal R).map (algebraMap R (ChartRing e y)) :=
  limit_maximalIdeal _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y) (B0_isField e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

instance (y : Y 0) : Algebra.FormallyUnramified R (ChartRing e y) := by
  have := Bk_formallyUnramified e (fun k ↦ hfu k) y 0
  exact limit_formallyUnramified _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y) (B0_isField e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

instance (y : Y 0) : IsAdicComplete (maximalIdeal (ChartRing e y)) (ChartRing e y) := by
  rw [chart_maximalIdeal e y]
  exact limit_isAdicComplete _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y)

include hfu hlft in
lemma chartProj_ker (y : Y 0) (n : ℕ) :
    RingHom.ker (chartProj e y n) = maximalIdeal (ChartRing e y) ^ (n + 1) := by
  rw [chart_maximalIdeal e y]
  exact limit_ker_eq _ _ (transition_surjective e y) (transition_ker_linear e y)
    (B0_finite e (fun k ↦ hfu k) (fun k ↦ hlft k) y) n

/-- `𝒪_{Y n, y} ≅ B_y / m^(n+1)`. -/
def qIso (y : Y 0) (n : ℕ) :
    Bk e y n ≃ₐ[R] ChartRing e y ⧸ maximalIdeal (ChartRing e y) ^ (n + 1) :=
  (Ideal.quotientKerAlgEquivOfSurjective ((chart_spec e y).2.1 n)).symm.trans
    (Ideal.quotientEquivAlgOfEq R (chartProj_ker e y n))

lemma qIso_chartProj (y : Y 0) (n : ℕ) (x : ChartRing e y) :
    qIso e y n (chartProj e y n x) = Ideal.Quotient.mk _ x := by
  rw [qIso, AlgEquiv.trans_apply]
  have : (Ideal.quotientKerAlgEquivOfSurjective ((chart_spec e y).2.1 n)).symm
      (chartProj e y n x) = Ideal.Quotient.mk _ x := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

/-- `ξ_n` transported to `B_y / m^(n+1)`. -/
def sAux (y : Y 0) (n : ℕ) :
    F.obj (op (ovR R (ChartRing e y ⧸ maximalIdeal (ChartRing e y) ^ (n + 1)))) :=
  F.map (homR (qIso e y n).toAlgHom).op (ξk e y n)

/-- The compatible family of `(F3)`. -/
def sFam (y : Y 0) : ∀ n, F.obj (op (ovR R (ChartRing e y ⧸ maximalIdeal (ChartRing e y) ^ n)))
  | 0 => F.map (homR (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal (ChartRing e y)) (Nat.le_succ 0)))).op
        (sAux e y 0)
  | n + 1 => sAux e y n

lemma sFam_succ (y : Y 0) (n : ℕ) : sFam e y (n + 1) = sAux e y n := rfl

lemma factor_qIso (y : Y 0) (n : ℕ) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := maximalIdeal (ChartRing e y))
      (Nat.le_succ (n + 1)))).comp (qIso e y (n + 1)).toAlgHom =
        (qIso e y n).toAlgHom.comp (transition e y n) := by
  ext b
  obtain ⟨x, rfl⟩ := (chart_spec e y).2.1 (n + 1) b
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [qIso_chartProj, show transition e y n (chartProj e y (n + 1) x) = chartProj e y n x from
    limitProj_compat _ _ n x, qIso_chartProj]
  rfl

lemma sFam_compat (y : Y 0) (n : ℕ) :
    F.map (homR (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal (ChartRing e y)) n.le_succ))).op
        (sFam e y (n + 1)) = sFam e y n := by
  cases n with
  | zero => rfl
  | succ n =>
    show F.map (homR (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal (ChartRing e y)) (Nat.le_succ (n + 1))))).op
        (sAux e y (n + 1)) = sAux e y n
    rw [sAux, sAux, map_homR_map_homR, factor_qIso, ← map_homR_map_homR, map_transition]

/-- The element `ξ_y ∈ F(Spec B_y)`, by (F3). -/
def chartElem (hF3 : AdicLimits F) (y : Y 0) : F.obj (op (ovR R (ChartRing e y))) :=
  (adic_exists (ChartRing e y) hF3 (sFam e y) (sFam_compat e y)).choose

lemma map_mk_chartElem (hF3 : AdicLimits F) (y : Y 0) (n : ℕ) :
    F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal (ChartRing e y) ^ n))).op
      (chartElem e hF3 y) = sFam e y n :=
  (adic_exists (ChartRing e y) hF3 (sFam e y) (sFam_compat e y)).choose_spec n

/-- The restriction of `ξ_y` to `𝒪_{Y n, y}` is `ξ_n`. -/
lemma map_chartProj_chartElem (hF3 : AdicLimits F) (y : Y 0) (n : ℕ) :
    F.map (homR (chartProj e y n)).op (chartElem e hF3 y) = ξk e y n := by
  have h : chartProj e y n = (qIso e y n).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ R (maximalIdeal (ChartRing e y) ^ (n + 1))) := by
    ext x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk]
    rw [← qIso_chartProj, AlgEquiv.symm_apply_apply]
  have h2 : (qIso e y n).symm.toAlgHom.comp (qIso e y n).toAlgHom = AlgHom.id R (Bk e y n) := by
    ext x; simp
  have e1 := map_homR_map_homR (F := F) (T := ChartRing e y)
    (T' := ChartRing e y ⧸ maximalIdeal (ChartRing e y) ^ (n + 1)) (T'' := Bk e y n)
    (Ideal.Quotient.mkₐ R (maximalIdeal (ChartRing e y) ^ (n + 1)))
    (qIso e y n).symm.toAlgHom (chartElem e hF3 y)
  rw [map_mk_chartElem, sFam_succ, sAux, map_homR_map_homR, h2, ArtinianBase.homR_id, op_id, F.map_id, ← h]
    at e1
  exact e1.symm

/-- `R/m^(k+1) → A` for an `R`-algebra `A` killing `m^(k+1)`. -/
def quotLift {A : Type u} [CommRing A] [Algebra R A] (k : ℕ)
    (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0) :
    CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)) ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R A) hA)

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
lemma quotLift_fac {A : Type u} [CommRing A] [Algebra R A] (k : ℕ)
    (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0) :
    Spec.map (quotLift k hA) ≫ maximalIdealPowQuotientMap R k = (ovR R A).hom := by
  show Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = _
  rw [← Spec.map_comp]
  congr 1

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
/-- If `A` is local and kills `m^(k+1)`, its residue field kills `m`. -/
lemma residue_kills {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A] (k : ℕ)
    (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0) :
    ∀ r ∈ maximalIdeal R ^ (0 + 1), algebraMap R (ResidueField A) r = 0 := by
  intro r hr
  rw [zero_add, pow_one] at hr
  rw [IsScalarTower.algebraMap_apply R A (ResidueField A), ResidueField.algebraMap_eq,
    residue_eq_zero_iff]
  have h0 := hA _ (Ideal.pow_mem_pow hr (k + 1))
  rw [map_pow] at h0
  exact (mem_maximalIdeal _).2 fun hu ↦ not_isUnit_zero (h0 ▸ hu.pow (k + 1))

include hfu hlft in
/-- An `R`-algebra map from `B_y` to a field killing `m` factors through `B_y → 𝒪_{Y 0, y}`. -/
lemma exists_factor_chartProj_zero (y : Y 0) {K : Type u} [Field K] [Algebra R K]
    (hK : ∀ r ∈ maximalIdeal R ^ (0 + 1), algebraMap R K r = 0) (σ : ChartRing e y →ₐ[R] K) :
    ∃ σ₀ : Bk e y 0 →ₐ[R] K, σ = σ₀.comp (chartProj e y 0) := by
  have hσ : ∀ b ∈ maximalIdeal (ChartRing e y) ^ (0 + 1), σ b = 0 := by
    intro b hb
    rw [zero_add, pow_one, chart_maximalIdeal e y] at hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨r, hr, rfl⟩
      rw [AlgHom.commutes]
      exact hK r (by rw [zero_add, pow_one]; exact hr)
    · exact map_zero σ
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  refine ⟨(Ideal.Quotient.liftₐ _ σ hσ).comp (qIso e y 0).toAlgHom, ?_⟩
  ext b
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [qIso_chartProj]
  rfl

include hfu hlft in
/-- If the restriction of `η ∈ F(Spec A)` to the residue field comes from `ξ_y`, the classifying
morphism of `η` at level `k` sends the closed point to the point of `Y k` given by `y`. -/
lemma cls_closedPoint_of_residue (hF3 : AdicLimits F) (y : Y 0) {A : Type u} [CommRing A]
    [IsLocalRing A] [Algebra R A] (k : ℕ)
    (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0) (η : F.obj (op (ovR R A)))
    (σ : ChartRing e y →ₐ[R] ResidueField A)
    (hσ : F.map (homR σ).op (chartElem e hF3 y) =
      F.map (homR (IsScalarTower.toAlgHom R A (ResidueField A))).op η) :
    cls _ (e k) (ovR R A) (Spec.map (quotLift k hA)) (quotLift_fac k hA) η (closedPoint A) =
      pt e y k := by
  set res := IsScalarTower.toAlgHom R A (ResidueField A)
  have hκ := residue_kills k hA
  obtain ⟨σ₀, rfl⟩ := exists_factor_chartProj_zero e y hκ σ
  have hσ₀ : F.map (homR σ₀).op (ξk e y 0) = F.map (homR res).op η := by
    rw [← hσ, ← map_homR_map_homR, map_chartProj_chartElem]
  have h0 : cls _ (e 0) (ovR R (ResidueField A)) (Spec.map (quotLift 0 hκ)) (quotLift_fac 0 hκ)
      (F.map (homR σ₀).op (ξk e y 0)) =
        Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫
          levelJ (maximalIdealPowQuotientMap R 0) (q 0) (pt e y 0) := by
    rw [ξk, map_levelElem _ (q 0) (pt e y 0) (e 0) (Spec.map (quotLift 0 hκ))
      (quotLift_fac 0 hκ) σ₀]
    exact cls_mkElem _ _ _ _ _ _ _
  have h1 := cls_towerMap e (Nat.zero_le k) (T := ovR R (ResidueField A))
    (Spec.map (quotLift 0 hκ)) (quotLift_fac 0 hκ) (F.map (homR σ₀).op (ξk e y 0))
  rw [h0, hσ₀] at h1
  have heq : Spec.map (quotLift 0 hκ) ≫ levelMap (R := R) (Nat.zero_le k) =
      (homR res).left ≫ Spec.map (quotLift k hA) := by
    rw [← cancel_mono (maximalIdealPowQuotientMap R k), Category.assoc, levelMap_comp,
      quotLift_fac, Category.assoc, quotLift_fac]
    exact (Over.w (homR res)).symm
  have hres : ((homR res).left ≫ Spec.map (quotLift k hA)) ≫ maximalIdealPowQuotientMap R k =
      (ovR R (ResidueField A)).hom := by
    rw [Category.assoc, quotLift_fac]; exact Over.w (homR res)
  have h2 := cls_map _ (e k) (homR res) ((homR res).left ≫ Spec.map (quotLift k hA))
    (Spec.map (quotLift k hA)) hres (quotLift_fac k hA) rfl η
  rw [← cls_congr _ (e k) heq (change_fac _ _ (levelMap_comp (R := R) (Nat.zero_le k))
    (T := ovR R (ResidueField A)) (Spec.map (quotLift 0 hκ)) (quotLift_fac 0 hκ)) hres] at h2
  have h3 := congrArg (fun f ↦ f (closedPoint (ResidueField A))) (h1.symm.trans h2)
  have : IsLocalHom (CommRingCat.ofHom res.toRingHom).hom :=
    inferInstanceAs (IsLocalHom (residue A))
  have hf := B0_isField e (fun k ↦ hfu k) (fun k ↦ hlft k) y
  let := hf.toField
  have hpt : (Spec.map (CommRingCat.ofHom σ₀.toRingHom)) (closedPoint (ResidueField A)) =
      closedPoint (Bk e y 0) := Subsingleton.elim (α := PrimeSpectrum (Bk e y 0)) _ _
  change towerMap e (Nat.zero_le k) ((Y 0).fromSpecStalk (pt e y 0)
      ((Spec.map (CommRingCat.ofHom σ₀.toRingHom)) (closedPoint (ResidueField A)))) =
    cls _ (e k) (ovR R A) (Spec.map (quotLift k hA)) (quotLift_fac k hA) η
      ((Spec.map (CommRingCat.ofHom res.toRingHom)) (closedPoint (ResidueField A))) at h3
  rw [hpt, Spec_closedPoint] at h3
  have h4 : (Y 0).fromSpecStalk (pt e y 0) (closedPoint (Bk e y 0)) = pt e y 0 :=
    Scheme.fromSpecStalk_closedPoint
  rw [h4, towerMap_pt] at h3
  exact h3.symm

include hfu hlft in
/-- Pro-representability at the closed point: an element of `F` over a local `R`-algebra
killing a power of `m`, whose restriction to the residue field comes from `ξ_y`, comes from
`ξ_y`. -/
lemma chart_lift (hF3 : AdicLimits F) (y : Y 0) {A : Type u} [CommRing A] [IsLocalRing A]
    [Algebra R A] (k : ℕ) (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0)
    (η : F.obj (op (ovR R A))) (σ : ChartRing e y →ₐ[R] ResidueField A)
    (hσ : F.map (homR σ).op (chartElem e hF3 y) =
      F.map (homR (IsScalarTower.toAlgHom R A (ResidueField A))).op η) :
    ∃ ψ : ChartRing e y →ₐ[R] A, F.map (homR ψ).op (chartElem e hF3 y) = η := by
  obtain ⟨ψ', hψ'⟩ := exists_levelElem _ (q k) (pt e y k) (e k) (Spec.map (quotLift k hA))
    (quotLift_fac k hA) η (Specializes.of_eq (cls_closedPoint_of_residue e hF3 y k hA η σ hσ))
  exact ⟨ψ'.comp (chartProj e y k), by
    rw [← map_homR_map_homR, map_chartProj_chartElem]; exact hψ'⟩

include hfu hlft in
/-- An `R`-algebra map from `B_y` killing `m^(k+1)` factors through `B_y → 𝒪_{Y k, y}`. -/
lemma exists_factor_chartProj (y : Y 0) {A : Type u} [CommRing A] [Algebra R A] (k : ℕ)
    (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0) (ψ : ChartRing e y →ₐ[R] A) :
    ∃ σ : Bk e y k →ₐ[R] A, ψ = σ.comp (chartProj e y k) := by
  have hψ : ∀ b ∈ maximalIdeal (ChartRing e y) ^ (k + 1), ψ b = 0 := by
    intro b hb
    rw [chart_maximalIdeal e y, ← Ideal.map_pow] at hb
    have : ((maximalIdeal R) ^ (k + 1)).map (algebraMap R (ChartRing e y)) ≤
        RingHom.ker ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      exact hA r hr
    exact this hb
  refine ⟨(Ideal.Quotient.liftₐ _ ψ hψ).comp (qIso e y k).toAlgHom, ?_⟩
  ext b
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [qIso_chartProj]
  rfl

include hfu hlft in
/-- Uniqueness at the closed point: two `R`-algebra maps from `B_y` to an `R`-algebra killing
`m^(k+1)` that restrict `ξ_y` to the same element are equal. -/
lemma chart_inj_level (hF3 : AdicLimits F) (y : Y 0) {A : Type u} [CommRing A] [Algebra R A]
    (k : ℕ) (hA : ∀ r ∈ maximalIdeal R ^ (k + 1), algebraMap R A r = 0)
    {ψ₁ ψ₂ : ChartRing e y →ₐ[R] A}
    (h : F.map (homR ψ₁).op (chartElem e hF3 y) = F.map (homR ψ₂).op (chartElem e hF3 y)) :
    ψ₁ = ψ₂ := by
  obtain ⟨σ₁, rfl⟩ := exists_factor_chartProj e y k hA ψ₁
  obtain ⟨σ₂, rfl⟩ := exists_factor_chartProj e y k hA ψ₂
  rw [← map_homR_map_homR, ← map_homR_map_homR, map_chartProj_chartElem] at h
  rw [levelElem_injective _ (q k) (pt e y k) (e k) (Spec.map (quotLift k hA)) (quotLift_fac k hA) h]

include hfu hlft in
/-- The closed-fibre charts cover the field-valued points of `F` over the closed point. -/
lemma chart_cover (hF3 : AdicLimits F) {K : Type u} [Field K] [Algebra R K]
    (hK : ∀ r ∈ maximalIdeal R ^ (0 + 1), algebraMap R K r = 0) (η : F.obj (op (ovR R K))) :
    ∃ (y : Y 0) (ψ : ChartRing e y →ₐ[R] K), F.map (homR ψ).op (chartElem e hF3 y) = η := by
  set y := cls _ (e 0) (ovR R K) (Spec.map (quotLift 0 hK)) (quotLift_fac 0 hK) η (closedPoint K)
  obtain ⟨σ₀, hσ₀⟩ := exists_levelElem _ (q 0) (pt e y 0) (e 0) (Spec.map (quotLift 0 hK))
    (quotLift_fac 0 hK) η (Specializes.of_eq (pt_zero e y).symm)
  exact ⟨y, σ₀.comp (chartProj e y 0), by
    rw [← map_homR_map_homR, map_chartProj_chartElem]; exact hσ₀⟩

include hfu hlft in
/-- `ξ_y` is infinitesimally étale at the closed point of `Spec B_y`. -/
theorem chart_infinitesimallyEtaleAt_closedPoint (hF3 : AdicLimits F) (y : Y 0) :
    InfinitesimallyEtaleAt F (chartElem e hF3 y) (closedPoint (ChartRing e y)) := by
  intro A _ _ _ f J hJ u₀ hu₀ v hv
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra R A := φ.hom.toAlgebra
  have hJm : J ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal (ne_top_of_isNilpotent hJ)
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_isNilpotent hJ)
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  -- the structure map is local
  have : IsLocalHom (algebraMap R (ChartRing e y)) := ⟨fun r hr ↦ by
    by_contra h
    have : algebraMap R (ChartRing e y) r ∈ maximalIdeal (ChartRing e y) := by
      rw [chart_maximalIdeal e y]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 h)
    exact (mem_maximalIdeal _).1 this hr⟩
  have hloc : ∀ r ∈ maximalIdeal R, algebraMap R A r ∈ maximalIdeal A := by
    have hw := congrArg (fun g ↦ g (closedPoint (A ⧸ J))) (Over.w u₀)
    change (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing e y))))
      (u₀.left (closedPoint (A ⧸ J))) = (Spec.map φ) ((Spec.map (CommRingCat.ofHom
        (algebraMap A (A ⧸ J)))) (closedPoint (A ⧸ J))) at hw
    have : IsLocalHom (CommRingCat.ofHom (algebraMap A (A ⧸ J))).hom :=
      isLocalHom_of_le_jacobson_bot _ (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hJm)
    have h1 : u₀.left (closedPoint (A ⧸ J)) = closedPoint (ChartRing e y) := hu₀ _
    have h2 : (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J)))) (closedPoint (A ⧸ J)) =
        closedPoint A := Spec_closedPoint
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing e y))))
        (closedPoint (ChartRing e y)) = closedPoint R := Spec_closedPoint
    have hw' : closedPoint R = (Spec.map φ) (closedPoint A) :=
      h3.symm.trans ((congrArg _ h1.symm).trans (hw.trans (congrArg _ h2)))
    intro r hr
    have := congrArg PrimeSpectrum.asIdeal hw'
    change maximalIdeal R = Ideal.comap φ.hom (maximalIdeal A) at this
    rw [this] at hr
    exact hr
  obtain ⟨N, hN⟩ : IsNilpotent (maximalIdeal A) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rwa [jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hA : ∀ r ∈ maximalIdeal R ^ (N + 1), algebraMap R A r = 0 := by
    intro r hr
    have h1 : ((maximalIdeal R) ^ (N + 1)).map (algebraMap R A) ≤ ⊥ := by
      rw [Ideal.map_pow, ← Ideal.zero_eq_bot, ← hN]
      have hmap : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A :=
        Ideal.map_le_iff_le_comap.2 (fun r hr ↦ Ideal.mem_comap.2 (hloc r hr))
      refine (Ideal.pow_right_mono hmap _).trans ?_
      exact Ideal.pow_le_pow_right (Nat.le_succ N)
    exact (Ideal.mem_bot.1 (h1 (Ideal.mem_map_of_mem _ hr)))
  have hAJ : ∀ r ∈ maximalIdeal R ^ (N + 1), algebraMap R (A ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ J), hA r hr, map_zero]
  -- translate `u₀` and `hv`
  obtain ⟨ψ₀, hψ₀⟩ := exists_homR ((towerIso A (A ⧸ J)).inv ≫ u₀)
  have hu₀' : u₀ = (towerIso A (A ⧸ J)).hom ≫ homR ψ₀ := by
    rw [← hψ₀, Iso.hom_inv_id_assoc]
  have hv' : F.map (homR ψ₀).op (chartElem e hF3 y) =
      F.map (homR (Ideal.Quotient.mkₐ R J)).op v := by
    apply map_towerIso_injective A (A ⧸ J)
    rw [← map_comp_op_apply, ← hu₀', hv]
    show F.map (algebraOverBase (ovR R A).hom (A ⧸ J)).op v = _
    rw [algebraOverBase_eq, map_comp_op_apply]
  -- the residue condition
  let πJ : A ⧸ J →ₐ[R] ResidueField A :=
    Ideal.Quotient.liftₐ J (IsScalarTower.toAlgHom R A (ResidueField A))
      (fun a ha ↦ (residue_eq_zero_iff a).2 (hJm ha))
  have hσ : F.map (homR (πJ.comp ψ₀)).op (chartElem e hF3 y) =
      F.map (homR (IsScalarTower.toAlgHom R A (ResidueField A))).op v := by
    have hcomp : πJ.comp (Ideal.Quotient.mkₐ R J) = IsScalarTower.toAlgHom R A (ResidueField A) :=
      Ideal.Quotient.liftₐ_comp _ _ _
    rw [← map_homR_map_homR, hv', map_homR_map_homR, hcomp]
  obtain ⟨ψ, hψ⟩ := chart_lift e hF3 y N hA v (πJ.comp ψ₀) hσ
  refine ⟨homR ψ, ⟨?_, hψ⟩, fun u ⟨_, hu⟩ ↦ ?_⟩
  · rw [hu₀', show algebraOverBase (Spec.map φ) (A ⧸ J) =
      (towerIso A (A ⧸ J)).hom ≫ homR (Ideal.Quotient.mkₐ R J) from algebraOverBase_eq A J,
      Category.assoc, ← homR_comp]
    congr 2
    apply chart_inj_level e hF3 y N hAJ
    rw [← map_homR_map_homR, hψ, hv']
  · obtain ⟨ψ', rfl⟩ := exists_homR u
    congr 1
    exact chart_inj_level e hF3 y N hA (hu.trans hψ.symm)

end Limit

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
