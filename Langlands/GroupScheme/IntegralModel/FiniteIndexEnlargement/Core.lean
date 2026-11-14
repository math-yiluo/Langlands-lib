import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Enlarged
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Cover
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.OpenImmersionCriterion
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.RingTheory.RingHom.Smooth

/-! # The algebraic core of the finite-index enlargement

In the abstract setting of `Separating` and `Enlarged`, let `B` be a commutative Hopf algebra
with an injective bialgebra map `ι : B →ₐc[R] A` whose image consists exactly of the
coordinates integral on `V`. Given an element `b₀ ∈ B` with unit counit whose image is small at
every point of `V` outside `U`, we show:

* `B` is smooth over `R`;
* `K ⊗[R] B → K ⊗[R] A` is bijective;
* `Spec A → Spec B` is an open immersion;
* the generic points integral on `B` are exactly the points of `V`.

Applied to the enlarged Hopf algebra and the separating coordinate, this gives the algebraic
form of the finite-index enlargement. -/

noncomputable section

universe u

open TensorProduct WithConv CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section Lift

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Type*} [CommRing C] [Algebra R C]

/-- An algebra map into the fraction field with integral values, as an integral point. -/
def liftPoint (f : C →ₐ[R] K) (hf : ∀ c, f c ∈ (algebraMap R K).range) : C →ₐ[R] R :=
  (AlgEquiv.ofInjective (Algebra.ofId R K) (IsFractionRing.injective R K)).symm.toAlgHom.comp
    (f.codRestrict (Algebra.ofId R K).range hf)

theorem algebraMap_liftPoint (f : C →ₐ[R] K) (hf : ∀ c, f c ∈ (algebraMap R K).range)
    (c : C) : algebraMap R K (liftPoint f hf c) = f c :=
  congrArg Subtype.val
    ((AlgEquiv.ofInjective (Algebra.ofId R K) (IsFractionRing.injective R K)).apply_symm_apply
      (f.codRestrict (Algebra.ofId R K).range hf c))

theorem ofId_comp_liftPoint (f : C →ₐ[R] K) (hf : ∀ c, f c ∈ (algebraMap R K).range) :
    (Algebra.ofId R K).comp (liftPoint f hf) = f :=
  AlgHom.ext (algebraMap_liftPoint f hf)

/-- Integral points are determined by their values in the fraction field. -/
theorem eq_of_ofId_comp_eq {g g' : C →ₐ[R] R}
    (h : (Algebra.ofId R K).comp g = (Algebra.ofId R K).comp g') : g = g' :=
  AlgHom.ext fun c => IsFractionRing.injective R K (DFunLike.congr_fun h c)

omit [IsFractionRing R K] in
theorem mem_range_of_isIntUnit_mul [IsLocalRing R] {a b : K} (ha : IsIntUnit R a)
    (h : a * b ∈ (algebraMap R K).range) : b ∈ (algebraMap R K).range := by
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨s, hs⟩ := h
  refine ⟨(hr.unit⁻¹ : Rˣ) * s, ?_⟩
  rw [map_mul, hs, ← mul_assoc, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]

end Lift

section Localization

/-- A localization map along an injective ring map is bijective when every element of the
target becomes a multiple of the image after multiplying by a power of `r`. -/
theorem awayMap_bijective_of_forall {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) (r : S) (h : ∀ a, ∃ (n : ℕ) (b : S), φ b = φ r ^ n * a) :
    Function.Bijective (Localization.awayMap φ r) := by
  refine ⟨Localization.awayMap_injective_iff.mpr fun a ha => ⟨0, ?_⟩,
    Localization.awayMap_surjective_iff.mpr fun a => ?_⟩
  · rw [pow_zero, one_mul]
    exact hφ (ha.trans (map_zero φ).symm)
  · obtain ⟨n, b, hb⟩ := h a
    exact ⟨b, n, hb⟩

/-- A principal localization isomorphic to one of a smooth algebra is smooth. -/
theorem smooth_away_of_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.Smooth R T] (φ : S →ₐ[R] T) (r : S)
    (h : Function.Bijective (Localization.awayMap φ.toRingHom r)) :
    Algebra.Smooth R (Localization.Away r) := by
  have : Algebra.Smooth T (Localization.Away (φ r)) :=
    Algebra.Smooth.of_isLocalization_Away (φ r)
  have : Algebra.Smooth R (Localization.Away (φ r)) := Algebra.Smooth.comp R T _
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective (Localization.awayMapₐ φ r) h).symm

/-- Elements of the extended maximal ideal are divisible by a uniformiser. -/
theorem exists_eq_smul_of_mem_map {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {C : Type*} [CommRing C] [Algebra R C] {ϖ : R}
    (hϖ : Irreducible ϖ) {c : C}
    (hc : c ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R C)) : ∃ c', c = ϖ • c' := by
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hc
  obtain ⟨c', rfl⟩ := hc
  exact ⟨c', (Algebra.smul_def ϖ c').symm⟩

end Localization

section HopfPoints

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [CommRing A] [HopfAlgebra R A] {P : Type*} [Group P]
  (ev : P →* WithConv (A →ₐ[R] K))
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (V : Subgroup P) (hUV : U ≤ V)
  {B : Type u} [CommRing B] [HopfAlgebra R B] (ι : B →ₐc[R] A)
  (hB : ∀ a, a ∈ Set.range ι ↔ ∀ x ∈ V, ev x a ∈ (algebraMap R K).range)

omit [IsFractionRing R K] in
theorem ev_smul_apply (x : P) (r : R) (a : A) :
    ev x (r • a) = algebraMap R K r * ev x a := by
  rw [Algebra.smul_def, ev_mul_apply, ev_algebraMap]

omit [IsFractionRing R K] in
include hB in
theorem ev_ι_mem {x : P} (hx : x ∈ V) (b : B) : ev x (ι b) ∈ (algebraMap R K).range :=
  (hB _).1 ⟨b, rfl⟩ x hx

/-- The integral point of `A` given by a point of `U`. -/
def pointA (u : U) : A →ₐ[R] R :=
  liftPoint (ev u).ofConv fun a => (hU u).1 u.2 a

theorem algebraMap_pointA (u : U) (a : A) :
    algebraMap R K (pointA ev U hU u a) = ev u a :=
  algebraMap_liftPoint _ _ a

theorem ofId_comp_pointA (u : U) :
    (Algebra.ofId R K).comp (pointA ev U hU u) = (ev u).ofConv :=
  ofId_comp_liftPoint _ _

/-- The integral point of `B` given by a point of `V`. -/
def pointB (z : V) : B →ₐ[R] R :=
  liftPoint ((ev z).ofConv.comp ι.toAlgHom) fun b => ev_ι_mem ev V ι hB z.2 b

theorem algebraMap_pointB (z : V) (b : B) :
    algebraMap R K (pointB ev V ι hB z b) = ev z (ι b) :=
  algebraMap_liftPoint _ _ b

theorem ofId_comp_pointB (z : V) :
    (Algebra.ofId R K).comp (pointB ev V ι hB z) = (ev z).ofConv.comp ι.toAlgHom :=
  ofId_comp_liftPoint _ _

/-- The points of `V`, as a group homomorphism into the convolution monoid of integral points
of `B`. -/
def σB : V →* WithConv (B →ₐ[R] R) where
  toFun z := toConv (pointB ev V ι hB z)
  map_one' := by
    apply WithConv.ofConv_injective
    ext b
    apply IsFractionRing.injective R K
    rw [ofConv_toConv, algebraMap_pointB]
    change ev (1 : P) (ι b) = algebraMap R K ((1 : WithConv (B →ₐ[R] R)) b)
    rw [AlgHom.convOne_apply, ev_one_apply, CoalgHomClass.counit_comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
  map_mul' z w := by
    apply WithConv.ofConv_injective
    apply eq_of_ofId_comp_eq (K := K)
    simp only
    rw [AlgHom.comp_convMul_distrib]
    simp only [ofId_comp_pointB]
    rw [← AlgHom.convMul_comp_bialgHom_distrib, ← map_mul]
    rfl

theorem σB_apply (z : V) : (σB ev V ι hB z).ofConv = pointB ev V ι hB z :=
  rfl

/-- Values of a translate: translating by `z ∈ V` multiplies the point on the right by `z`. -/
theorem ev_ι_pointTrans (x : P) (z : V) (b : B) :
    ev x (ι (pointTrans (pointB ev V ι hB z) b)) = ev (x * z) (ι b) := by
  have h := comp_pointTrans ((ev x).ofConv.comp ι.toAlgHom) (pointB ev V ι hB z)
  rw [ofId_comp_pointB, ← AlgHom.convMul_comp_bialgHom_distrib, ← map_mul] at h
  exact DFunLike.congr_fun h b

/-- On points of `U`, the integral points of `B` are restrictions of those of `A`. -/
theorem pointB_eq_comp (u : U) :
    pointB ev V ι hB ⟨u, hUV u.2⟩ = (pointA ev U hU u).comp ι.toAlgHom :=
  eq_of_ofId_comp_eq (K := K) (by rw [ofId_comp_pointB, ← AlgHom.comp_assoc, ofId_comp_pointA])

end HopfPoints

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A] [Algebra.Smooth R A]
  {P : Type*} [Group P] (ev : P →* WithConv (A →ₐ[R] K))
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ)
  (V : Subgroup P) (hUV : U ≤ V)
  (T : Finset P) (hT : ∀ x ∈ V, ∃ r ∈ T, ∃ u ∈ U, x = r * u)
  {B : Type u} [CommRing B] [HopfAlgebra R B] (ι : B →ₐc[R] A) (hι : Function.Injective ι)
  (hB : ∀ a, a ∈ Set.range ι ↔ ∀ x ∈ V, ev x a ∈ (algebraMap R K).range)
  {ϖ : R} (hϖ : Irreducible ϖ)

omit [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra.Smooth R A] in
include hU hT hB hϖ in
/-- Every coordinate becomes a coordinate of `B` after multiplication by a power of `ϖ`. -/
theorem exists_ι_eq_pow_mul (a : A) :
    ∃ (n : ℕ) (b : B), ι b = algebraMap R A (ϖ ^ n) * a := by
  obtain ⟨N, hN⟩ := exists_bound ev U hU V T hT hϖ a
  obtain ⟨b, hb⟩ := (hB (algebraMap R A (ϖ ^ N) * a)).2 fun x hx => by
    rw [ev_mul_apply, ev_algebraMap]
    exact hN x hx
  exact ⟨N, b, hb⟩

omit [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra.Smooth R A] in
include hU hT hB hϖ in
/-- Every coordinate becomes a coordinate of `B` after multiplication by a power of an element
of `B` that is small at every point of `V` outside `U`. -/
theorem exists_ι_eq_pow_mul_of_small {e : B}
    (he : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι e))) (a : A) :
    ∃ (n : ℕ) (b : B), ι b = ι e ^ n * a := by
  obtain ⟨N, hN⟩ := exists_bound ev U hU V T hT hϖ a
  obtain ⟨b, hb⟩ := (hB (ι e ^ (N + 1) * a)).2 fun x hx => by
    rw [ev_mul_apply, ev_pow_apply]
    by_cases hxU : x ∈ U
    · exact Subring.mul_mem _ (Subring.pow_mem _ (ev_ι_mem ev V ι hB hx e) _) ((hU x).1 hxU a)
    · rw [mul_comm]
      exact (isIntSmall_mul_pow hϖ (hN x hx) (he x hx hxU)).mem_range
  exact ⟨N + 1, b, hb⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  [Algebra.Smooth R A] in
/-- Translates by points of `U` of an element small off `U` are again small off `U`. -/
theorem isIntSmall_pointTrans {e : B} (he : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι e)))
    (u : U) :
    ∀ x ∈ V, x ∉ U →
      IsIntSmall R (ev x (ι (pointTrans (pointB ev V ι hB ⟨u, hUV u.2⟩) e))) := by
  intro x hx hxU
  rw [ev_ι_pointTrans]
  refine he _ (V.mul_mem hx (hUV u.2)) fun hxu => hxU ?_
  simpa using U.mul_mem hxu (U.inv_mem u.2)

include hU hsurj hϖ in
/-- The integral points from `U` detect divisibility by `ϖ` in `A`. -/
theorem exists_eq_smul_of_forall_pointA (c : A)
    (hc : ∀ u : U, pointA ev U hU u c ∈ IsLocalRing.maximalIdeal R) : ∃ c', c = ϖ • c' := by
  apply exists_eq_smul_of_mem_map hϖ
  apply mem_map_maximalIdeal_of_forall
  intro σ
  obtain ⟨u, hu⟩ := hsurj σ
  have huU : u ∈ U := (hU u).2 fun a => ⟨σ a, by rw [hu]; rfl⟩
  have hσ : σ = pointA ev U hU ⟨u, huU⟩ :=
    eq_of_ofId_comp_eq (K := K) (by rw [← hu, ofId_comp_pointA])
  rw [hσ]
  exact hc _

include hU hsurj hUV hι hB hϖ in
/-- The integral points from `V` detect divisibility by `ϖ` in `B`. -/
theorem exists_eq_smul_of_forall_pointB (b : B)
    (hb : ∀ z : V, pointB ev V ι hB z b ∈ IsLocalRing.maximalIdeal R) : ∃ b', b = ϖ • b' := by
  have hϖK : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  obtain ⟨a', ha'⟩ := exists_eq_smul_of_forall_pointA ev U hU hsurj hϖ (ι b) fun u => by
    have h1 : pointA ev U hU u (ι b) = pointB ev V ι hB ⟨u, hUV u.2⟩ b := by
      rw [pointB_eq_comp ev U hU V hUV ι hB u]
      rfl
    rw [h1]
    exact hb _
  obtain ⟨b', hb'⟩ := (hB a').2 fun x hx => by
    obtain ⟨c, hc⟩ : ϖ ∣ pointB ev V ι hB ⟨x, hx⟩ b := by
      have := hb ⟨x, hx⟩
      rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    refine ⟨c, mul_left_cancel₀ hϖK ?_⟩
    rw [← map_mul, ← hc, algebraMap_pointB, ha', ev_smul_apply]
  refine ⟨b', hι ?_⟩
  rw [ha', map_smul, hb']

include hU hsurj hUV hι hB hϖ in
/-- `ϖ` and the translates of `b₀` by the points of `V` generate the unit ideal of `B`. -/
theorem span_cover_B {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀)) :
    Ideal.span (insert (algebraMap R B ϖ)
      (Set.range fun z : V => pointTrans (pointB ev V ι hB z) b₀)) = ⊤ :=
  span_insert_pointTrans_eq_top (pointB ev V ι hB)
    (exists_eq_smul_of_forall_pointB ev U hU hsurj V hUV ι hι hB hϖ) hb₀

include hU hsurj hϖ in
/-- `ϖ` and the translates of `ι b₀` by the points of `U` generate the unit ideal of `A`. -/
theorem span_cover_A {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀)) :
    Ideal.span (insert (algebraMap R A ϖ)
      (Set.range fun u : U => pointTrans (pointA ev U hU u) (ι b₀))) = ⊤ :=
  span_insert_pointTrans_eq_top (pointA ev U hU)
    (exists_eq_smul_of_forall_pointA ev U hU hsurj hϖ)
    (by rwa [CoalgHomClass.counit_comp_apply])

include hU hsurj hUV hT hι hB hϖ in
/-- **Smoothness.** `B` is smooth over `R`. -/
theorem smooth_of_core {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀))
    (hsmall : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι b₀))) : Algebra.Smooth R B := by
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.Smooth.ofLocalizationSpanTarget (algebraMap R B) _
    (span_cover_B ev U hU hsurj V hUV ι hι hB hϖ hb₀) ?_
  rintro ⟨r, hr⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.smooth_algebraMap]
  rcases hr with rfl | ⟨z, rfl⟩
  · refine smooth_away_of_bijective ι.toAlgHom _
      (awayMap_bijective_of_forall _ hι _ fun a => ?_)
    obtain ⟨n, b, hb⟩ := exists_ι_eq_pow_mul ev U hU V T hT ι hB hϖ a
    refine ⟨n, b, ?_⟩
    change ι b = ι (algebraMap R B ϖ) ^ n * a
    rw [hb, AlgHomClass.commutes, map_pow]
  · have : Algebra.Smooth R (Localization.Away b₀) :=
      smooth_away_of_bijective ι.toAlgHom b₀ (awayMap_bijective_of_forall _ hι _
        (exists_ι_eq_pow_mul_of_small ev U hU V T hT ι hB hϖ hsmall))
    exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective
      (Localization.awayMapₐ (transEquiv (σB ev V ι hB) z).toAlgHom b₀)
      (awayMap_bijective_of_forall _ (transEquiv (σB ev V ι hB) z).injective _ fun a =>
        ⟨0, (transEquiv (σB ev V ι hB) z).symm a, by
          rw [pow_zero, one_mul]
          exact (transEquiv (σB ev V ι hB) z).apply_symm_apply a⟩))

theorem tensorMap_apply_eq_lTensor {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : B →ₐ[R] A) (t : K ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id K K) f t = LinearMap.lTensor K f.toLinearMap t := by
  induction t using TensorProduct.inductionOn with
  | tmul c b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra.Smooth R A] in
include hU hT hι hB hϖ in
/-- **Generic fibre.** `K ⊗[R] B → K ⊗[R] A` is bijective. -/
theorem baseChange_bijective_of_core :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) ι.toAlgHom) := by
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hϖK : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  constructor
  · intro t t' h
    rw [tensorMap_apply_eq_lTensor, tensorMap_apply_eq_lTensor] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toAlgHom.toLinearMap hι h
  · intro t
    induction t using TensorProduct.inductionOn with
    | tmul c a =>
      obtain ⟨n, b, hb⟩ := exists_ι_eq_pow_mul ev U hU V T hT ι hB hϖ a
      have hne : algebraMap R K (ϖ ^ n) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ hϖK
      refine ⟨(c * (algebraMap R K (ϖ ^ n))⁻¹) ⊗ₜ b, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (c * (algebraMap R K (ϖ ^ n))⁻¹) ⊗ₜ[R] ι b = c ⊗ₜ[R] a
      rw [hb, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hne, mul_one]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

include hU hsurj hUV hT hι hB hϖ in
/-- **Open immersion.** `Spec A → Spec B` is an open immersion. -/
theorem isOpenImmersion_of_core {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀))
    (hsmall : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι b₀))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ι.toAlgHom.toRingHom)) := by
  let s : Option U → B := fun i =>
    i.elim (algebraMap R B ϖ) fun u => pointTrans (pointB ev V ι hB ⟨u, hUV u.2⟩) b₀
  refine isOpenImmersion_specMap_of_away_bijective ι.toAlgHom.toRingHom s ?_ ?_
  · rw [eq_top_iff, ← span_cover_A ev U hU hsurj ι hϖ hb₀]
    apply Ideal.span_mono
    rintro a (rfl | ⟨u, rfl⟩)
    · exact ⟨none, AlgHomClass.commutes ι ϖ⟩
    · refine ⟨some u, ?_⟩
      change ι (pointTrans (pointB ev V ι hB ⟨u, hUV u.2⟩) b₀) =
        pointTrans (pointA ev U hU u) (ι b₀)
      rw [pointB_eq_comp ev U hU V hUV ι hB u, map_pointTrans]
  · rintro (_ | u)
    · refine awayMap_bijective_of_forall _ hι _ fun a => ?_
      obtain ⟨n, b, hb⟩ := exists_ι_eq_pow_mul ev U hU V T hT ι hB hϖ a
      refine ⟨n, b, ?_⟩
      change ι b = ι (algebraMap R B ϖ) ^ n * a
      rw [hb, AlgHomClass.commutes, map_pow]
    · exact awayMap_bijective_of_forall _ hι _
        (exists_ι_eq_pow_mul_of_small ev U hU V T hT ι hB hϖ
          (isIntSmall_pointTrans ev U V hUV ι hB hsmall u))

include hU hsurj hUV hT hι hB hϖ in
/-- **Points.** A generic point integral on `B` lies in `V`. -/
theorem mem_of_forall_ev_ι {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀))
    (hsmall : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι b₀))) {x : P}
    (hx : ∀ b, ev x (ι b) ∈ (algebraMap R K).range) : x ∈ V := by
  let τ : B →ₐ[R] R := liftPoint ((ev x).ofConv.comp ι.toAlgHom) hx
  have hmap := congrArg (Ideal.map τ) (span_cover_B ev U hU hsurj V hUV ι hι hB hϖ hb₀)
  rw [Ideal.map_span, Ideal.map_top] at hmap
  obtain ⟨_, ⟨r, hr, rfl⟩, hunit⟩ : ∃ s ∈ τ '' (insert (algebraMap R B ϖ)
      (Set.range fun z : V => pointTrans (pointB ev V ι hB z) b₀)), IsUnit s := by
    by_contra hcon
    push Not at hcon
    apply (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    rw [eq_top_iff, ← hmap, Ideal.span_le]
    intro s hs
    exact (IsLocalRing.mem_maximalIdeal s).mpr (mem_nonunits_iff.mpr (hcon s hs))
  rcases hr with rfl | ⟨z, rfl⟩
  · rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hunit
    exact absurd hunit hϖ.not_isUnit
  · have h1 : IsIntUnit R (ev (x * z) (ι b₀)) :=
      ⟨_, hunit, (algebraMap_liftPoint _ hx _).trans (ev_ι_pointTrans ev V ι hB x z b₀)⟩
    have hxz : x * z ∈ U := by
      rw [hU]
      intro a
      obtain ⟨n, b, hb⟩ := exists_ι_eq_pow_mul_of_small ev U hU V T hT ι hB hϖ hsmall a
      apply mem_range_of_isIntUnit_mul (h1.pow n)
      rw [← ev_pow_apply, ← ev_mul_apply, ← hb, ← ev_ι_pointTrans ev V ι hB x z b]
      exact hx _
    simpa using V.mul_mem (hUV hxz) (V.inv_mem z.2)

include hU hsurj hUV hT hι hB hϖ in
/-- **Algebraic core, generic form.** -/
theorem core_of_hopf {b₀ : B} (hb₀ : IsUnit (Coalgebra.counit (R := R) b₀))
    (hsmall : ∀ x ∈ V, x ∉ U → IsIntSmall R (ev x (ι b₀))) :
    Algebra.Smooth R B ∧
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) ι.toAlgHom) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ι.toAlgHom.toRingHom)) ∧
      ∀ x, (∀ b, (ev x).ofConv (ι b) ∈ (algebraMap R K).range) ↔ x ∈ V :=
  ⟨smooth_of_core ev U hU hsurj V hUV T hT ι hι hB hϖ hb₀ hsmall,
    baseChange_bijective_of_core ev U hU V T hT ι hι hB hϖ,
    isOpenImmersion_of_core ev U hU hsurj V hUV T hT ι hι hB hϖ hb₀ hsmall,
    fun _ => ⟨mem_of_forall_ev_ι ev U hU hsurj V hUV T hT ι hι hB hϖ hb₀ hsmall,
      fun hx b => ev_ι_mem ev V ι hB hx b⟩⟩

end Main

section Assembly

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A] [Algebra.Smooth R A]
  {P : Type*} [Group P] (ev : P →* WithConv (A →ₐ[R] K))
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ)
  (V : Subgroup P) (hUV : U ≤ V) (hnorm : ∀ x ∈ V, ∀ u ∈ U, x⁻¹ * u * x ∈ U)

/-- The inclusion of the enlarged Hopf algebra, as a bialgebra map. -/
abbrev enlargedι (hfin : HasReps U V) :
    let := enlargedHopfAlgebra ev V U hU hsurj hUV hnorm hfin
    enlarged ev V →ₐc[R] A :=
  haveI := flat_enlarged ev V (R := R)
  SubHopf.valBialgHom (enlarged ev V)
    (comul_mem_range_ι₂_of_hasReps ev V U hU hsurj hUV hnorm hfin)
    (fun x => antipode_mem_enlarged ev V x.2)

include hU hsurj hUV in
/-- **Algebraic core of the finite-index enlargement.** There is a smooth commutative Hopf
algebra `B` with a bialgebra map to `A` that is an isomorphism after base change to `K` and an
open immersion on spectra, whose integral generic points are exactly the points of `V`. -/
theorem exists_hopf_enlargement [(U.subgroupOf V).Normal] [(U.subgroupOf V).FiniteIndex] :
    ∃ (B : CommHopfAlgCat.{u} R) (ι : B →ₐc[R] A), Algebra.Smooth R B ∧
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) ι.toAlgHom) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ι.toAlgHom.toRingHom)) ∧
      ∀ x, (∀ b, (ev x).ofConv (ι b) ∈ (algebraMap R K).range) ↔ x ∈ V := by
  classical
  have hnorm := inv_mul_mul_mem U V hUV
  obtain ⟨n, hpow⟩ := exists_pow_succ_mem U V
  obtain ⟨T, hT⟩ := exists_finset_of_finiteIndex U V
  have hfin : HasReps U V := by
    refine ⟨T.filter (· ∈ V), fun r hr => (Finset.mem_filter.mp hr).2, fun x hx => ?_⟩
    obtain ⟨r, hr, u, hu, rfl⟩ := hT x hx
    have hrV : r ∈ V := by simpa using V.mul_mem hx (V.inv_mem (hUV hu))
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, hrV⟩, u, hu, rfl⟩
  obtain ⟨e, heV, he1, hesmall⟩ := exists_separating ev U hU hsurj V hUV hnorm T hT n hpow
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := enlargedHopfAlgebra ev V U hU hsurj hUV hnorm hfin
  let ι := enlargedι ev U hU hsurj V hUV hnorm hfin
  have hι : Function.Injective ι := Subtype.val_injective
  have hB : ∀ a, a ∈ Set.range ι ↔ ∀ x ∈ V, ev x a ∈ (algebraMap R K).range :=
    fun a => ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  let b₀ : enlarged ev V := ⟨e, heV⟩
  have hb₀ : IsUnit (Coalgebra.counit (R := R) b₀) := by
    rw [← CoalgHomClass.counit_comp_apply ι b₀]
    change IsUnit (Coalgebra.counit (R := R) e)
    obtain ⟨r, hr, hre⟩ := he1
    rw [ev_one_apply] at hre
    rwa [← IsFractionRing.injective R K hre]
  exact ⟨CommHopfAlgCat.of R (enlarged ev V), ι,
    core_of_hopf ev U hU hsurj V hUV T hT ι hι hB hϖ hb₀ hesmall⟩

end Assembly

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
