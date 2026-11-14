import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.Separating
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement.SubHopf
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-! # The enlarged Hopf algebra

In the abstract setting of `Translation`, let `V ⊇ U` be a subgroup in which the integral points
`U` are normal of finite index. The coordinates integral at all points of `V` form a subalgebra
`enlarged ev V` of `A`. We show that the comultiplication maps it into its own tensor square and
the antipode maps it into itself, so that it is a Hopf algebra over `R`.

The proof that the comultiplication preserves the subalgebra uses flatness twice: the subalgebra
is cut out of `A` by finitely many conditions on translates, both by right and by left
translations, and tensoring with a flat module preserves such descriptions. -/

noncomputable section

universe u

open TensorProduct WithConv

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

section FlatKernel

variable {R : Type*} [CommRing R] {M N N' Q : Type*} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup N'] [AddCommGroup Q] [Module R M] [Module R N] [Module R N'] [Module R Q]
  {I : Type*} [Fintype I]

/-- If `N` is cut out of `N'` by finitely many linear conditions, then for flat `M` the image of
`M ⊗ N` in `M ⊗ N'` is cut out by the same conditions. -/
theorem mem_range_lTensor_of_forall [Module.Flat R M] (ι : N →ₗ[R] N') (f : I → N' →ₗ[R] Q)
    (hf : ∀ y, (∀ i, f i y = 0) ↔ y ∈ LinearMap.range ι) (z : M ⊗[R] N')
    (hz : ∀ i, LinearMap.lTensor M (f i) z = 0) :
    z ∈ LinearMap.range (LinearMap.lTensor M ι) := by
  classical
  have hex : Function.Exact ι (LinearMap.pi f) := by
    intro y
    have h := hf y
    rw [LinearMap.mem_range] at h
    rw [Set.mem_range, ← h, funext_iff]
    simp only [LinearMap.pi_apply, Pi.zero_apply]
  have hcomp : ∀ (w : M ⊗[R] N') (i : I),
      TensorProduct.piRight R R M (fun _ : I => Q) (LinearMap.lTensor M (LinearMap.pi f) w) i =
        LinearMap.lTensor M (f i) w := by
    intro w i
    induction w using TensorProduct.inductionOn with
    | tmul m n => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  have h0 : LinearMap.lTensor M (LinearMap.pi f) z = 0 := by
    apply (TensorProduct.piRight R R M (fun _ : I => Q)).injective
    rw [map_zero]
    funext i
    rw [hcomp, Pi.zero_apply, hz i]
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact M hex z).1 h0
  exact ⟨w, hw⟩

theorem comm_rTensor_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] (g : X →ₗ[R] Y) (w : X ⊗[R] M) :
    TensorProduct.comm R Y M (LinearMap.rTensor M g w) =
      LinearMap.lTensor M g (TensorProduct.comm R X M w) := by
  induction w using TensorProduct.inductionOn with
  | tmul m n => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Right-handed version of `mem_range_lTensor_of_forall`. -/
theorem mem_range_rTensor_of_forall [Module.Flat R M] (ι : N →ₗ[R] N') (f : I → N' →ₗ[R] Q)
    (hf : ∀ y, (∀ i, f i y = 0) ↔ y ∈ LinearMap.range ι) (z : N' ⊗[R] M)
    (hz : ∀ i, LinearMap.rTensor M (f i) z = 0) :
    z ∈ LinearMap.range (LinearMap.rTensor M ι) := by
  obtain ⟨w, hw⟩ := mem_range_lTensor_of_forall ι f hf (TensorProduct.comm R N' M z) fun i => by
    rw [← comm_rTensor_apply, hz i, map_zero]
  refine ⟨TensorProduct.comm R M N w, (TensorProduct.comm R N' M).injective ?_⟩
  have hcc : TensorProduct.comm R N M (TensorProduct.comm R M N w) = w := by
    rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply]
  rw [comm_rTensor_apply, hcc, hw]

end FlatKernel

section Identities

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {A : Type u} [CommRing A] [HopfAlgebra R A] {P : Type*} [Group P]
  (ev : P →* WithConv (A →ₐ[R] K))

/-- The inclusion `a ↦ 1 ⊗ a` of `A` into `K ⊗[R] A`. -/
abbrev incl : A →ₗ[R] K ⊗[R] A := (Algebra.TensorProduct.includeRight (R := R) (A := K)).toLinearMap

theorem incl_apply (a : A) : incl (R := R) (K := K) a = (1 : K) ⊗ₜ[R] a := rfl

theorem rightTrans_toLinearMap (x : P) :
    (rightTrans ev x).toLinearMap =
      (TensorProduct.comm R A K).toLinearMap ∘ₗ
        LinearMap.lTensor A (ev x).ofConv.toLinearMap ∘ₗ Coalgebra.comul := by
  apply LinearMap.ext
  intro a
  rfl

theorem leftTrans_toLinearMap (x : P) :
    (leftTrans ev x).toLinearMap =
      LinearMap.rTensor A (ev x).ofConv.toLinearMap ∘ₗ Coalgebra.comul := by
  apply LinearMap.ext
  intro a
  rfl

/-- Coassociativity in terms of right translations. -/
theorem leftComm_lTensor_rightTrans (x : P) (a : A) :
    TensorProduct.leftComm R A K A
        (LinearMap.lTensor A (rightTrans ev x).toLinearMap (Coalgebra.comul (R := R) a)) =
      LinearMap.lTensor K Coalgebra.comul (rightTrans ev x a) := by
  have hv : ∀ (v : A ⊗[R] A) (z : A),
      TensorProduct.leftComm R A K A
          (LinearMap.lTensor A (TensorProduct.comm R A K).toLinearMap
            (LinearMap.lTensor A (LinearMap.lTensor A (ev x).ofConv.toLinearMap)
              (TensorProduct.assoc R A A A (v ⊗ₜ[R] z)))) =
        ev x z ⊗ₜ[R] v := by
    intro v z
    induction v using TensorProduct.inductionOn with
    | tmul p q => simp
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq, TensorProduct.tmul_add]
  have hw : ∀ w : A ⊗[R] A,
      TensorProduct.leftComm R A K A
          (LinearMap.lTensor A (TensorProduct.comm R A K).toLinearMap
            (LinearMap.lTensor A (LinearMap.lTensor A (ev x).ofConv.toLinearMap)
              (TensorProduct.assoc R A A A (LinearMap.rTensor A Coalgebra.comul w)))) =
        LinearMap.lTensor K Coalgebra.comul
          (TensorProduct.comm R A K (LinearMap.lTensor A (ev x).ofConv.toLinearMap w)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q =>
      rw [LinearMap.rTensor_tmul, hv, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
        LinearMap.lTensor_tmul]
      rfl
    | add p q hp hq => simp only [map_add, hp, hq]
  rw [show rightTrans ev x a = (rightTrans ev x).toLinearMap a from rfl, rightTrans_toLinearMap,
    LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  simp only [LinearMap.comp_apply]
  rw [← Coalgebra.coassoc_apply, hw]
  rfl

/-- Coassociativity in terms of left translations. -/
theorem assoc_rTensor_leftTrans (x : P) (a : A) :
    TensorProduct.assoc R K A A
        (LinearMap.rTensor A (leftTrans ev x).toLinearMap (Coalgebra.comul (R := R) a)) =
      LinearMap.lTensor K Coalgebra.comul (leftTrans ev x a) := by
  have hw : ∀ w : (A ⊗[R] A) ⊗[R] A,
      TensorProduct.assoc R K A A
          (LinearMap.rTensor A (LinearMap.rTensor A (ev x).ofConv.toLinearMap) w) =
        LinearMap.rTensor (A ⊗[R] A) (ev x).ofConv.toLinearMap (TensorProduct.assoc R A A A w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q =>
      induction p using TensorProduct.inductionOn with
      | tmul s t => simp
      | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | add p q hp hq => simp only [map_add, hp, hq]
  have hm : ∀ w : A ⊗[R] A,
      LinearMap.lTensor K Coalgebra.comul (LinearMap.rTensor A (ev x).ofConv.toLinearMap w) =
        LinearMap.rTensor (A ⊗[R] A) (ev x).ofConv.toLinearMap
          (LinearMap.lTensor A Coalgebra.comul w) := by
    intro w
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [show leftTrans ev x a = (leftTrans ev x).toLinearMap a from rfl, leftTrans_toLinearMap,
    LinearMap.rTensor_comp]
  simp only [LinearMap.comp_apply]
  rw [hw, hm, Coalgebra.coassoc_apply]

theorem leftComm_symm_tmul_one (w : A ⊗[R] A) :
    (TensorProduct.leftComm R A K A).symm ((1 : K) ⊗ₜ[R] w) = LinearMap.lTensor A incl w := by
  induction w using TensorProduct.inductionOn with
  | tmul p q => rfl
  | add p q hp hq => rw [TensorProduct.tmul_add, map_add, hp, hq, map_add]

theorem assoc_symm_tmul_one (w : A ⊗[R] A) :
    (TensorProduct.assoc R K A A).symm ((1 : K) ⊗ₜ[R] w) = LinearMap.rTensor A incl w := by
  induction w using TensorProduct.inductionOn with
  | tmul p q => rfl
  | add p q hp hq => rw [TensorProduct.tmul_add, map_add, hp, hq, map_add]

/-- The convolution inverse of an evaluation is its composite with the antipode. -/
theorem ev_inv_ofConv (x : P) :
    (ev x⁻¹).ofConv = (ev x).ofConv.comp (HopfAlgebra.antipodeAlgHom R A) := by
  set f := ev x
  set g : WithConv (A →ₐ[R] K) := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
  have hleft : g * f = 1 := by
    have H : (Algebra.TensorProduct.lmul' R).comp
        (Algebra.TensorProduct.map f.ofConv f.ofConv) =
        f.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
    trans toConv <| ((Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (Bialgebra.comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp
        (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] K)
    rw [LinearMap.antipode_mul_id]
    ext
    simp
  have hinv : ev x⁻¹ = g :=
    calc ev x⁻¹ = 1 * ev x⁻¹ := (one_mul _).symm
      _ = (g * f) * ev x⁻¹ := by rw [hleft]
      _ = g * (f * ev x⁻¹) := mul_assoc _ _ _
      _ = g := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [hinv]

theorem ev_inv_apply (x : P) (a : A) : ev x⁻¹ a = ev x (HopfAlgebra.antipode R a) :=
  DFunLike.congr_fun (ev_inv_ofConv ev x) a

end Identities

/-- `V` is covered by finitely many left cosets `r * U` with `r ∈ V`. -/
def HasReps {P : Type*} [Group P] (U V : Subgroup P) : Prop :=
  ∃ T : Finset P, (∀ r ∈ T, r ∈ V) ∧ ∀ x ∈ V, ∃ r ∈ T, ∃ u ∈ U, x = r * u

section Enlarged

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {A : Type u} [CommRing A] [HopfAlgebra R A] {P : Type*} [Group P]
  (ev : P →* WithConv (A →ₐ[R] K)) (V : Subgroup P)

/-- The coordinates whose values at all points of `V` are integral. -/
def enlarged : Subalgebra R A where
  carrier := {a | ∀ x ∈ V, ev x a ∈ (algebraMap R K).range}
  mul_mem' {a b} ha hb x hx := by
    rw [map_mul]
    exact Subring.mul_mem _ (ha x hx) (hb x hx)
  add_mem' {a b} ha hb x hx := by
    rw [map_add]
    exact Subring.add_mem _ (ha x hx) (hb x hx)
  algebraMap_mem' r x _ := ⟨r, (ev_algebraMap ev x r).symm⟩

theorem mem_enlarged {a : A} :
    a ∈ enlarged ev V ↔ ∀ x ∈ V, ev x a ∈ (algebraMap R K).range :=
  Iff.rfl

/-- The antipode preserves the enlarged algebra. -/
theorem antipode_mem_enlarged {a : A} (ha : a ∈ enlarged ev V) :
    HopfAlgebra.antipode R a ∈ enlarged ev V := fun x hx => by
  rw [← ev_inv_apply]
  exact ha _ (V.inv_mem hx)

theorem mem_range_val_iff {a : A} :
    a ∈ LinearMap.range (enlarged ev V).val.toLinearMap ↔ a ∈ enlarged ev V :=
  ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K] [Algebra.Smooth R A]
  (U : Subgroup P) (hU : ∀ x, x ∈ U ↔ ∀ a, ev x a ∈ (algebraMap R K).range)
  (hsurj : ∀ σ : A →ₐ[R] R, ∃ u, (ev u).ofConv = (Algebra.ofId R K).comp σ)
  (hUV : U ≤ V) (hnorm : ∀ x ∈ V, ∀ u ∈ U, x⁻¹ * u * x ∈ U)
  (T : Finset P) (hTV : ∀ r ∈ T, r ∈ V) (hT : ∀ x ∈ V, ∃ r ∈ T, ∃ u ∈ U, x = r * u)

include hU hsurj hUV hnorm hTV hT in
/-- The enlarged algebra is cut out by the right translates by the representatives. -/
theorem mem_enlarged_iff_rightTrans (a : A) :
    a ∈ enlarged ev V ↔ ∀ r ∈ T, ∃ b : A, (1 : K) ⊗ₜ[R] b = rightTrans ev r a := by
  constructor
  · intro ha r hr
    exact exists_rightTrans_eq ev U hU hsurj r a fun u hu => ha _ (V.mul_mem (hUV hu) (hTV r hr))
  · intro h x hx
    obtain ⟨r, hr, u, hu, rfl⟩ := hT x hx
    obtain ⟨b, hb⟩ := h r hr
    have hu' : r * u * r⁻¹ ∈ U := by simpa using hnorm r⁻¹ (V.inv_mem (hTV r hr)) u hu
    have hru : r * u = (r * u * r⁻¹) * r := by group
    rw [hru, ← evalExt_rightTrans, ← hb, evalExt_one_tmul]
    exact (hU _).1 hu' b

include hU hsurj hUV hTV hT in
/-- The enlarged algebra is cut out by the left translates by the representatives. -/
theorem mem_enlarged_iff_leftTrans (a : A) :
    a ∈ enlarged ev V ↔ ∀ r ∈ T, ∃ b : A, (1 : K) ⊗ₜ[R] b = leftTrans ev r a := by
  constructor
  · intro ha r hr
    exact exists_leftTrans_eq ev U hU hsurj r a fun u hu => ha _ (V.mul_mem (hTV r hr) (hUV hu))
  · intro h x hx
    obtain ⟨r, hr, u, hu, rfl⟩ := hT x hx
    obtain ⟨b, hb⟩ := h r hr
    rw [← evalExt_leftTrans, ← hb, evalExt_one_tmul]
    exact (hU _).1 hu b

include hU hsurj hUV hnorm hTV hT in
theorem forall_mkQ_rightTrans_iff (a : A) :
    (∀ r : T, ((LinearMap.range (incl (R := R) (K := K) (A := A))).mkQ ∘ₗ
        (rightTrans ev r).toLinearMap) a = 0) ↔
      a ∈ LinearMap.range (enlarged ev V).val.toLinearMap := by
  rw [mem_range_val_iff, mem_enlarged_iff_rightTrans ev V U hU hsurj hUV hnorm T hTV hT]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range, incl_apply]
  exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r r.2⟩

include hU hsurj hUV hTV hT in
theorem forall_mkQ_leftTrans_iff (a : A) :
    (∀ r : T, ((LinearMap.range (incl (R := R) (K := K) (A := A))).mkQ ∘ₗ
        (leftTrans ev r).toLinearMap) a = 0) ↔
      a ∈ LinearMap.range (enlarged ev V).val.toLinearMap := by
  rw [mem_range_val_iff, mem_enlarged_iff_leftTrans ev V U hU hsurj hUV T hTV hT]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range, incl_apply]
  exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r r.2⟩

include hU hsurj hUV hnorm hTV hT in
/-- The comultiplication of an element of the enlarged algebra has its right leg in the
enlarged algebra. -/
theorem comul_mem_range_lTensor {b : A} (hb : b ∈ enlarged ev V) :
    Coalgebra.comul (R := R) b ∈
      LinearMap.range (LinearMap.lTensor A (enlarged ev V).val.toLinearMap) := by
  apply mem_range_lTensor_of_forall _ _ (forall_mkQ_rightTrans_iff ev V U hU hsurj hUV hnorm T hTV hT)
  intro r
  obtain ⟨c, hc⟩ := (mem_enlarged_iff_rightTrans ev V U hU hsurj hUV hnorm T hTV hT b).1 hb r r.2
  have h1 : LinearMap.lTensor A (rightTrans ev r).toLinearMap (Coalgebra.comul (R := R) b) =
      LinearMap.lTensor A incl (Coalgebra.comul (R := R) c) := by
    rw [← leftComm_symm_tmul_one, LinearEquiv.eq_symm_apply, leftComm_lTensor_rightTrans, ← hc,
      LinearMap.lTensor_tmul]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, h1,
    ← LinearMap.comp_apply (LinearMap.lTensor A _), ← LinearMap.lTensor_comp,
    LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]

include hU hsurj hUV hnorm hTV hT in
/-- **The comultiplication preserves the enlarged algebra.** -/
theorem comul_mem_range_ι₂ [Module.Flat R (enlarged ev V)] {b : A} (hb : b ∈ enlarged ev V) :
    Coalgebra.comul (R := R) b ∈ LinearMap.range (SubHopf.ι₂ (enlarged ev V)) := by
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  set B := enlarged ev V
  obtain ⟨c', hc'⟩ := comul_mem_range_lTensor ev V U hU hsurj hUV hnorm T hTV hT hb
  obtain ⟨c'', hc''⟩ : c' ∈ LinearMap.range (LinearMap.rTensor B B.val.toLinearMap) := by
    apply mem_range_rTensor_of_forall _ _ (forall_mkQ_leftTrans_iff ev V U hU hsurj hUV T hTV hT)
    intro r
    obtain ⟨c, hc⟩ := (mem_enlarged_iff_leftTrans ev V U hU hsurj hUV T hTV hT b).1 hb r r.2
    have hcB : c ∈ B := fun y hy => by
      rw [← evalExt_one_tmul, hc, evalExt_leftTrans]
      exact hb _ (V.mul_mem (hTV r r.2) hy)
    obtain ⟨d, hd⟩ := comul_mem_range_lTensor ev V U hU hsurj hUV hnorm T hTV hT hcB
    have hy : LinearMap.rTensor B (leftTrans ev r).toLinearMap c' =
        LinearMap.rTensor B incl d := by
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := K ⊗[R] A)
        B.val.toLinearMap Subtype.val_injective
      rw [← LinearMap.comp_apply (LinearMap.lTensor _ _), LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hc',
        ← LinearMap.comp_apply (LinearMap.lTensor _ _), LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hd, ← assoc_symm_tmul_one,
        LinearEquiv.eq_symm_apply, assoc_rTensor_leftTrans, ← hc, LinearMap.lTensor_tmul]
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hy,
      ← LinearMap.comp_apply (LinearMap.rTensor B _), ← LinearMap.rTensor_comp,
      LinearMap.range_mkQ_comp, LinearMap.rTensor_zero, LinearMap.zero_apply]
  refine ⟨c'', ?_⟩
  rw [← hc', ← hc'', ← LinearMap.comp_apply (LinearMap.lTensor _ _),
    LinearMap.lTensor_comp_rTensor]

omit [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K]
  [Algebra.Smooth R A] in
theorem flat_enlarged [Module.Flat R A] : Module.Flat R (enlarged ev V) := inferInstance

include hU hsurj hUV hnorm in
theorem comul_mem_range_ι₂_of_hasReps (hfin : HasReps U V) (x : enlarged ev V) :
    Coalgebra.comul (R := R) (x : A) ∈ LinearMap.range (SubHopf.ι₂ (enlarged ev V)) := by
  have := flat_enlarged ev V (R := R)
  obtain ⟨T, hTV, hT⟩ := hfin
  exact comul_mem_range_ι₂ ev V U hU hsurj hUV hnorm T hTV hT x.2

/-- The Hopf algebra structure of the enlarged algebra. -/
abbrev enlargedHopfAlgebra (hfin : HasReps U V) : HopfAlgebra R (enlarged ev V) :=
  haveI := flat_enlarged ev V (R := R)
  SubHopf.hopfAlgebra (enlarged ev V)
    (comul_mem_range_ι₂_of_hasReps ev V U hU hsurj hUV hnorm hfin)
    (fun x => antipode_mem_enlarged ev V x.2)

end Enlarged

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
