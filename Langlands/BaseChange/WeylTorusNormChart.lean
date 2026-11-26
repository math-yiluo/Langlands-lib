import Langlands.BaseChange.CyclicAlgebraTrace
import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.TwistedWeylOrbit
import Langlands.BaseChange.WeylTorusLie
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # The norm image in rational Weyl torus coordinates -/

noncomputable section

open Filter Set Topology
open scoped RightActions

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

namespace WeylTorus

variable {F : Type u} [Field F] {n : ℕ}
variable (T : WeylTorus F n) {γ : GeneralLinear n F}

local notation "MF" => Matrix (Fin n) (Fin n) F

/-- The affine matrix coordinate at the identity of the rational torus. -/
def affineCoordinate (hT : glCentralizer γ = T.val) (t : T.val) : weylTorusLie γ :=
  ⟨t.val.val - 1, (mem_ker_adjointDefect_iff γ _).mpr (by
    have hmem : t.val ∈ glCentralizer γ := hT.symm ▸ t.property
    rw [glCentralizer_eq_centralizer] at hmem
    exact (show Commute t.val.val γ.val from
      (show Commute t.val γ from Subgroup.mem_centralizer_singleton_iff.mp hmem).map
        (Units.coeHom _)).sub_left (Commute.one_left _))⟩

@[simp]
theorem affineCoordinate_one (hT : glCentralizer γ = T.val) :
    T.affineCoordinate hT 1 = 0 := by
  apply Subtype.ext
  exact sub_self _

theorem range_affineCoordinate (hT : glCentralizer γ = T.val) :
    range (T.affineCoordinate hT) = {x | IsUnit (1 + x.val : MF)} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change IsUnit (1 + (t.val.val - 1))
    simp
  · intro hx
    have hcomm : Commute (1 + x.val) γ.val :=
      (Commute.one_left _).add_left ((mem_ker_adjointDefect_iff γ _).mp x.property)
    have hmem : hx.unit ∈ T.val := by
      rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      simpa only [Units.val_mul, hx.unit_spec] using hcomm.eq
    refine ⟨⟨hx.unit, hmem⟩, Subtype.ext ?_⟩
    change hx.unit.val - 1 = x.val
    rw [hx.unit_spec]
    abel

variable [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]

theorem isOpenEmbedding_affineCoordinate (hT : glCentralizer γ = T.val) :
    IsOpenEmbedding (T.affineCoordinate hT) := by
  let : Module.Finite F MF := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  let : IsModuleTopology F MF := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → F))
  have hv := finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := MF)
  have he : IsEmbedding (fun t : T.val => t.val.val - 1) :=
    (Homeomorph.subRight (1 : MF)).isEmbedding.comp
      (hv.isEmbedding.comp IsEmbedding.subtypeVal)
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.mp he, ?_⟩
  rw [T.range_affineCoordinate hT]
  exact hv.isOpen_range.preimage (continuous_const.add continuous_subtype_val)

end WeylTorus

section StrictDerivative

variable {K X R : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup X] [NormedSpace K X] [NormedRing R] [NormedAlgebra K R]

/-- The derivative of an ordered product of maps taking value one at the
center is the sum of their derivatives. -/
theorem hasStrictFDerivAt_listRange_prod_at_one
    (g : ℕ → X → R) (D : ℕ → X →L[K] R) (l : ℕ)
    (hg : ∀ k, HasStrictFDerivAt (g k) (D k) 0) (h₀ : ∀ k, g k 0 = 1) :
    HasStrictFDerivAt (fun x => ((List.range l).map fun i => g i x).prod)
      (∑ i ∈ Finset.range l, D i) 0 := by
  induction l with
  | zero => simpa using (hasStrictFDerivAt_const (𝕜 := K) (1 : R) (0 : X))
  | succ l ih =>
    rw [Finset.sum_range_succ]
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    convert ih.mul' (hg l) using 1
    ext x
    simp [h₀, List.prod_replicate, add_comm]

private theorem strictDerivative_listRange_prod_one_add_at
    (A : ℕ → X →L[K] R) (l : ℕ) (a : X) :
    ∃ D : X →L[K] R,
      HasStrictFDerivAt (fun x => ((List.range l).map fun i => 1 + A i x).prod) D a := by
  induction l with
  | zero => exact ⟨0, hasStrictFDerivAt_const (𝕜 := K) (1 : R) a⟩
  | succ l ih =>
    obtain ⟨D, hD⟩ := ih
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    exact ⟨_, hD.mul' ((A l).hasStrictFDerivAt.const_add (c := (1 : R)))⟩

private theorem contDiff_listRange_prod_one_add
    (A : ℕ → X →L[K] R) (l : ℕ) :
    ContDiff K 1 (fun x => ((List.range l).map fun i => 1 + A i x).prod) := by
  induction l with
  | zero => exact contDiff_const
  | succ l ih =>
    simpa only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton] using ih.mul (contDiff_const.add (A l).contDiff)

end StrictDerivative

namespace WeylTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  (T : WeylTorus F n) {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E

include hσ in
/-- The affine norm from a trace-one direction gives a partial
homeomorphism in rational Lie coordinates with a strictly differentiable
inverse at every point of its target. -/
theorem exists_affineNormChart {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    (hT : glCentralizer γ = T.val) :
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : CompleteSpace F := LocalGalois.localNormedField_complete F
    letI : Module.Finite F E := hσ.1
    letI : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
    letI : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
    letI : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
    letI : NormedRing ME := finiteAlgebraNormedRing F ME
    letI : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
    ∃ (L : weylTorusLie γ →L[F] ME)
      (e : OpenPartialHomeomorph (weylTorusLie γ) (weylTorusLie γ)),
      0 ∈ e.source ∧ e 0 = 0 ∧
      (∀ x ∈ e.source, ∃ d : T.points E,
        d.val.val = 1 + L x ∧ e x = T.affineCoordinate hT (T.normToRational hσ d)) ∧
      (∀ y ∈ e.target, ∃ D : weylTorusLie γ →L[F] weylTorusLie γ,
        HasStrictFDerivAt e.symm D y) := by
  classical
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  let : IsReduced E := hσ.2.2.1
  let : Module.Finite F MF := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  let : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
  let : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
  let : NormedRing ME := finiteAlgebraNormedRing F ME
  let : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
  let : CompleteSpace ME := FiniteDimensional.complete F ME
  have htγ : γ ∈ T.val := by
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  let tγ : T.val := ⟨γ, htγ⟩
  have hpoints := T.points_eq_centralizer (E := E) (γ := tγ) hγ
  let S := weylTorusLie γ
  let : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  let : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  let : CompleteSpace S := FiniteDimensional.complete F S
  let i : S →ₗ[F] ME := weylTorusLieInclusion γ
  have hi : Function.Injective i :=
    matrixBaseChangeLinear_injective.comp Subtype.val_injective
  obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let P : ME →L[F] S := p.toContinuousLinearMap
  obtain ⟨c, hc⟩ := hσ.exists_cyclic_sum_eq_one
  let a : ℕ → S →L[F] ME := fun k =>
    (((σ ^ k) c) • i.toContinuousLinearMap :
      S →L[F] ME)
  let raw : S → ME := fun x => ((List.range l).map fun k => 1 + a k x).prod
  let f : S → S := fun x => P (raw x - 1)
  have hsum : (∑ k ∈ Finset.range l, a k) = i.toContinuousLinearMap := by
    ext x p q
    change (∑ k ∈ Finset.range l, a k) x p q = i x p q
    rw [_root_.sum_apply, Matrix.sum_apply, Finset.sum_range]
    change (∑ k : Fin l, (σ ^ (k : ℕ)) c * i x p q) = i x p q
    rw [← Finset.sum_mul, hc, one_mul]
  have hraw : HasStrictFDerivAt raw i.toContinuousLinearMap 0 :=
    hsum ▸ hasStrictFDerivAt_listRange_prod_at_one
      (fun k x => 1 + a k x) a l (fun k => (a k).hasStrictFDerivAt.const_add (c := (1 : ME)))
      (by simp)
  have hderiv : HasStrictFDerivAt f (ContinuousLinearMap.id F S) 0 := by
    convert P.hasStrictFDerivAt.comp (0 : S) (hraw.sub_const (1 : ME)) using 1
    apply ContinuousLinearMap.ext
    intro x
    exact (DFunLike.congr_fun hp x).symm
  have hfzero : f 0 = 0 := by
    simp [f, raw, List.prod_replicate]
  let U : Set S := {x | IsUnit (1 + a 0 x)}
  have hnorm (x : S) (hx : x ∈ U) :
      ∃ d : T.points E, d.val.val = 1 + a 0 x ∧
        f x = T.affineCoordinate hT (T.normToRational hσ d) := by
    have hu : IsUnit (1 + a 0 x) := hx
    have hcomm : Commute (1 + a 0 x) (baseChange F E n γ).val := by
      have ha₀ : a 0 x = c • weylTorusLieInclusion γ x := by
        simp only [a, pow_zero, AlgEquiv.one_apply]
        rfl
      rw [ha₀]
      exact (Commute.one_left _).add_left
        ((weylTorusLieInclusion_commutes (E := E) γ x).smul_left c)
    have hd : hu.unit ∈ T.points E := by
      rw [hpoints, Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      simpa only [Units.val_mul, hu.unit_spec] using hcomm.eq
    let d : T.points E := ⟨hu.unit, hd⟩
    have hval (k : ℕ) : (entrywiseAut (σ ^ k) n d.val).val = 1 + a k x := by
      change matrixEntrywiseAut (σ ^ k) hu.unit.val = _
      rw [hu.unit_spec, map_add, map_one]
      congr 1
      ext j j'
      change (σ ^ k) ((σ ^ 0) c * (i x) j j') = (σ ^ k) c * (i x) j j'
      simp only [map_mul, pow_zero, AlgEquiv.one_apply]
      exact congrArg ((σ ^ k) c * ·) ((σ ^ k).commutes (x.val j j'))
    have hraw' (k : ℕ) : ((List.range k).map fun j => 1 + a j x).prod =
        (cyclicNorm σ k d.val).val := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, ih, cyclicNorm_succ, Units.val_mul, hval]
    refine ⟨d, hu.unit_spec, ?_⟩
    let y := T.affineCoordinate hT (T.normToRational hσ d)
    have hy : i y = raw x - 1 := by
      change matrixBaseChangeLinear (((T.normToRational hσ d).val).val - 1) = _
      dsimp only [raw]
      rw [map_sub, hraw' l]
      have h := congrArg (fun z : GeneralLinear n E => z.val) (T.baseChange_normToRational hσ d)
      exact congrArg₂ (· - ·) h (map_one (algebraMap F E).mapMatrix)
    exact (congrArg P hy).symm.trans (DFunLike.congr_fun hp y)
  have hstrict (x : S) : HasStrictFDerivAt f (fderiv F f x) x := by
    obtain ⟨D, hD⟩ := strictDerivative_listRange_prod_one_add_at a l x
    have hh : HasStrictFDerivAt f (P.comp D) x :=
      P.hasStrictFDerivAt.comp x (hD.sub_const (1 : ME))
    rw [hh.hasFDerivAt.fderiv]
    exact hh
  have hC : ContDiff F 1 f :=
    P.contDiff.comp ((contDiff_listRange_prod_one_add a l).sub contDiff_const)
  let V : Set S := U ∩ (fderiv F f) ⁻¹' {D | ContinuousLinearMap.IsInvertible D}
  have hV : IsOpen V := (Units.isOpen.preimage (continuous_const.add (a 0).continuous)).inter
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage (hC.continuous_fderiv one_ne_zero))
  have h0V : (0 : S) ∈ V := by
    refine ⟨by simp [U], ?_⟩
    change (fderiv F f 0).IsInvertible
    rw [hderiv.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl F S)
  have hd : HasStrictFDerivAt f ((ContinuousLinearEquiv.refl F S : S ≃L[F] S) : S →L[F] S) 0 :=
    hderiv
  let e₀ := hd.toOpenPartialHomeomorph f
  let e := e₀.restrOpen V hV
  refine ⟨a 0, e, ⟨hd.mem_toOpenPartialHomeomorph_source, h0V⟩, hfzero, ?_, ?_⟩
  · intro x hx
    exact hnorm x hx.2.1
  · intro y hy
    have hy' := e.map_target hy
    obtain ⟨D, hD⟩ : ContinuousLinearMap.IsInvertible (fderiv F f (e.symm y)) := hy'.2.2
    have hh : HasStrictFDerivAt e (D : S →L[F] S) (e.symm y) := hD ▸ hstrict (e.symm y)
    exact ⟨D.symm, e.hasStrictFDerivAt_symm hy hh⟩

include hσ in
/-- The norm image contains a neighborhood of the identity. -/
theorem normImage_mem_nhds_one : T.normImage σ l ∈ 𝓝 (1 : T.val) := by
  let : Module.Finite F E := hσ.1
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
  let : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
  let : NormedRing ME := finiteAlgebraNormedRing F ME
  let : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
  let : CompleteSpace ME := FiniteDimensional.complete F ME
  obtain ⟨γ, hγ, hT⟩ := T.property
  obtain ⟨_, e, h₀, he₀, hlift, _⟩ := T.exists_affineNormChart hσ hγ hT
  have htarget : (0 : weylTorusLie γ) ∈ e.target := he₀ ▸ e.map_source h₀
  have he : Continuous (T.affineCoordinate hT) := (T.isOpenEmbedding_affineCoordinate hT).continuous
  have hpre : (T.affineCoordinate hT) ⁻¹' e.target ∈ 𝓝 (1 : T.val) :=
    (he.tendsto' 1 0 (T.affineCoordinate_one hT)).eventually (e.open_target.mem_nhds htarget)
  filter_upwards [hpre] with t ht
  have ht' : T.affineCoordinate hT t ∈ e.target := ht
  obtain ⟨d, _, hd⟩ := hlift _ (e.map_target ht')
  rw [e.right_inv ht'] at hd
  have htd := (T.isOpenEmbedding_affineCoordinate hT).injective hd
  exact ⟨d, (T.baseChange_normToRational hσ d).symm.trans
    (congrArg (fun z : T.val => baseChange F E n z.val) htd.symm)⟩

include hσ in
/-- The image of the torus norm is open in every characteristic. -/
theorem isOpen_normImage : IsOpen (T.normImage σ l) := by
  let H := (T.normToRational hσ).range
  have hH : (H : Set T.val) = T.normImage σ l := T.range_normToRational hσ
  rw [← hH]
  exact H.isOpen_of_mem_nhds (hH ▸ T.normImage_mem_nhds_one hσ)

include hσ in
/-- The regular norm domain of the twisted Weyl map is open. -/
theorem isOpen_regularNormPoints : IsOpen (T.regularNormPoints σ l) :=
  ((regularSemisimpleOpenConull F n).1.preimage continuous_subtype_val).inter
    (T.isOpen_normImage hσ)

end WeylTorus
end Langlands.BaseChange
