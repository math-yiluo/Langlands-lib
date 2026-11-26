import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.BaseChange.WeylTorusNormImage

/-! # Matrix coordinates on a Weyl torus and its scalar extension -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E

/-- Scalar extension of matrices as a linear map over the base field. -/
abbrev matrixBaseChangeLinear : MF →ₗ[F] ME :=
  (Algebra.linearMap F E).mapMatrix

/-- Entrywise action on matrices as an algebra automorphism over the base field. -/
abbrev matrixEntrywiseAut (σ : E ≃ₐ[F] E) : ME ≃ₐ[F] ME :=
  σ.mapMatrix

/-- The Lie algebra of the torus centralizing a regular matrix. -/
abbrev weylTorusLie (γ : GeneralLinear n F) : Submodule F MF :=
  (adjointDefect γ).ker

/-- The scalar-extended inclusion of the rational torus Lie algebra. -/
abbrev weylTorusLieInclusion (γ : GeneralLinear n F) : weylTorusLie γ →ₗ[F] ME :=
  matrixBaseChangeLinear.comp (weylTorusLie γ).subtype

theorem matrixBaseChangeLinear_injective [Nontrivial E] :
    Function.Injective (matrixBaseChangeLinear : MF →ₗ[F] ME) := by
  intro A B h
  exact Matrix.ext fun i j =>
    (algebraMap F E).injective (congrArg (fun C : ME => C i j) h)

theorem matrixEntrywiseAut_baseChange (σ : E ≃ₐ[F] E) (A : MF) :
    matrixEntrywiseAut σ (matrixBaseChangeLinear A) =
      (matrixBaseChangeLinear A : ME) := by
  ext i j
  exact σ.commutes (A i j)

theorem weylTorusLieInclusion_commutes (γ : GeneralLinear n F) (X : weylTorusLie γ) :
    Commute (weylTorusLieInclusion (E := E) γ X) (baseChange F E n γ).val :=
  ((mem_ker_adjointDefect_iff γ X).mp X.property).map (algebraMap F E).mapMatrix

/-- Every exact lift at a regular torus point commutes with the Lie algebra
of the scalar-extended torus. -/
theorem WeylTorus.commute_weylTorusLieInclusion
    (T : WeylTorus F n) {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    {t : T.val} (ht : t ∈ T.regularPoints) (δ : T.points E) (X : weylTorusLie t.val) :
    Commute δ.val.val (weylTorusLieInclusion t.val X) := by
  let : Module.Finite F E := hσ.1
  let : IsReduced E := hσ.2.2.1
  obtain ⟨v, hv⟩ := regularCyclicBasis F n t.val.val ht
  have hvE : IsUnit (cyclicBasisMatrix (baseChange F E n t.val).val (algebraMap F E ∘ v)) := by
    change IsUnit (cyclicBasisMatrix (t.val.val.map (algebraMap F E)) (algebraMap F E ∘ v))
    rw [← cyclicBasisMatrix_map]
    exact hv.map (algebraMap F E).mapMatrix
  have hδ : Commute δ.val (baseChange F E n t.val) := by
    have hm : δ.val ∈ Subgroup.centralizer {baseChange F E n t.val} :=
      (T.points_eq_centralizer (E := E) ht) ▸ δ.property
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  exact commute_of_commute_cyclicBasisMatrix hvE (hδ.map (Units.coeHom _))
    (weylTorusLieInclusion_commutes t.val X)

/-- An invertible matrix whose entries are fixed by the generator descends
to an invertible matrix over the base, also for a product algebra. -/
theorem IsCyclicAlgebra.exists_baseChange_of_fixed
    {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    {a : GeneralLinear n E} (ha : entrywiseAut σ n a = a) :
    ∃ b : GeneralLinear n F, baseChange F E n b = a := by
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  have descend (x : GeneralLinear n E) (hx : entrywiseAut σ n x = x) :
      ∃ X : MF, (algebraMap F E).mapMatrix X = x.val := by
    have hentry (i j : Fin n) : x.val i j ∈ (algebraMap F E).range :=
      hσ.2.2.2.2 _ (congrArg (fun g : GeneralLinear n E => g.val i j) hx)
    choose c hc using hentry
    exact ⟨c, Matrix.ext hc⟩
  obtain ⟨b, hb⟩ := descend a ha
  obtain ⟨b', hb'⟩ := descend a⁻¹ (by rw [map_inv, ha])
  let f : MF →+* ME := (algebraMap F E).mapMatrix
  have hinj : Function.Injective f := matrixBaseChangeLinear_injective
  have hmul : b * b' = 1 := hinj (by rw [map_mul, hb, hb', map_one]; exact a.val_inv)
  have hmul' : b' * b = 1 := hinj (by rw [map_mul, hb', hb, map_one]; exact a.inv_val)
  exact ⟨⟨b, b', hmul, hmul'⟩, Units.ext hb⟩

namespace WeylTorus

variable (T : WeylTorus F n) {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)

/-- An entrywise coefficient automorphism preserves the extended torus. -/
theorem entrywiseAut_mem_points (a : E ≃ₐ[F] E) (d : T.points E) :
    entrywiseAut a n d.val ∈ T.points E := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨t, ht, rfl⟩
  have he := congrArg (entrywiseAut a n)
    (Subgroup.mem_centralizer_iff.mp d.property _ ⟨t, ht, rfl⟩)
  simpa only [map_mul, entrywiseAut_baseChange] using he

/-- The extended torus is commutative. -/
theorem points_commute [Module.Finite F E] [IsReduced E] (a b : T.points E) :
    Commute a.val b.val := by
  obtain ⟨γ, hγ, hT⟩ := T.property
  have hmem : baseChange F E n γ ∈ T.val.map (baseChange F E n) := by
    refine ⟨γ, ?_, rfl⟩
    change γ ∈ T.val
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  have ha := Subgroup.mem_centralizer_iff.mp a.property _ hmem
  have hb := Subgroup.mem_centralizer_iff.mp b.property _ hmem
  exact commute_of_commute_baseChange hγ ha.symm hb.symm

/-- Each ordered partial norm of a point of the extended torus
is again a point of that torus. -/
theorem cyclicNorm_mem_points (d : T.points E) (k : ℕ) :
    cyclicNorm σ k d.val ∈ T.points E := by
  induction k with
  | zero => simp
  | succ k ih => rw [cyclicNorm_succ]; exact mul_mem ih (T.entrywiseAut_mem_points (σ ^ k) d)

include hσ in
/-- The norm of an extended torus point lies in the rational torus. -/
theorem exists_cyclicNorm_eq (δ : T.points E) :
    ∃ t : T.val, cyclicNorm σ l δ.val = baseChange F E n t.val := by
  let : Module.Finite F E := hσ.1
  let : IsReduced E := hσ.2.2.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  obtain ⟨γ, hγ, hT⟩ := T.property
  have htγ : γ ∈ T.val := by
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  have hpoints := T.points_eq_centralizer (E := E) (γ := ⟨γ, htγ⟩) hγ
  have hδ : Commute δ.val (baseChange F E n γ) := by
    have hm : δ.val ∈ Subgroup.centralizer {baseChange F E n γ} :=
      hpoints ▸ δ.property
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have hN k : Commute (cyclicNorm σ k δ.val) (baseChange F E n γ) := by
    induction k with
    | zero => exact Commute.one_left _
    | succ k ih =>
      rw [cyclicNorm_succ]
      exact ih.mul_left (by
        simpa only [entrywiseAut_baseChange] using hδ.map (entrywiseAut (σ ^ k) n))
  have hcomm := commute_of_commute_baseChange hγ (hN l) hδ
  have hfixed : entrywiseAut σ n (cyclicNorm σ l δ.val) = cyclicNorm σ l δ.val := by
    rw [entrywiseAut_cyclicNorm, hσ.pow_eq_one, entrywiseAut_one_apply,
      hcomm.symm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨t, ht⟩ := hσ.exists_baseChange_of_fixed hfixed
  have hmem : t ∈ T.val := by
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hinj : Function.Injective (baseChange F E n) := fun _ _ h =>
      Units.ext (matrixBaseChangeLinear_injective (congrArg Units.val h))
    apply hinj
    rw [map_mul, map_mul, ht]
    exact (hN l).eq
  exact ⟨⟨t, hmem⟩, ht.symm⟩

/-- The cyclic norm restricted to an extended Weyl torus, with codomain the
rational point group. -/
def normToRational : T.points E →* T.val where
  toFun d := (T.exists_cyclicNorm_eq hσ d).choose
  map_one' := by
    let : Module.Finite F E := hσ.1
    let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
    apply Subtype.ext
    have h := (T.exists_cyclicNorm_eq hσ (1 : T.points E)).choose_spec
    have h1 (k : ℕ) : cyclicNorm σ k (1 : GeneralLinear n E) = 1 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [cyclicNorm_succ, ih]
    change cyclicNorm σ l 1 = baseChange F E n _ at h
    rw [h1] at h
    apply Units.ext
    apply matrixBaseChangeLinear_injective (E := E)
    exact congrArg Units.val (h.symm.trans (map_one (baseChange F E n)).symm)
  map_mul' a b := by
    let : Module.Finite F E := hσ.1
    let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
    let : IsReduced E := hσ.2.2.1
    have hm (k : ℕ) : cyclicNorm σ k (a * b).val =
        cyclicNorm σ k a.val * cyclicNorm σ k b.val := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [cyclicNorm_succ, cyclicNorm_succ, cyclicNorm_succ, ih]
        change (_ * _) * entrywiseAut (σ ^ k) n (a.val * b.val) = _
        rw [map_mul]
        exact (T.points_commute
          ⟨_, T.cyclicNorm_mem_points (σ := σ) b k⟩
          ⟨_, T.entrywiseAut_mem_points (σ ^ k) a⟩).mul_mul_mul_comm _ _
    have ha := (T.exists_cyclicNorm_eq hσ a).choose_spec
    have hb := (T.exists_cyclicNorm_eq hσ b).choose_spec
    have hab := (T.exists_cyclicNorm_eq hσ (a * b)).choose_spec
    apply Subtype.ext
    apply Units.ext
    apply matrixBaseChangeLinear_injective (E := E)
    exact congrArg (fun g : GeneralLinear n E => g.val) (hab.symm.trans ((hm l).trans
      ((congrArg₂ (· * ·) ha hb).trans (map_mul (baseChange F E n) _ _).symm)))

/-- The rational norm map has the same ordered norm as the ambient map. -/
theorem baseChange_normToRational (d : T.points E) :
    baseChange F E n (T.normToRational hσ d).val = cyclicNorm σ l d.val :=
  (T.exists_cyclicNorm_eq hσ d).choose_spec.symm

/-- The range of the rational norm map is the Weyl norm image. -/
theorem range_normToRational : Set.range (T.normToRational hσ) = T.normImage σ l := by
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  ext t
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, (T.baseChange_normToRational hσ d).symm⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, Subtype.ext (Units.ext ?_)⟩
    exact matrixBaseChangeLinear_injective
      (congrArg Units.val ((T.baseChange_normToRational hσ d).trans hd))

end WeylTorus
end Langlands.BaseChange
