import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness

/-! # Missing ordinary directions and doubled-root cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- No ordinary affine root has the given actual relative-root form as derivative. -/
def HasNoOrdinaryRootDirection (a : relativeRoots B.i) : Prop :=
  ∀ ψ ∈ B.affineRoots, ψ.linear ≠ rootForm B.i a

/-- V 4: `U_{2a,x,2r} ⊆ U_{a,x,r}`. -/
theorem filtration_two_smul_le {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i) (x : B.Apartment) (r : ℝ) :
    B.filtration x (2 • (a : characterLattice B.S)) (2 * r) ≤ B.filtration x a r := by
  intro v hv
  rw [KPApartmentData.mem_filtration] at hv ⊢
  refine ⟨RelativeRoot.double_subgroup_le B.i a (Over.mk (𝟙 _)) hv.1, ?_⟩
  have hd := hv.2
  rw [x.isValuation.double a a.property h2a v hv.1, two_nsmul] at hd
  induction hval : x.val a v using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hval, ← WithTop.coe_add, WithTop.coe_le_coe] at hd
    rw [WithTop.coe_le_coe]
    linarith

/-- One step of KP Lemma 6.3.9. If no affine root has derivative `a`, then every
`u ∈ U_a(F) ∖ {1}` is a product `u' w` with `x_a(u') > x_a(u)` and `w ∈ U_{2a,x,2x_a(u)}`. -/
theorem exists_mul_of_forall_not_mem_affineRoots {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (hno : B.HasNoOrdinaryRootDirection a)
    {u : rationalPoints G} (hu : u ∈ B.rootGroup a) (hu1 : u ≠ 1) (x : B.Apartment) :
    ∃ u' w : rationalPoints G, u' * w = u ∧ u' ∈ B.rootGroup a ∧
      ((B.reflectionFunctional a u x : ℝ) : WithTop ℝ) < x.val a u' ∧
      w ∈ B.filtration x (2 • (a : characterLattice B.S))
        (2 * B.reflectionFunctional a u x) := by
  have hlin : (B.reflectionFunctional a u).linear = rootForm B.i a :=
    B.reflectionFunctional_linear a u
  have hψ : B.reflectionFunctional a u ∉ B.affineRoots := fun h => hno _ h hlin
  have huψ : u ∈ B.apartment.affineRootGroup a (B.reflectionFunctional a u) :=
    (KPApartmentData.mem_affineRootGroup_iff hlin x).2
      ⟨hu, (B.coe_reflectionFunctional_apply hu hu1 x).le⟩
  obtain ⟨u', hu', w, hw, huw⟩ :=
    B.apartment.affineRootGroup_subset_mul_double_of_not_mem_affineRoots h2a hlin hψ huψ
  have hlin2 : ((2 : ℝ) • B.reflectionFunctional a u).linear =
      rootForm B.i ⟨2 • (a : characterLattice B.S), h2a⟩ := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul a.property 2 h2a]
    norm_num
  have hu'' := (KPApartmentData.mem_affineRootGroupPlus_iff hlin x).1 hu'
  have hw' := (KPApartmentData.mem_affineRootGroup_iff hlin2 x).1 hw
  refine ⟨u', w, huw, hu''.1, hu''.2, hw'.1, ?_⟩
  simpa only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] using hw'.2

/-- If no affine root has derivative `a`, then every `u ∈ U_{a,x,r}` can be moved into
`U_{a,x,s}`, for every `s`, by right multiplication with an element of `U_{2a,x,2r}`. This is
the iteration in the proof of KP Lemma 6.3.9; it terminates by the discreteness of the jumps
(KP Proposition 6.3.7). -/
theorem exists_mul_inv_mem_filtration_of_forall_not_mem_affineRoots {a : relativeRoots B.i}
    (h2a : 2 • (a : characterLattice B.S) ∈ relativeRoots B.i)
    (hno : B.HasNoOrdinaryRootDirection a)
    (x : B.Apartment) {r : ℝ} {u : rationalPoints G} (hu : u ∈ B.filtration x a r) (s : ℝ) :
    ∃ v ∈ B.filtration x (2 • (a : characterLattice B.S)) (2 * r),
      u * v⁻¹ ∈ B.filtration x a s := by
  by_contra hcon
  push Not at hcon
  set K := B.filtration x (2 • (a : characterLattice B.S)) (2 * r) with hKdef
  have hK : ∀ v ∈ K, u * v⁻¹ ∈ B.filtration x a r := fun v hv =>
    (B.filtration x a r).mul_mem hu
      ((B.filtration x a r).inv_mem (B.filtration_two_smul_le h2a x r hv))
  have hne : ∀ v ∈ K, u * v⁻¹ ≠ 1 := fun v hv h1 =>
    hcon v hv (h1 ▸ (B.filtration x a s).one_mem)
  have hmemU : ∀ v ∈ K, u * v⁻¹ ∈ B.rootGroup a := fun v hv =>
    B.filtration_le_rootGroup x a r (hK v hv)
  -- the value of `u v⁻¹` lies in `[r, s)`
  have hval : ∀ v ∈ K, r ≤ B.reflectionFunctional a (u * v⁻¹) x ∧
      B.reflectionFunctional a (u * v⁻¹) x < s := by
    intro v hv
    have he := B.coe_reflectionFunctional_apply (hmemU v hv) (hne v hv) x
    constructor
    · have h := (KPApartmentData.mem_filtration.1 (hK v hv)).2
      rw [← he] at h
      exact_mod_cast h
    · by_contra hge
      push Not at hge
      apply hcon v hv
      refine KPApartmentData.mem_filtration.2 ⟨hmemU v hv, ?_⟩
      rw [← he]
      exact_mod_cast hge
  let T : Set ℝ := {t | ∃ v ∈ K, B.reflectionFunctional a (u * v⁻¹) x = t}
  have hTfin : T.Finite := by
    refine ((B.finite_bounded_reflectionFunctionals_of_oppositePairs B.hasOppositeFactorPairs a
      x (|r| + |s|)).image fun ψ => ψ x).subset ?_
    rintro t ⟨v, hv, rfl⟩
    refine ⟨_, ⟨u * v⁻¹, hmemU v hv, hne v hv, rfl, ?_⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hval v hv
    rw [abs_le]
    constructor <;> linarith [neg_abs_le r, le_abs_self s, abs_nonneg r, abs_nonneg s]
  have hTne : T.Nonempty := ⟨_, 1, K.one_mem, rfl⟩
  obtain ⟨t, ⟨v, hv, rfl⟩, hmax⟩ := Set.exists_max_image T id hTfin hTne
  obtain ⟨u', w, huw, hu', hlt, hw⟩ :=
    B.exists_mul_of_forall_not_mem_affineRoots h2a hno (hmemU v hv) (hne v hv) x
  have hwK : w * v ∈ K := by
    refine K.mul_mem ?_ hv
    refine KPApartmentData.filtration_antitone x _ ?_ hw
    have := (hval v hv).1
    linarith
  have heq : u * (w * v)⁻¹ = u' := by
    rw [mul_inv_rev, ← mul_assoc, ← huw, mul_inv_cancel_right]
  have hT' : B.reflectionFunctional a u' x ∈ T := ⟨w * v, hwK, by rw [heq]⟩
  have hle : B.reflectionFunctional a u' x ≤ B.reflectionFunctional a (u * v⁻¹) x :=
    hmax _ hT'
  have hu'1 : u' ≠ 1 := heq ▸ hne _ hwK
  have he := B.coe_reflectionFunctional_apply hu' hu'1 x
  rw [← he] at hlt
  have hlt' : B.reflectionFunctional a (u * v⁻¹) x < B.reflectionFunctional a u' x := by
    exact_mod_cast hlt
  linarith

end Langlands.Geometry.Building.IntegerValuationBuildingData
