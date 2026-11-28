import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution
import Mathlib.Topology.LocallyClosed

/-!
# Conjugacy orbits in finite-dimensional topological algebras

The rank of the intertwining operator `z ↦ X * z - z * N` gives local
closedness of the orbit of `N`. A continuous local correction of an
intertwiner gives openness of the orbit map. Inversion then gives the
homeomorphism from left cosets used by `OrbitalDistribution`.
-/

noncomputable section

open Filter Matrix Module Set Topology

namespace Langlands.HarmonicAnalysis.UnitConjugation

open QuotientIntegration

universe u v

section Rank

variable {F E V S : Type*} [Field F]
  [AddCommGroup E] [Module F E] [AddCommGroup V] [Module F V]

private theorem exists_rankCompression (t : E →ₗ[F] V) :
    ∃ i : LinearMap.range t →ₗ[F] E, ∃ p : V →ₗ[F] LinearMap.range t,
      p ∘ₗ t ∘ₗ i = LinearMap.id := by
  obtain ⟨i, hi⟩ := t.rangeRestrict.exists_rightInverse_of_surjective t.range_rangeRestrict
  obtain ⟨p, hp⟩ := (LinearMap.range t).subtype.exists_leftInverse_of_injective
    (LinearMap.range t).ker_subtype
  refine ⟨i, p, LinearMap.ext fun y => ?_⟩
  have hiy : t.rangeRestrict (i y) = y := LinearMap.congr_fun hi y
  change p ((LinearMap.range t).subtype (t.rangeRestrict (i y))) = y
  rw [hiy]
  exact LinearMap.congr_fun hp y

variable [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [TopologicalSpace V] [IsModuleTopology F V] [TopologicalSpace S]

private theorem continuous_compressionMatrix (T : S → E →ₗ[F] V)
    (hT : ∀ z, Continuous fun x => T x z) {B : Type*} [AddCommGroup B] [Module F B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι F B)
    (i : B →ₗ[F] E) (p : V →ₗ[F] B) :
    Continuous (fun x => LinearMap.toMatrix b b (p ∘ₗ T x ∘ₗ i)) := by
  apply continuous_matrix
  intro j k
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply]
  exact (IsModuleTopology.continuous_of_linearMap ((b.coord j).comp p)).comp (hT (i (b k)))

variable [T1Space F] [Module.Finite F V] [TopologicalSpace E] [IsModuleTopology F E]

private theorem exists_continuousAt_kernelSection (T : S → E →ₗ[F] V)
    (hT : ∀ z, Continuous fun x => T x z) (a : S) (z : E) (hz : T a z = 0) :
    ∃ f : S → E, f a = z ∧ ContinuousAt f a ∧
      ∀ᶠ x in 𝓝 a,
        finrank F (LinearMap.range (T a)) ≤ finrank F (LinearMap.range (T x)) ∧
        (finrank F (LinearMap.range (T x)) = finrank F (LinearMap.range (T a)) →
          T x (f x) = 0) := by
  let : IsTopologicalAddGroup E := IsModuleTopology.isTopologicalAddGroup F E
  let B := LinearMap.range (T a)
  obtain ⟨i, p, hip⟩ := exists_rankCompression (T a)
  let b := Module.finBasis F B
  let M x := LinearMap.toMatrix b b (p ∘ₗ T x ∘ₗ i)
  let w x := b.equivFun (p (T x z))
  let j := i.comp b.equivFun.symm.toLinearMap
  let f x := z - j ((M x)⁻¹ *ᵥ w x)
  have hM : Continuous M := continuous_compressionMatrix T hT b i p
  have hMa : M a = 1 := by simp [M, hip]
  have hw : Continuous w :=
    (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.comp p)).comp (hT z)
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap j
  refine ⟨f, by simp [f, w, hz], ?_, ?_⟩
  · have hInv : ContinuousAt (fun x => (M x)⁻¹) a := by
      apply (continuousAt_matrix_inv _ ?_).comp hM.continuousAt
      rw [Ring.inverse_eq_inv', hMa, Matrix.det_one]
      exact continuousAt_inv₀ one_ne_zero
    have hmul : Continuous (fun q : Matrix (Fin (finrank F B)) (Fin (finrank F B)) F ×
        (Fin (finrank F B) → F) => q.1 *ᵥ q.2) :=
      continuous_fst.matrix_mulVec continuous_snd
    exact continuousAt_const.sub
      (hj.continuousAt.comp (hmul.continuousAt.comp (hInv.prodMk hw.continuousAt)))
  · have hdet : ∀ᶠ x in 𝓝 a, (M x).det ≠ 0 := by
      apply (isOpen_compl_singleton.preimage hM.matrix_det).mem_nhds
      simp [hMa]
    filter_upwards [hdet] with x hx
    let p' := p.comp (LinearMap.range (T x)).subtype
    have hs : Function.Surjective (p ∘ₗ T x ∘ₗ i) := by
      have hu := (Matrix.isUnit_iff_isUnit_det (M x)).2 (isUnit_iff_ne_zero.2 hx)
      exact LinearMap.range_eq_top.1
        ((LinearMap.isUnit_iff_range_eq_top _).mp ((LinearMap.isUnit_toMatrix_iff b).mp hu))
    have hp' : Function.Surjective p' := by
      intro y
      obtain ⟨r, hr⟩ := hs y
      exact ⟨⟨T x (i r), LinearMap.mem_range_self _ _⟩, hr⟩
    refine ⟨LinearMap.finrank_le_finrank_of_surjective hp', fun hdim => ?_⟩
    have hi' : Function.Injective p' :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hp'
    have hcoord (v : Fin (finrank F B) → F) :
        b.equivFun (p (T x (i (b.equivFun.symm v)))) = M x *ᵥ v := by
      simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, M,
        LinearMap.comp_apply] using
        (LinearMap.toMatrix_mulVec_repr b b (p ∘ₗ T x ∘ₗ i) (b.equivFun.symm v)).symm
    have hzero : p (T x (f x)) = 0 := by
      apply b.equivFun.injective
      simp only [f, j, map_sub, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero]
      rw [hcoord]
      change w x - M x *ᵥ ((M x)⁻¹ *ᵥ w x) = 0
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hx),
        Matrix.one_mulVec, sub_self]
    have hEq : p' ⟨T x (f x), LinearMap.mem_range_self _ _⟩ = p' 0 := by simpa [p'] using hzero
    exact congrArg Subtype.val (hi' hEq)

private theorem isClosed_finrank_range_le (T : S → E →ₗ[F] V)
    (hT : ∀ z, Continuous fun x => T x z) (r : ℕ) :
    IsClosed {x | finrank F (LinearMap.range (T x)) ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨_, _, _, h⟩ := exists_continuousAt_kernelSection T hT x 0 (map_zero _)
  exact h.mono fun _ hy hy' => hx (hy.1.trans hy')

end Rank

section Orbits

variable (F : Type u) {A : Type v} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [T1Space F] [Ring A] [Algebra F A] [Module.Finite F A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A]

private def intertwiningMap (N X : A) : A →ₗ[F] A :=
  LinearMap.mulLeft F X - LinearMap.mulRight F N

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]
  [Module.Finite F A] [IsModuleTopology F A] in
private theorem continuous_intertwiningMap_apply (N z : A) :
    Continuous fun X => intertwiningMap F N X z :=
  (continuous_id.mul continuous_const).sub continuous_const

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]
  [Module.Finite F A] [IsModuleTopology F A] in
private theorem finrank_range_intertwiningMap_conjugate (N : A) (u : Aˣ) :
    finrank F (LinearMap.range (intertwiningMap F N (conjugationHomeomorph u N))) =
      finrank F (LinearMap.range (intertwiningMap F N N)) := by
  let l := Units.mulLeftLinearEquiv F A u
  have heq : intertwiningMap F N (conjugationHomeomorph u N) =
      l.conj (intertwiningMap F N N) := by
    ext x
    change (u : A) * N * (↑u⁻¹ : A) * x - x * N =
      (u : A) * (N * ((↑u⁻¹ : A) * x) - ((↑u⁻¹ : A) * x) * N)
    simp [mul_sub, mul_assoc, Units.mul_inv_cancel_left]
  rw [heq, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range l.symm),
    LinearEquiv.finrank_map_eq]

include F in
private theorem eventually_conjugation_image (N : A) (u : Aˣ) (s : Set Aˣ) (hs : s ∈ 𝓝 u) :
    ∀ᶠ Y in 𝓝 (conjugationHomeomorph u N),
      Y ∈ closure (conjugationSaturation ({N} : Set A)) →
        Y ∈ (fun w : Aˣ => conjugationHomeomorph w N) '' s := by
  let O := conjugationSaturation ({N} : Set A)
  let T := intertwiningMap F N
  have hT : ∀ z, Continuous fun X => T X z := continuous_intertwiningMap_apply F N
  let r := finrank F (LinearMap.range (T N))
  have hO : O ⊆ {X | finrank F (LinearMap.range (T X)) ≤ r} := by
    intro X hX
    obtain ⟨u, Y, hY, rfl⟩ := mem_conjugationSaturation_iff.mp hX
    rw [Set.mem_singleton_iff] at hY
    subst Y
    exact (finrank_range_intertwiningMap_conjugate F N u).le
  have hc := closure_minimal hO (isClosed_finrank_range_le T hT r)
  let X := conjugationHomeomorph u N
  have hu : T X (u : A) = 0 := by
    change ((u : A) * N * ((↑u⁻¹ : A))) * u - u * N = 0
    rw [mul_assoc ((u : A) * N), Units.inv_mul, mul_one, sub_self]
  obtain ⟨f, hf, hfcont, hfker⟩ := exists_continuousAt_kernelSection T hT X u.val hu
  have hfnear : ∀ᶠ Y in 𝓝 X, f Y ∈ Units.val '' s := by
    have hv := BaseChange.finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := A)
    exact hfcont (by rw [hf]; exact hv.image_mem_nhds.mpr hs)
  filter_upwards [hfnear, hfker] with Y hY hker hYc
  obtain ⟨w, hws, hw⟩ := hY
  have hr := finrank_range_intertwiningMap_conjugate F N u
  have hle := hc hYc
  have hzero := hker.2 (le_antisymm (hle.trans_eq hr.symm) hker.1)
  change Y * f Y - f Y * N = 0 at hzero
  have hm := sub_eq_zero.mp hzero
  rw [← hw] at hm
  refine ⟨w, hws, ?_⟩
  change conjugationHomeomorph w N = Y
  rw [conjugationHomeomorph_apply, ← hm, mul_assoc, Units.mul_inv, mul_one]

include F in
/-- Each conjugacy orbit of the unit group in a finite algebra is locally closed. -/
theorem isLocallyClosed_conjugationOrbit (N : A) :
    IsLocallyClosed (conjugationSaturation ({N} : Set A)) := by
  rw [isLocallyClosed_iff_isLocallyClosedAt]
  intro X hX
  obtain ⟨u, Y, hY, rfl⟩ := mem_conjugationSaturation_iff.mp hX
  rw [Set.mem_singleton_iff] at hY
  subst Y
  apply isLocallyClosedAt_iff_closure_eventuallySubset.mpr
  exact (eventually_conjugation_image F N u univ univ_mem).mono fun _ hy hc => by
    obtain ⟨w, _, rfl⟩ := hy hc
    exact conjugationHomeomorph_mem_conjugationSaturation w (mem_singleton _)

private def conjugationOrbitMap (N : A) (u : Aˣ) :
    conjugationSaturation ({N} : Set A) :=
  ⟨conjugationHomeomorph u N, conjugationHomeomorph_mem_conjugationSaturation u (mem_singleton N)⟩

include F in
private theorem isOpenMap_conjugationOrbitMap (N : A) : IsOpenMap (conjugationOrbitMap N) := by
  rw [isOpenMap_iff_nhds_le]
  intro u s hs
  change conjugationOrbitMap N ⁻¹' s ∈ 𝓝 u at hs
  change ∀ᶠ Y in 𝓝 (conjugationOrbitMap N u), Y ∈ s
  rw [nhds_subtype]
  apply eventually_comap.mpr
  filter_upwards [eventually_conjugation_image F N u _ hs] with y hy Y hY
  subst y
  obtain ⟨w, hw, heq⟩ := hy (subset_closure Y.property)
  have := show conjugationOrbitMap N w = Y from Subtype.ext heq
  exact this ▸ hw

include F in
/-- Left centralizer cosets are homeomorphic to the conjugacy orbit with its subspace topology. -/
def conjugationOrbitHomeomorph (N : A) :
    LeftQuotient (conjugationCentralizer N) ≃ₜ conjugationSaturation ({N} : Set A) := by
  let H := conjugationCentralizer N
  let f := descend H (fun g : Aˣ => conjugationOrbitMap N g⁻¹) (by
    intro h g
    apply Subtype.ext
    change conjugationHomeomorph (h.val * g)⁻¹ N = conjugationHomeomorph g⁻¹ N
    rw [_root_.mul_inv_rev, conjugationHomeomorph_mul, conjugationHomeomorph_eq_smul h.val⁻¹,
      (mem_conjugationCentralizer_iff_smul _ _).mp (H.inv_mem h.property)])
  have hq := leftQuotient_isOpenQuotientMap H
  have hf (g : Aˣ) : f (leftQuotientMap H g) = conjugationOrbitMap N g⁻¹ := rfl
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    have hxy : conjugationHomeomorph x⁻¹ N = conjugationHomeomorph y⁻¹ N := by
      rw [hf, hf] at hab
      exact congrArg Subtype.val hab
    apply Quotient.sound
    change QuotientGroup.rightRel H x y
    rw [QuotientGroup.rightRel_apply, mem_conjugationCentralizer_iff_smul,
      ← conjugationHomeomorph_eq_smul, conjugationHomeomorph_mul, hxy,
      ← conjugationHomeomorph_mul, mul_inv_cancel, conjugationHomeomorph_one]
  have hsurj : Function.Surjective f := by
    rintro ⟨X, hX⟩
    obtain ⟨u, Y, hY, heq⟩ := mem_conjugationSaturation_iff.mp hX
    rw [mem_singleton_iff] at hY
    subst Y
    exact ⟨leftQuotientMap H u⁻¹, by rw [hf, inv_inv]; exact Subtype.ext heq⟩
  refine (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen ?_ ?_
  · apply hq.isQuotientMap.continuous_iff.mpr
    exact ((Units.continuous_val.comp continuous_inv).mul continuous_const |>.mul
      Units.continuous_val).subtype_mk _
  · exact hq.isOpenMap_iff.mpr ((isOpenMap_conjugationOrbitMap F N).comp (isOpenMap_inv Aˣ))

@[simp]
theorem conjugationOrbitHomeomorph_mk (N : A) (g : Aˣ) :
    (conjugationOrbitHomeomorph F N (leftQuotientMap (conjugationCentralizer N) g) : A) =
      conjugationHomeomorph g⁻¹ N := rfl

end Orbits

/-- Every unit conjugacy orbit in a finite-dimensional topological algebra is
locally closed, and its left centralizer cosets parametrize it homeomorphically. -/
def ConjugationOrbitTopologyStatement : Prop :=
  ∀ (F : Type u) (A : Type v) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [T1Space F] [Ring A] [Algebra F A] [Module.Finite F A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] (N : A),
    IsLocallyClosed (conjugationSaturation ({N} : Set A)) ∧
      ∃ e : LeftQuotient (conjugationCentralizer N) ≃ₜ conjugationSaturation ({N} : Set A),
        ∀ g : Aˣ, (e (leftQuotientMap (conjugationCentralizer N) g) : A) =
          conjugationHomeomorph g⁻¹ N

/-- The rank and intertwiner construction proves `ConjugationOrbitTopologyStatement`. -/
theorem conjugationOrbitTopology : ConjugationOrbitTopologyStatement.{u, v} := by
  intro F A _ _ _ _ _ _ _ _ _ _ N
  exact ⟨isLocallyClosed_conjugationOrbit F N, conjugationOrbitHomeomorph F N,
    conjugationOrbitHomeomorph_mk F N⟩

end Langlands.HarmonicAnalysis.UnitConjugation
