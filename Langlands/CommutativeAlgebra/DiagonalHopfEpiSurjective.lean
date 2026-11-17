import Langlands.CommutativeAlgebra.DiagonalCoalgebraImage
import Langlands.GroupScheme.AffineHomImageHopfAdapter

/-! # Epimorphic Hopf maps into diagonal Hopf algebras are surjective -/

noncomputable section

universe u

open AddMonoidAlgebra

namespace Langlands.CommutativeAlgebra.DiagonalHopfEpi

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]

/-- The ideal of coefficients `r` for which the monomial `single m r` lies in a subalgebra
`B` of `R[M]`. -/
def coefficientIdeal (B : Subalgebra R (AddMonoidAlgebra R M)) (m : M) : Ideal R :=
  Submodule.comap (AddMonoidAlgebra.lsingle (R := R) m) (Subalgebra.toSubmodule B)

theorem mem_coefficientIdeal {B : Subalgebra R (AddMonoidAlgebra R M)} {m : M} {r : R} :
    r ∈ coefficientIdeal B m ↔ single m r ∈ B := Iff.rfl

/-- A subalgebra of `R[M]` all of whose coefficient ideals are the unit ideal is everything. -/
theorem mem_of_coefficientIdeal_eq_top (B : Subalgebra R (AddMonoidAlgebra R M))
    (h : ∀ m, coefficientIdeal B m = ⊤) (x : AddMonoidAlgebra R M) : x ∈ B := by
  rw [← sum_coeff_single x]
  refine Subalgebra.sum_mem B fun m _ => ?_
  exact mem_coefficientIdeal.mp (by rw [h m]; exact Submodule.mem_top)

variable {B : Type u} [CommRing B] [Bialgebra R B]

/-- **Epimorphic bialgebra maps onto a diagonal Hopf algebra are surjective.** Let
`φ : B → R[M]` be a bialgebra homomorphism into the group algebra of an abelian group whose
range is stable under the antipode. If `φ` is an epimorphism of commutative rings, then `φ` is
surjective. -/
theorem surjective_of_epi (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (hS : ∀ x ∈ φ.toAlgHom.range, HopfAlgebra.antipode R x ∈ φ.toAlgHom.range)
    (hφ : ∀ (D : Type u) [CommRing D] (f g : AddMonoidAlgebra R M →+* D),
      f.comp (φ.toAlgHom : B →+* AddMonoidAlgebra R M) =
        g.comp (φ.toAlgHom : B →+* AddMonoidAlgebra R M) → f = g) :
    Function.Surjective φ := by
  classical
  set Bφ := φ.toAlgHom.range with hBφ
  by_contra hns
  obtain ⟨l, hl⟩ : ∃ l, coefficientIdeal Bφ l ≠ ⊤ := by
    by_contra h
    push Not at h
    apply hns
    intro y
    obtain ⟨b, hb⟩ := (AlgHom.mem_range _).mp (mem_of_coefficientIdeal_eq_top Bφ h y)
    exact ⟨b, hb⟩
  obtain ⟨𝔪, h𝔪, hl𝔪⟩ := Ideal.exists_le_maximal _ hl
  have one_not_mem : (1 : R) ∉ 𝔪 := fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  let N : AddSubgroup M :=
    { carrier := {m | ¬ coefficientIdeal Bφ m ≤ 𝔪}
      zero_mem' := by
        intro h
        apply one_not_mem
        apply h
        rw [mem_coefficientIdeal, ← AddMonoidAlgebra.one_def]
        exact Subalgebra.one_mem _
      add_mem' := by
        intro a b ha hb
        obtain ⟨r, hr, hr𝔪⟩ := SetLike.not_le_iff_exists.mp ha
        obtain ⟨s, hs, hs𝔪⟩ := SetLike.not_le_iff_exists.mp hb
        intro h
        have hrs : r * s ∈ coefficientIdeal Bφ (a + b) := by
          rw [mem_coefficientIdeal, ← single_mul_single]
          exact Subalgebra.mul_mem _ (mem_coefficientIdeal.mp hr) (mem_coefficientIdeal.mp hs)
        rcases h𝔪.isPrime.mem_or_mem (h hrs) with h' | h'
        · exact hr𝔪 h'
        · exact hs𝔪 h'
      neg_mem' := by
        intro a ha
        obtain ⟨r, hr, hr𝔪⟩ := SetLike.not_le_iff_exists.mp ha
        intro h
        apply hr𝔪
        apply h
        rw [mem_coefficientIdeal]
        have := hS _ (mem_coefficientIdeal.mp hr)
        simpa [AddMonoidAlgebra.antipode_single] using this }
  have hmemN : ∀ m, m ∈ N ↔ ¬ coefficientIdeal Bφ m ≤ 𝔪 := fun m => Iff.rfl
  have hlN : l ∉ N := fun h => (hmemN l).mp h hl𝔪
  let k := R ⧸ 𝔪
  have : 𝔪.IsMaximal := h𝔪
  let D := AddMonoidAlgebra k (M ⧸ N)
  let χ : Multiplicative M →* D :=
    (AddMonoidAlgebra.of k (M ⧸ N)).comp
      (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' N))
  let f : AddMonoidAlgebra R M →ₐ[R] D := AddMonoidAlgebra.lift R D M 1
  let g : AddMonoidAlgebra R M →ₐ[R] D := AddMonoidAlgebra.lift R D M χ
  have hsmul : ∀ (r : R) (y : D), r ∈ 𝔪 → r • y = 0 := by
    intro r y hr
    rw [← algebraMap_smul k r y]
    have : algebraMap R k r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    rw [this, zero_smul]
  have hfg : f.toRingHom.comp (φ.toAlgHom : B →+* AddMonoidAlgebra R M) =
      g.toRingHom.comp (φ.toAlgHom : B →+* AddMonoidAlgebra R M) := by
    refine RingHom.ext fun b => ?_
    change f (φ b) = g (φ b)
    have hx : ∀ m, (φ b).coeff m ∈ coefficientIdeal Bφ m := fun m =>
      DiagonalCoalgebraImage.single_coefficient_mem_range φ b m
    rw [← sum_coeff_single (φ b), map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr fun m _ => ?_
    simp only [f, g, AddMonoidAlgebra.lift_single, MonoidHom.one_apply]
    by_cases hm : m ∈ N
    · have h0 : ((m : M ⧸ N)) = 0 := (QuotientAddGroup.eq_zero_iff m).mpr hm
      simp only [χ, MonoidHom.coe_comp, Function.comp_apply, AddMonoidAlgebra.of_apply]
      simp [h0, ← AddMonoidAlgebra.one_def]
    · have hm' : (φ b).coeff m ∈ 𝔪 := by
        rw [hmemN, not_not] at hm
        exact hm (hx m)
      rw [hsmul _ _ hm', hsmul _ _ hm']
  have hfg' := congrArg (fun F => F (single l 1)) (hφ D f.toRingHom g.toRingHom hfg)
  simp only [f, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AddMonoidAlgebra.lift_single,
    MonoidHom.one_apply, one_smul, χ, MonoidHom.coe_comp, Function.comp_apply,
    AddMonoidAlgebra.of_apply] at hfg'
  rw [AddMonoidAlgebra.one_def] at hfg'
  have hl0 : (0 : M ⧸ N) = QuotientAddGroup.mk' N l :=
    (single_left_inj (one_ne_zero (α := k))).mp hfg'
  exact hlN ((QuotientAddGroup.eq_zero_iff l).mp hl0.symm)

end Langlands.CommutativeAlgebra.DiagonalHopfEpi
