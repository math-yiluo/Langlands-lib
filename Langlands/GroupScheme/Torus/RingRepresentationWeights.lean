import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex

/-! # Split-torus representation weights over commutative rings -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitTorusRepresentationWeights

open splitTorus
open CharacterRestrictionFiniteIndex (monomialUnit monomialUnit_val
  exponentValue_monomialUnit exponentValue_monomialUnit_id)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [CommRing k] {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- The matrix of `ρ` at the image under `j` of the universal point of the split torus, an
invertible matrix over the group algebra `k[ℤ^I]`. -/
def universalMatrix : Matrix.GeneralLinearGroup (Fin N) (AddMonoidAlgebra k (I → ℤ)) :=
  GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ)))
    (universalPoint (R := CommRingCat.of k) I ≫ j.hom.hom ≫ ρ.hom.hom)

/-- The weight matrix `P_m`: the coefficient of the monomial `m` in the universal matrix. -/
def weight (m : I → ℤ) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun a b =>
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b).coeff m

/-- A finite set of exponents outside which all weight matrices vanish. -/
def weightSupport : Finset (I → ℤ) :=
  Finset.univ.biUnion fun ab : Fin N × Fin N =>
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ)))
      ab.1 ab.2).coeff.support

/-- Outside the weight support the weight matrices vanish. -/
theorem weight_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I j) : weight ρ I j m = 0 := by
  ext a b
  by_contra h
  exact hm (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)

/-- The universal matrix is the sum of its weight matrices times the monomials. -/
theorem universalMatrix_apply (a b : Fin N) :
    (universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b =
      ∑ m ∈ weightSupport ρ I j, weight ρ I j m a b • AddMonoidAlgebra.single m 1 := by
  apply AddMonoidAlgebra.coeff_injective
  ext n
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · change weight ρ I j n a b = 0
    rw [weight_eq_zero ρ I j hn]
    rfl

/-- **Evaluation formula.** At the point of the split torus with unit coordinates `t` over a
`k`-algebra `A`, the matrix of `ρ ∘ j` is `∑ₘ P_m · tᵐ`. -/
theorem affinePointsEquiv_eval {A : Type u} [CommRing A] [Algebra k A] (t : I → Aˣ) (a b : Fin N) :
    (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) A)
      ((algebraPointsEquiv I A).symm t ≫ j.hom.hom ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) A) a b =
      ∑ m ∈ weightSupport ρ I j,
        weight ρ I j m a b • ((exponentValue I t (Multiplicative.ofAdd m) : Aˣ) : A) := by
  rw [← universalPoint_evaluateUnits (R := CommRingCat.of k) I t, Lie.affineMap_apply,
    Category.assoc, GeneralLinear.affinePointsEquiv_naturality]
  change evaluateUnits (R := CommRingCat.of k) I t
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b) = _
  rw [universalMatrix_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, evaluateUnits_single, map_one, one_mul]

/-- A function of exponents that vanishes outside the weight support is recovered from its
sum against a Kronecker delta over the weight support. -/
theorem sum_ite_eq_of_weightSupport {X : Type*} [AddCommMonoid X] (f : (I → ℤ) → X)
    (hf : ∀ m ∉ weightSupport ρ I j, f m = 0) (m₀ : I → ℤ) :
    ∑ m ∈ weightSupport ρ I j, (if m = m₀ then f m else 0) = f m₀ := by
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hf m₀ h).symm

/-- The weight matrices sum to the identity: evaluate at the identity point. -/
theorem sum_weight : ∑ m ∈ weightSupport ρ I j, weight ρ I j m = 1 := by
  ext a b
  have h := affinePointsEquiv_eval ρ I j (A := k) 1 a b
  rw [map_one, MonObj.one_comp, map_one] at h
  simp only [exponentValue, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply, one_zpow,
    Finset.prod_const_one, Units.val_one, smul_eq_mul, mul_one] at h
  rw [Matrix.sum_apply]
  exact h.symm

/-- The entries of the weight matrices vanish outside the weight support. -/
theorem weight_apply_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I j) (a b : Fin N) :
    weight ρ I j m a b = 0 := by
  rw [weight_eq_zero ρ I j hm]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The coefficient of a scaled monomial. -/
theorem coeff_smul_single_one {M : Type u} [AddCommGroup M] [DecidableEq M] (c : k) (x y : M) :
    (c • AddMonoidAlgebra.single x (1 : k)).coeff y = if x = y then c else 0 := by
  rw [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- The group algebra `k[ℤ^I × ℤ^I]` of pairs of exponents. -/
local notation "K₂" => AddMonoidAlgebra k ((I → ℤ) × (I → ℤ))

/-- The weight matrices are orthogonal idempotents: multiply two independent universal points. -/
theorem weight_mul_weight (m₀ n₀ : I → ℤ) :
    weight ρ I j m₀ * weight ρ I j n₀ = if m₀ = n₀ then weight ρ I j m₀ else 0 := by
  classical
  let t₁ : I → K₂ˣ := fun i => monomialUnit (AddMonoidHom.inl (I → ℤ) (I → ℤ) (Pi.single i 1))
  let t₂ : I → K₂ˣ := fun i => monomialUnit (AddMonoidHom.inr (I → ℤ) (I → ℤ) (Pi.single i 1))
  let δ : (I → ℤ) →+ (I → ℤ) × (I → ℤ) := (AddMonoidHom.id _).prod (AddMonoidHom.id _)
  have ht : t₁ * t₂ = fun i => monomialUnit (δ (Pi.single i 1)) := by
    funext i
    simp only [Pi.mul_apply, t₁, t₂, δ, monomialUnit, ← map_mul, ← ofAdd_add]
    congr 2
    rw [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hpt : (algebraPointsEquiv I K₂).symm (t₁ * t₂) ≫ j.hom.hom ≫ ρ.hom.hom =
      ((algebraPointsEquiv I K₂).symm t₁ ≫ j.hom.hom ≫ ρ.hom.hom) *
        ((algebraPointsEquiv I K₂).symm t₂ ≫ j.hom.hom ≫ ρ.hom.hom) := by
    rw [map_mul, MonObj.mul_comp]
  have h12 : ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) K₂)
        ((algebraPointsEquiv I K₂).symm (t₁ * t₂) ≫ j.hom.hom ≫ ρ.hom.hom) :
          Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) =
      ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
        (CommAlgCat.of (CommRingCat.of k) K₂)
          ((algebraPointsEquiv I K₂).symm t₁ ≫ j.hom.hom ≫ ρ.hom.hom) :
            Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) *
      ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
        (CommAlgCat.of (CommRingCat.of k) K₂)
          ((algebraPointsEquiv I K₂).symm t₂ ≫ j.hom.hom ≫ ρ.hom.hom) :
            Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) := by
    rw [hpt, map_mul, Units.val_mul]
  ext a b
  have hab := congrArg (fun z : K₂ => z.coeff (m₀, n₀)) (congrFun (congrFun h12 a) b)
  simp only [Matrix.mul_apply] at hab
  rw [affinePointsEquiv_eval ρ I j (A := K₂) (t₁ * t₂) a b, ht] at hab
  simp only [affinePointsEquiv_eval ρ I j (A := K₂)] at hab
  simp only [t₁, t₂, exponentValue_monomialUnit, monomialUnit_val] at hab
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, AddMonoidAlgebra.single_mul_single, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_smul_single_one] at hab
  simp only [δ, AddMonoidHom.prod_apply, AddMonoidHom.id_apply, AddMonoidHom.inl_apply,
    AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add] at hab
  have hR : ∀ l, (∑ m ∈ weightSupport ρ I j, ∑ n ∈ weightSupport ρ I j,
      if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0) =
        weight ρ I j m₀ a l * weight ρ I j n₀ l b := by
    intro l
    have hm : ∀ m, (∑ n ∈ weightSupport ρ I j,
        if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0) =
          if m = m₀ then weight ρ I j m a l * weight ρ I j n₀ l b else 0 := by
      intro m
      by_cases h : m = m₀
      · subst h
        simp only [Prod.mk.injEq, true_and, ite_true]
        exact sum_ite_eq_of_weightSupport ρ I j (fun n => weight ρ I j m a l * weight ρ I j n l b)
          (fun n hn => by rw [weight_apply_eq_zero ρ I j hn, mul_zero]) n₀
      · simp [Prod.mk.injEq, h]
    rw [Finset.sum_congr rfl fun m _ => hm m]
    exact sum_ite_eq_of_weightSupport ρ I j (fun m => weight ρ I j m a l * weight ρ I j n₀ l b)
      (fun m hm => by rw [weight_apply_eq_zero ρ I j hm, zero_mul]) m₀
  have hL : (∑ m ∈ weightSupport ρ I j, if (m, m) = (m₀, n₀) then weight ρ I j m a b else 0) =
      if m₀ = n₀ then weight ρ I j m₀ a b else 0 := by
    by_cases h : m₀ = n₀
    · subst h
      simp only [Prod.mk.injEq, and_self, ite_true]
      exact sum_ite_eq_of_weightSupport ρ I j (fun m => weight ρ I j m a b)
        (fun m hm => weight_apply_eq_zero ρ I j hm a b) m₀
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun m _ => ite_eq_right ?_
      rintro ⟨⟩
      exact h rfl
  calc (weight ρ I j m₀ * weight ρ I j n₀) a b
      = ∑ l, ∑ m ∈ weightSupport ρ I j, ∑ n ∈ weightSupport ρ I j,
          if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun l _ => (hR l).symm
    _ = ∑ m ∈ weightSupport ρ I j, if (m, m) = (m₀, n₀) then weight ρ I j m a b else 0 :=
        hab.symm
    _ = if m₀ = n₀ then weight ρ I j m₀ a b else 0 := hL
    _ = (if m₀ = n₀ then weight ρ I j m₀ else 0) a b := by split_ifs <;> rfl

/-- The group algebra `k[ℤ^I/Λ]` of a quotient of the exponents. -/
local notation "KΛ" Λ:max => AddMonoidAlgebra k ((I → ℤ) ⧸ Λ)

/-- **The weights generate the characters.** If `ρ ∘ j` is a monomorphism, the exponents of the
nonzero weight matrices generate `ℤ^I`: otherwise the torus point over `k[ℤ^I/Λ]` with
coordinates the classes of the `eᵢ` is nontrivial but has trivial matrix. -/
theorem closure_weights_eq_top [Nontrivial k] (hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left) :
    AddSubgroup.closure {m : I → ℤ | weight ρ I j m ≠ 0} = ⊤ := by
  classical
  have : Mono (j.hom.hom ≫ ρ.hom.hom) := Over.mono_of_mono_left _
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : AddSubgroup (I → ℤ),
      Λ = AddSubgroup.closure {m : I → ℤ | weight ρ I j m ≠ 0} := ⟨_, rfl⟩
  rw [← hΛ]
  let t : I → (KΛ Λ)ˣ :=
    fun i => monomialUnit (QuotientAddGroup.mk' Λ (Pi.single i 1))
  have hmat : GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (KΛ Λ))
        ((algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)).symm t ≫ j.hom.hom ≫
          ρ.hom.hom) = 1 := by
    apply Units.ext
    ext a b
    rw [affinePointsEquiv_eval]
    simp only [t, exponentValue_monomialUnit, monomialUnit_val]
    have hterm : ∀ n ∈ weightSupport ρ I j,
        weight ρ I j n a b • AddMonoidAlgebra.single (QuotientAddGroup.mk' Λ n) (1 : k) =
          weight ρ I j n a b • (1 : KΛ Λ) := by
      intro n _
      by_cases h : weight ρ I j n = 0
      · rw [h]
        simp
      · have hn : QuotientAddGroup.mk' Λ n = 0 :=
          (QuotientAddGroup.eq_zero_iff n).mpr (hΛ ▸ AddSubgroup.subset_closure h)
        rw [hn, AddMonoidAlgebra.one_def]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← Matrix.sum_apply, sum_weight,
      Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hpt : (algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)).symm t = 1 := by
    apply (cancel_mono (j.hom.hom ≫ ρ.hom.hom)).mp
    rw [MonObj.one_comp]
    apply (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (KΛ Λ))).injective
    rw [hmat, map_one]
  have ht : t = 1 := by
    have := congrArg (algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)) hpt
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have he : ∀ i, Pi.single i (1 : ℤ) ∈ Λ := by
    intro i
    have h := congrArg (fun u : I → (KΛ Λ)ˣ =>
      ((u i : (KΛ Λ)ˣ) : KΛ Λ).coeff) ht
    simp only [t, monomialUnit_val, Pi.one_apply, Units.val_one, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single] at h
    exact (QuotientAddGroup.eq_zero_iff _).mp (Finsupp.single_left_injective one_ne_zero h)
  rw [eq_top_iff]
  intro m _
  have hm : m = ∑ i, m i • Pi.single i (1 : ℤ) := by
    ext i
    simp [Pi.single_apply]
  rw [hm]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (he i) _

/-- Every coefficient projector is idempotent. -/
theorem weight_mul_self (m : I → ℤ) :
    weight ρ I j m * weight ρ I j m = weight ρ I j m := by
  rw [weight_mul_weight, ite_eq_left rfl]

/-- The finite entry-support union consists exactly of the occurring weights. -/
theorem mem_weightSupport (m : I → ℤ) :
    m ∈ weightSupport ρ I j ↔ weight ρ I j m ≠ 0 := by
  constructor
  · intro hm hz
    obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.mem_biUnion.mp hm
    have hcoeff : weight ρ I j m a b ≠ 0 := Finsupp.mem_support_iff.mp hab
    exact hcoeff (congrFun (congrFun hz a) b)
  · intro hm
    by_contra hmem
    exact hm (weight_eq_zero ρ I j hmem)

/-- Only finitely many weight matrices are nonzero. -/
theorem finite_weights : Set.Finite {m : I → ℤ | weight ρ I j m ≠ 0} := by
  have hs : {m : I → ℤ | weight ρ I j m ≠ 0} =
      (weightSupport ρ I j : Set (I → ℤ)) := by
    ext m
    exact (mem_weightSupport ρ I j m).symm
  rw [hs]
  exact Finset.finite_toSet _

/-- Over a field these projectors are exactly the existing representation weights. -/
theorem weight_eq_field_weight {F : Type u} [Field F]
    {H : GroupScheme (Spec (CommRingCat.of F))} {M : ℕ}
    (σ : MatrixRepresentation H (Fin M)) (J : Type u) [Fintype J] [DecidableEq J]
    (i : splitTorus (Spec (CommRingCat.of F)) J ⟶ H) (m : J → ℤ) :
    weight σ J i m = CharacterRestrictionFiniteIndex.weight σ J i m := rfl

end Langlands.GroupScheme.SplitTorusRepresentationWeights
