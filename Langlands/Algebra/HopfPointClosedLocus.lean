import Langlands.Algebra.HopfPointWindowExtension
import Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

/-! # The closed-immersion locus of a Hopf point is open -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointClosedLocus

open HopfPointExtension HopfPointWeightWindow HopfPointWindowExtension

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {M : Type*} [AddCommGroup M]

/-- The `C`-linear extension `C ⊗ A → C[M]` of a point `A → C[M]`. -/
def scalarExt (α : A →ₐ[R] AddMonoidAlgebra C M) : C ⊗[R] A →ₐ[C] AddMonoidAlgebra C M :=
  Algebra.TensorProduct.lift (Algebra.ofId C (AddMonoidAlgebra C M)) α
    (fun _ _ => Commute.all _ _)

@[simp] theorem scalarExt_tmul (α : A →ₐ[R] AddMonoidAlgebra C M) (c : C) (a : A) :
    scalarExt α (c ⊗ₜ a) = c • α a := by
  simp [scalarExt, Algebra.ofId_apply, Algebra.smul_def]

theorem coeff_pairMap_pair (β : A →ₐ[R] AddMonoidAlgebra C M) (l μ : M) (t : A ⊗[R] A) :
    (pairMap β t).coeff (l, μ) =
      LinearMap.mul' R C (TensorProduct.map (coeffForm β l) (coeffForm β μ) t) := by
  induction t with
  | tmul a b =>
    simp only [pairMap, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply, coeffForm_apply]
    exact coeff_inlMap_mul_inrMap _ _ l μ
  | add a b ha hb => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]

/-- The comultiplication is a coassociative coaction of `A` on itself. -/
theorem isCoassoc_comul : IsCoassoc (Coalgebra.comul (R := R) (A := A)) :=
  Coalgebra.coassoc

/-- Applying the scalar extension after the weight-`χ` projector of `A` keeps only
the `χ`-coefficient. -/
theorem scalarExt_proj {α : A →ₐ[R] AddMonoidAlgebra C M} (hα : IsHopfPoint α) (χ : M)
    (x : C ⊗[R] A) :
    scalarExt α (proj (Coalgebra.comul (R := R) (A := A)) α χ x) =
      AddMonoidAlgebra.single χ ((scalarExt α x).coeff χ) := by
  induction x with
  | tmul c a =>
    rw [proj_tmul, map_smul, scalarExt_tmul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      ← AddMonoidAlgebra.smul_single]
    congr 1
    have key : ∀ t : A ⊗[R] A, ∀ ψ : M,
        (scalarExt α (coeffSwap α χ t)).coeff ψ =
          LinearMap.mul' R C (TensorProduct.map (coeffForm α ψ) (coeffForm α χ) t) := by
      intro t ψ
      induction t with
      | tmul a' a'' =>
        simp only [coeffSwap_tmul, scalarExt_tmul, AddMonoidAlgebra.coeff_smul,
          Finsupp.smul_apply, smul_eq_mul, TensorProduct.map_tmul, LinearMap.mul'_apply,
          coeffForm_apply, mul_comm]
      | add x y hx hy => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    apply AddMonoidAlgebra.coeff_injective
    ext ψ
    rw [key, ← coeff_pairMap_pair]
    have h := congrArg (fun F => (F a).coeff (ψ, χ)) hα.comul
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at h
    rw [h, diagMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.coeff_single]
    change (Finsupp.mapDomain _ (α a).coeff) (ψ, χ) = (Finsupp.single χ ((α a).coeff χ)) ψ
    by_cases hψ : ψ = χ
    · subst hψ
      have hd : ((AddMonoidHom.id M).prod (AddMonoidHom.id M)) ψ = (ψ, ψ) := rfl
      have hinj : Function.Injective ((AddMonoidHom.id M).prod (AddMonoidHom.id M)) :=
        fun x y h => by simpa using congrArg Prod.fst h
      rw [← hd, Finsupp.mapDomain_apply_of_injective hinj, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne hψ]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨x, hx⟩
      simp only [AddMonoidHom.prod_apply, AddMonoidHom.id_apply, Prod.mk.injEq] at hx
      exact hψ (hx.1.symm.trans hx.2)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.single_add]

/-- A surjective residue-field specialization has, in every degree, a coefficient
that does not vanish at the residue field. -/
theorem exists_coeff_not_mem {α : A →ₐ[R] AddMonoidAlgebra C M} (p : Ideal C) [p.IsPrime]
    (h : Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp α))) (m : M) :
    ∃ a : A, (α a).coeff m ∉ p := by
  by_contra! hall
  obtain ⟨z, hz⟩ := h (AddMonoidAlgebra.single m 1)
  have key : ∀ z : p.ResidueField ⊗[R] A, (scalarExt ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp α) z).coeff m = 0 := by
    intro z
    induction z with
    | tmul k a =>
      rw [scalarExt_tmul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AlgHom.comp_apply,
        AddMonoidAlgebra.coeff_mapAlgHom, IsScalarTower.coe_toAlgHom',
        (Ideal.algebraMap_residueField_eq_zero).mpr (hall a), smul_zero]
    | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy,
        add_zero]
  have := key z
  rw [hz, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
  exact one_ne_zero this

theorem coeff_scalarExt_one_tmul {D : Type*} [CommRing D] [Algebra R D] [Algebra C D]
    [IsScalarTower R C D] (α : A →ₐ[R] AddMonoidAlgebra C M) (a : A) (m : M) :
    (scalarExt ((AddMonoidAlgebra.mapAlgHom M (IsScalarTower.toAlgHom R C D)).comp α)
      (1 ⊗ₜ a)).coeff m = algebraMap C D ((α a).coeff m) := by
  rw [scalarExt_tmul, one_smul, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom,
    IsScalarTower.coe_toAlgHom']

theorem single_mem_range_of_isUnit {α : A →ₐ[R] AddMonoidAlgebra C M} (hα : IsHopfPoint α)
    (a : A) (m : M) (h : IsUnit ((α a).coeff m)) :
    AddMonoidAlgebra.single m (1 : C) ∈ (scalarExt α).range := by
  obtain ⟨v, hv⟩ := h.exists_left_inv
  rw [AlgHom.mem_range]
  refine ⟨v • proj (Coalgebra.comul (R := R) (A := A)) α m (1 ⊗ₜ a), ?_⟩
  rw [map_smul, scalarExt_proj hα, scalarExt_tmul, one_smul, AddMonoidAlgebra.smul_single,
    smul_eq_mul, hv]

/-- Openness of the closed-immersion locus: surjectivity of the scalar extension at
the residue field of `p` spreads to a principal open around `p`. -/
theorem exists_away_surjective [AddMonoid.FG M] {α : A →ₐ[R] AddMonoidAlgebra C M}
    (hα : IsHopfPoint α) (p : Ideal C) [p.IsPrime]
    (h : Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp α))) :
    ∃ f ∉ p, Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α)) := by
  classical
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := M)
  choose a ha using exists_coeff_not_mem p h
  let f := ∏ m ∈ s, (α (a m)).coeff m
  have hfp : f ∉ p := by
    intro hmem
    obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact ha m hm
  refine ⟨f, hfp, ?_⟩
  have hαD : IsHopfPoint ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α) :=
    IsHopfPoint.mapAlgHom _ hα
  have hgen : ∀ m ∈ (s : Set M), AddMonoidAlgebra.single m (1 : Localization.Away f) ∈
      (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α)).range := by
    intro m hm
    apply single_mem_range_of_isUnit hαD (a m) m
    rw [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom, IsScalarTower.coe_toAlgHom']
    apply isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ hm))
    exact IsLocalization.Away.algebraMap_isUnit f
  exact CommutativeAlgebra.DiagonalCoalgebraLocus.surjective_of_generators_mem _ _ hs hgen

/-- A surjective scalar extension makes the values of `α` generate `C[M]`. -/
theorem adjoin_range_eq_top {α : A →ₐ[R] AddMonoidAlgebra C M}
    (h : Function.Surjective (scalarExt α)) : Algebra.adjoin C (Set.range α) = ⊤ := by
  have key : ∀ x : C ⊗[R] A, scalarExt α x ∈ Algebra.adjoin C (Set.range α) := by
    intro x
    induction x with
    | tmul c a =>
      rw [scalarExt_tmul]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self a)) c
    | add x x' hx hx' => rw [map_add]; exact add_mem hx hx'
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := h y
  exact key x

/-- A surjective specialization at a field point has, in every degree, a
coefficient that does not vanish at that point. -/
theorem exists_coeff_ne_zero_of_field {α : A →ₐ[R] AddMonoidAlgebra C M} {K : Type*}
    [Field K] [Algebra R K] (φ : C →ₐ[R] K)
    (h : Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M φ).comp α))) (m : M) :
    ∃ a : A, φ ((α a).coeff m) ≠ 0 := by
  by_contra! hall
  obtain ⟨z, hz⟩ := h (AddMonoidAlgebra.single m 1)
  have key : ∀ z : K ⊗[R] A,
      (scalarExt ((AddMonoidAlgebra.mapAlgHom M φ).comp α) z).coeff m = 0 := by
    intro z
    induction z with
    | tmul k a =>
      rw [scalarExt_tmul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AlgHom.comp_apply,
        AddMonoidAlgebra.coeff_mapAlgHom, hall a, smul_zero]
    | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy,
        add_zero]
  have := key z
  rw [hz, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
  exact one_ne_zero this

/-- Openness of the closed-immersion locus around an arbitrary field point. -/
theorem exists_away_surjective_of_field [AddMonoid.FG M] {α : A →ₐ[R] AddMonoidAlgebra C M}
    (hα : IsHopfPoint α) {K : Type*} [Field K] [Algebra R K] (φ : C →ₐ[R] K)
    (h : Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M φ).comp α))) :
    ∃ f : C, φ f ≠ 0 ∧ Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α)) := by
  classical
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := M)
  choose a ha using exists_coeff_ne_zero_of_field φ h
  let f := ∏ m ∈ s, (α (a m)).coeff m
  have hf : φ f ≠ 0 := by
    simp only [f, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => ha m
  refine ⟨f, hf, ?_⟩
  have hαD : IsHopfPoint ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α) :=
    IsHopfPoint.mapAlgHom _ hα
  have hgen : ∀ m ∈ (s : Set M), AddMonoidAlgebra.single m (1 : Localization.Away f) ∈
      (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.Away f))).comp α)).range := by
    intro m hm
    apply single_mem_range_of_isUnit hαD (a m) m
    rw [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom, IsScalarTower.coe_toAlgHom']
    apply isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ hm))
    exact IsLocalization.Away.algebraMap_isUnit f
  exact CommutativeAlgebra.DiagonalCoalgebraLocus.surjective_of_generators_mem _ _ hs hgen

/-- Surjectivity of the scalar extension is preserved by change of coefficients. -/
theorem surjective_scalarExt_mapAlgHom {α : A →ₐ[R] AddMonoidAlgebra C M} {D : Type*}
    [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (h : Function.Surjective (scalarExt α)) :
    Function.Surjective (scalarExt ((AddMonoidAlgebra.mapAlgHom M ψ).comp α)) := by
  apply CommutativeAlgebra.DiagonalCoalgebraLocus.surjective_of_generators_mem _ Set.univ
    (AddSubmonoid.closure_univ)
  intro χ _
  obtain ⟨x, hx⟩ := h (AddMonoidAlgebra.single χ 1)
  rw [AlgHom.mem_range]
  refine ⟨Algebra.TensorProduct.map ψ (AlgHom.id R A) x, ?_⟩
  have key : ∀ y : C ⊗[R] A,
      scalarExt ((AddMonoidAlgebra.mapAlgHom M ψ).comp α)
        (Algebra.TensorProduct.map ψ (AlgHom.id R A) y) =
      AddMonoidAlgebra.mapAlgHom M ψ (scalarExt α y) := by
    intro y
    induction y with
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, scalarExt_tmul, scalarExt_tmul, AlgHom.id_apply,
        AlgHom.comp_apply]
      apply AddMonoidAlgebra.coeff_injective
      ext b
      simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_mapAlgHom,
        smul_eq_mul, map_mul]
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
  rw [key, hx]
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp

/-- The scalar extension commutes with changes of coefficients. -/
theorem scalarExt_mapAlgHom_map {α : A →ₐ[R] AddMonoidAlgebra C M} {D : Type*}
    [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (y : C ⊗[R] A) :
    scalarExt ((AddMonoidAlgebra.mapAlgHom M ψ).comp α)
        (Algebra.TensorProduct.map ψ (AlgHom.id R A) y) =
      AddMonoidAlgebra.mapAlgHom M ψ (scalarExt α y) := by
  induction y with
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, scalarExt_tmul, scalarExt_tmul, AlgHom.id_apply,
      AlgHom.comp_apply]
    apply AddMonoidAlgebra.coeff_injective
    ext b
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_mapAlgHom,
      smul_eq_mul, map_mul]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]

/-- Kernels of scalar extensions are determined by the localizations at maximal ideals. -/
theorem ker_scalarExt_le_of_localization {α₁ α₂ : A →ₐ[R] AddMonoidAlgebra C M}
    (h : ∀ (P : Ideal C) (_ : P.IsMaximal),
      RingHom.ker (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.AtPrime P))).comp α₁)) ≤
      RingHom.ker (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.AtPrime P))).comp α₂))) :
    RingHom.ker (scalarExt α₁) ≤ RingHom.ker (scalarExt α₂) := by
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  apply AddMonoidAlgebra.coeff_injective
  ext χ
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply eq_zero_of_localization
  intro P hP
  have h1 : Algebra.TensorProduct.map (IsScalarTower.toAlgHom R C (Localization.AtPrime P))
      (AlgHom.id R A) x ∈ RingHom.ker (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.AtPrime P))).comp α₁)) := by
    rw [RingHom.mem_ker, scalarExt_mapAlgHom_map, hx, map_zero]
  have h2 := h P hP h1
  rw [RingHom.mem_ker, scalarExt_mapAlgHom_map] at h2
  have h3 := congrArg (fun y => y.coeff χ) h2
  simpa [AddMonoidAlgebra.coeff_mapAlgHom] using h3

/-- Equality of kernels of scalar extensions is local at maximal ideals. -/
theorem ker_scalarExt_eq_of_localization {α₁ α₂ : A →ₐ[R] AddMonoidAlgebra C M}
    (h : ∀ (P : Ideal C) (_ : P.IsMaximal),
      RingHom.ker (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.AtPrime P))).comp α₁)) =
      RingHom.ker (scalarExt ((AddMonoidAlgebra.mapAlgHom M
        (IsScalarTower.toAlgHom R C (Localization.AtPrime P))).comp α₂))) :
    RingHom.ker (scalarExt α₁) = RingHom.ker (scalarExt α₂) :=
  le_antisymm (ker_scalarExt_le_of_localization fun P hP => (h P hP).le)
    (ker_scalarExt_le_of_localization fun P hP => (h P hP).ge)

end Langlands.Algebra.HopfPointClosedLocus
