import Langlands.GroupScheme.Rational.TorusWeightSmooth

/-! # Formal smoothness for arbitrary semigroups of torus weights -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
    [Algebra.FormallySmooth R B]

/-- When zero is allowed, the supported lift itself lies in the requested
weight subgroup; no correction of the zero component is required. -/
theorem exists_lift_mem_weightSubgroup_of_zero_mem (P : AddSubsemigroup (I → ℤ)) (h0 : (0 : I → ℤ) ∈ P)
    {C : CommAlgCat.{u} R} (N : Ideal C) (hN : N ^ 2 = ⊥)
    {u₀ : F.obj (CommAlgCat.of R (C ⧸ N))}
    (hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N))) :
    ∃ u ∈ weightSubgroup e σ P C, F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) u = u₀ := by
  let Q := CommAlgCat.of R (C ⧸ N)
  let M := insertZero P
  let π : C ⟶ Q := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)
  have hπ : ∀ c, π.hom c = 0 ↔ c ∈ N := fun c => Ideal.Quotient.eq_zero_iff_mem
  -- Step 1: lift the twisted point with supported coordinates.
  let φ₀ : B →ₐ[R] supportedSubalgebra I Q M :=
    (coord e (hat σ u₀)).codRestrict _ (coord_hat_mem_supportedSubalgebra e σ M
      fun f _ hm => coord_comp_eq_zero_of_mem_weightSubgroup e σ hu₀ f hm)
  let φ : B →ₐ[R] supportedSubalgebra I C M :=
    Algebra.FormallySmooth.liftOfSurjective φ₀ (supportedMap M π.hom)
      (supportedMap_surjective M Ideal.Quotient.mk_surjective)
      ⟨2, by rw [Ideal.zero_eq_bot]; exact supportedMap_ker_sq M N hN⟩
  have hφ : ∀ f, supportedMap M π.hom (φ f) = φ₀ f :=
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _
  let X : F.obj (laurent I C) := ofCoord e ((supportedSubalgebra I C M).val.comp φ)
  have hX : F.map (laurentMap π) X = hat σ u₀ := by
    apply coord_injective e
    rw [coord_map, coord_ofCoord]
    apply AlgHom.ext
    intro f
    exact congrArg Subtype.val (hφ f)
  have hXs : ∀ f m, m ∉ M → (coord e X f).coeff m = 0 := by
    intro f m hm
    rw [coord_ofCoord]
    exact (φ f).2 m hm
  -- Step 2: untwist by the inverse universal units.
  let Y : F.obj (laurent I C) := σ.act (universalUnits I C)⁻¹ X
  have hY : F.map (laurentMap π) Y = F.map (constHom I Q) u₀ := by
    change F.map (laurentMap π) (σ.act _ X) = _
    rw [σ.naturality, units_map_laurentMap, hX]
    change σ.act (A := laurent I Q) (universalUnits I Q)⁻¹
      (σ.act (A := laurent I Q) (universalUnits I Q) (F.map (constHom I Q) u₀)) = _
    rw [← σ.act_mul, inv_mul_cancel, σ.act_one]
  have hYc : ∀ f, AddMonoidAlgebra.mapAlgHom (I → ℤ) π.hom (coord e Y f) =
      AddMonoidAlgebra.single 0 (coord e u₀ f) := by
    intro f
    have h := congrArg (fun y => coord e y f) hY
    simp only [coord_map, AlgHom.comp_apply] at h
    exact h
  have hYN : ∀ f n, n ≠ 0 → (coord e Y f).coeff n ∈ N := by
    intro f n hn
    rw [← hπ]
    have h := congrArg (fun s => AddMonoidAlgebra.coeff s n) (hYc f)
    simp only at h
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne hn] at h
    exact h
  have hYh : ∀ m h, IsHomogeneous e σ m h →
      coord e Y h = coord e X h * AddMonoidAlgebra.single (-m) 1 := by
    intro m h hh
    change coord e (σ.act _ X) h = _
    rw [coord_act_of_isHomogeneous e σ _ X hh, exponentValue_inv, exponentValue_universalUnits]
    rfl
  -- Step 3: the constant coefficient of the untwisted point.
  let p : B →ₐ[R] C := coeffZeroHom (coord e Y) fun f g =>
    coeff_zero_mul_of_mem hN (hYN f) (hYN g)
  let v : F.obj C := ofCoord e p
  have hv : F.map π v = u₀ := by
    apply coord_injective e
    rw [coord_map, coord_ofCoord]
    apply AlgHom.ext
    intro f
    change π.hom ((coord e Y f).coeff 0) = coord e u₀ f
    have h := congrArg (fun s => AddMonoidAlgebra.coeff s 0) (hYc f)
    simp only at h
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at h
    exact h
  have hvM : ∀ f m, m ∉ M → coord e v (comp e σ m f) = 0 := by
    intro f m hm
    rw [coord_ofCoord, coeffZeroHom_apply, hYh m _ (isHomogeneous_comp e σ m f)]
    have h0m : (0 : I → ℤ) = m + -m := (add_neg_cancel m).symm
    rw [h0m, AddMonoidAlgebra.coeff_mul_single_add, hXs _ m hm, zero_mul]
  refine ⟨v, ?_, hv⟩
  intro f m hm
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hm (hm0.symm ▸ h0)
  have hmM : m ∉ M := fun h => ((mem_insertZero P m).1 h).elim hm0 hm
  rw [hvM f m hmM, counit_comp]
  simp [hm0]

/-- Points of every semigroup weight subgroup lift through square-zero
thickenings, including semigroups containing zero and the empty semigroup. -/
theorem exists_lift_mem_weightSubgroup_all (P : AddSubsemigroup (I → ℤ))
    {C : CommAlgCat.{u} R} (N : Ideal C) (hN : N ^ 2 = ⊥)
    {u₀ : F.obj (CommAlgCat.of R (C ⧸ N))}
    (hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N))) :
    ∃ u ∈ weightSubgroup e σ P C,
      F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) u = u₀ := by
  by_cases h0 : (0 : I → ℤ) ∈ P
  · exact exists_lift_mem_weightSubgroup_of_zero_mem e σ P h0 N hN hu₀
  · exact exists_lift_mem_weightSubgroup e σ P h0 N hN hu₀

/-- Choose an actual point of the semigroup weight subgroup lifting the
given point through a square-zero quotient. No naturality of this choice is asserted. -/
def weightSubgroupLift (P : AddSubsemigroup (I → ℤ))
    {C : CommAlgCat.{u} R} (N : Ideal C) (hN : N ^ 2 = ⊥)
    (u₀ : F.obj (CommAlgCat.of R (C ⧸ N)))
    (hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N))) :
    weightSubgroup e σ P C :=
  ⟨(exists_lift_mem_weightSubgroup_all e σ P N hN hu₀).choose,
    (exists_lift_mem_weightSubgroup_all e σ P N hN hu₀).choose_spec.1⟩

/-- The chosen subgroup point reduces to the prescribed point. -/
theorem map_weightSubgroupLift (P : AddSubsemigroup (I → ℤ))
    {C : CommAlgCat.{u} R} (N : Ideal C) (hN : N ^ 2 = ⊥)
    (u₀ : F.obj (CommAlgCat.of R (C ⧸ N)))
    (hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N))) :
    F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N))
      (weightSubgroupLift e σ P N hN u₀ hu₀) = u₀ :=
  (exists_lift_mem_weightSubgroup_all e σ P N hN hu₀).choose_spec.2

/-- The coordinate algebra of every semigroup weight subgroup of a formally
smooth corepresented group functor is formally smooth. -/
theorem formallySmooth_quotient_weightIdeal_all (P : AddSubsemigroup (I → ℤ)) :
    Algebra.FormallySmooth R (B ⧸ weightIdeal e σ P) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ N hN f₀ => ?_
  let u₀ : F.obj (CommAlgCat.of R (C ⧸ N)) :=
    ofCoord e (f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P)))
  have hu₀c : coord e u₀ = f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P)) :=
    coord_ofCoord e _
  have hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N)) := by
    refine (isCutOutBy_weightIdeal e σ P _ u₀).2 fun b hb => ?_
    change coord e u₀ b = 0
    rw [hu₀c, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  obtain ⟨u, hu, hmap⟩ :=
    exists_lift_mem_weightSubgroup_all e σ P (C := CommAlgCat.of R C) N hN hu₀
  refine ⟨Ideal.Quotient.liftₐ _ (coord e u) ((isCutOutBy_weightIdeal e σ P _ u).1 hu), ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro b
  have h := congrArg (fun y => coord e y b) hmap
  simp only [coord_map, AlgHom.comp_apply] at h
  change Ideal.Quotient.mkₐ R N (coord e u b) =
    (f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P))) b
  rw [← hu₀c]
  exact h

/-- Over a Noetherian base, the coordinate algebra of each semigroup weight
subgroup of a finite-type formally smooth group functor is smooth. -/
theorem smooth_quotient_weightIdeal [IsNoetherianRing R] [Algebra.FiniteType R B]
    (P : AddSubsemigroup (I → ℤ)) : Algebra.Smooth R (B ⧸ weightIdeal e σ P) where
  formallySmooth := formallySmooth_quotient_weightIdeal_all e σ P
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

end Langlands.GroupScheme.Corepresented
