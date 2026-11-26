import Langlands.LocalFactor.Ramification.Herbrand.LocalQuotientProof

/-!
# Herbrand's quotient theorem and the tower laws

The kernel of normal restriction from `Gal(L/K)` to `Gal(E/K)` acts on the
integers of `L`. Its fixed ring is the supplied integer ring of `E`, and the
quotient action is the action of `Gal(E/K)`. These identifications carry the
Herbrand quotient and composition formulas to the supplied realizations.
-/

noncomputable section

namespace Langlands.Ramification.Local

open QuotientBridge

universe u₀ uK uE uL

section Kernel

variable (K : Type uK) [Field K] (L : Type uL) [Field L] [Algebra K L]
  (E : Type uE) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E]

private abbrev restrictionKernel : Subgroup (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker

private theorem mem_restrictionKernel_iff (σ : L ≃ₐ[K] L) :
    σ ∈ restrictionKernel K L E ↔ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x := by
  change σ ∈ (AlgEquiv.restrictNormalHom E).ker ↔ _
  rw [AlgEquiv.ker_restrictNormalHom, IntermediateField.mem_fixingSubgroup_iff]
  simp only [AlgHom.mem_fieldRange, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

/-- The kernel consists of the automorphisms over `E`, with the same action on `L`. -/
private def restrictionKernelEquiv : (L ≃ₐ[E] L) ≃* restrictionKernel K L E where
  toFun τ := ⟨τ.restrictScalars K, (mem_restrictionKernel_iff K L E _).mpr τ.commutes⟩
  invFun σ :=
    { (σ : L ≃ₐ[K] L).toRingEquiv with
      commutes' := (mem_restrictionKernel_iff K L E σ).mp σ.2 }
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

private def restrictionQuotientEquiv [Normal K L] :
    ((L ≃ₐ[K] L) ⧸ restrictionKernel K L E) ≃* (E ≃ₐ[K] E) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective L)

end Kernel

section IntegerRings

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (L : Type uL) [Field L] [Algebra K₀ L] [Algebra K L] [IsScalarTower K₀ K L]
  (E : Type uE) [Field E] [Algebra K₀ E] [Algebra K E] [Algebra E L]
  [IsScalarTower K₀ E L] [IsScalarTower K E L] [Normal K E]
  (T : LocalField.TopologicalData K₀ L) (S : LocalField.TopologicalData K₀ E)

private theorem lowerGroupOrder_restrictionKernel (i : ℕ) :
    let := integerAction T K
    lowerGroupOrder T E i = lowerGroupCard T.Integers (restrictionKernel K L E) i := by
  let := integerAction T K
  let := integerAction T E
  exact (HerbrandBridge.lowerRamificationCard_of_equivariant (RingEquiv.refl T.Integers)
    (restrictionKernelEquiv K L E) (fun _ _ => Subtype.ext rfl) i).symm

/-- The integer ring of `E` embeds onto the fixed subring of the restriction kernel. -/
private def restrictionIntegerEquiv [IsGalois E L] :
    let := integerAction T K
    S.Integers ≃+* FixedPoints.subring T.Integers (restrictionKernel K L E) := by
  let := integerAction T K
  have hmem (x : E) : algebraMap E L x ∈ T.Integers ↔ x ∈ S.Integers :=
    algHom_mem_integers_iff S T (IsScalarTower.toAlgHom K₀ E L) x
  let f : S.Integers →+* FixedPoints.subring T.Integers (restrictionKernel K L E) :=
    { toFun x := ⟨⟨algebraMap E L (x : E), (hmem x).mpr x.2⟩,
        fun σ => Subtype.ext ((mem_restrictionKernel_iff K L E σ).mp σ.2 x)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (algebraMap E L)))
      map_mul' x y := Subtype.ext (Subtype.ext (map_mul (algebraMap E L) (x : E) (y : E)))
      map_zero' := Subtype.ext (Subtype.ext (map_zero (algebraMap E L)))
      map_add' x y := Subtype.ext (Subtype.ext (map_add (algebraMap E L) (x : E) (y : E))) }
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext ((algebraMap E L).injective (congrArg (fun z => (z.val : L)) h))
  · intro z
    have hfix (τ : L ≃ₐ[E] L) : τ ((z : T.Integers) : L) = ((z : T.Integers) : L) :=
      congrArg Subtype.val (z.2 (restrictionKernelEquiv K L E τ))
    obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
    exact ⟨⟨x, (hmem x).mp (hx ▸ (z : T.Integers).2)⟩, Subtype.ext (Subtype.ext hx)⟩

variable [IsScalarTower K₀ K E] [Normal K L] [IsGalois E L]

private theorem restrictionIntegerEquiv_symm_smul
    (g : (L ≃ₐ[K] L) ⧸ restrictionKernel K L E)
    (a : let := integerAction T K; FixedPoints.subring T.Integers (restrictionKernel K L E)) :
    let := integerAction T K
    let := integerAction S K
    (restrictionIntegerEquiv K L E T S).symm (g • a) =
      restrictionQuotientEquiv K L E g • (restrictionIntegerEquiv K L E T S).symm a := by
  let := integerAction T K
  let := integerAction S K
  let e := restrictionIntegerEquiv K L E T S
  change e.symm (g • a) = restrictionQuotientEquiv K L E g • e.symm a
  induction g using QuotientGroup.induction_on with
  | H σ =>
    obtain ⟨x, rfl⟩ := e.surjective a
    apply e.injective
    rw [e.apply_symm_apply, e.symm_apply_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ E (x : E)).symm

private theorem lowerGroupOrder_restrictionQuotient (i : ℕ) :
    let := integerAction T K
    lowerGroupOrder S K i =
      lowerGroupCard (FixedPoints.subring T.Integers (restrictionKernel K L E))
        ((L ≃ₐ[K] L) ⧸ restrictionKernel K L E) i := by
  let := integerAction T K
  let := integerAction S K
  exact HerbrandBridge.lowerRamificationCard_of_equivariant
    (restrictionIntegerEquiv K L E T S).symm (restrictionQuotientEquiv K L E)
    (restrictionIntegerEquiv_symm_smul K L E T S) i

end IntegerRings

section Tower

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (L : Type uL) [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
  [Algebra K L] [IsScalarTower K₀ K L]
  (E : Type uE) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E]
  [Algebra K E] [Algebra E L] [IsScalarTower K₀ K E] [IsScalarTower K₀ E L]
  [IsScalarTower K E L] [IsGalois K L] [IsGalois K E] [IsGalois E L]

/-- The phi tower law at every real index (Serre, *Local Fields*, IV §3, Proposition 15). -/
theorem herbrandPhiTower (T : LocalField.TopologicalData K₀ L)
    (S : LocalField.TopologicalData K₀ E) : HerbrandPhiTower K L E T S := by
  intro u
  let := integerAction T K
  let : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  have hrat : ∀ q : ℚ, herbrandPhi T K q = herbrandPhi S K (herbrandPhi T E q) := by
    intro q
    rcases le_or_gt q 0 with hq | hq
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      rw [herbrandPhi_of_nonpos T K hq', herbrandPhi_of_nonpos T E hq',
        herbrandPhi_of_nonpos S K hq']
    · have hφ := herbrandPhi_ratCast T E (lowerGroupOrder_restrictionKernel K L E T) hq.le
      have hφ0 : 0 ≤ herbrandPhiRat T.Integers (restrictionKernel K L E) q := by
        have h := herbrandPhi_pos T E (by exact_mod_cast hq : (0 : ℝ) < q)
        rw [hφ] at h
        exact_mod_cast h.le
      rw [herbrandPhi_ratCast T K (lowerGroupOrder_eq_source T K) hq.le, hφ,
        herbrandPhi_ratCast S K (lowerGroupOrder_restrictionQuotient K L E T S) hφ0,
        herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq
          (source_map_lowerRamificationGroup_mk K L T (restrictionKernel K L E)) hq.le]
  have hcont : Continuous fun x => herbrandPhi S K (herbrandPhi T E x) :=
    (herbrandPhi_continuous S K).comp (herbrandPhi_continuous T E)
  exact congrFun (Continuous.ext_on Rat.denseRange_cast
    (herbrandPhi_continuous T K) hcont (by rintro _ ⟨q, rfl⟩; exact hrat q)) u

/-- The psi tower law at every real index (Serre, *Local Fields*, IV §3, Proposition 15). -/
theorem herbrandPsiTower (T : LocalField.TopologicalData K₀ L)
    (S : LocalField.TopologicalData K₀ E) : HerbrandPsiTower K L E T S := by
  intro v
  apply (herbrandPhi_strictMono T K).injective
  rw [herbrandPhi_herbrandPsi, herbrandPhiTower K L E T S (herbrandPsi T E (herbrandPsi S K v)),
    herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi]

omit [IsScalarTower K₀ E L] in
/-- Upper numbering is compatible with the normal restriction to `E`
(Serre, *Local Fields*, IV §3, Proposition 14). -/
theorem upperRestrictionCompatibility (T : LocalField.TopologicalData K₀ L)
    (S : LocalField.TopologicalData K₀ E) : UpperRestrictionCompatibility K L E T S := by
  intro v hv
  let : IsScalarTower K₀ E L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K₀ K L, IsScalarTower.algebraMap_apply K E L,
      ← IsScalarTower.algebraMap_apply K₀ K E]
  let := integerAction T K
  let := integerAction S K
  let : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  rcases hv.eq_or_lt with rfl | hv
  · rw [upperRamificationGroup_neg_one, upperRamificationGroup_neg_one,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨qT, hqT0, hvqT, hT⟩ := exists_rat_upperRamificationGroup_eq T K hv
  obtain ⟨qS, hqS0, hvqS, hS⟩ := exists_rat_upperRamificationGroup_eq S K hv
  have hw0 : (0 : ℚ) ≤ min qT qS := le_min hqT0 hqS0
  have hvw : v ≤ ((min qT qS : ℚ) : ℝ) := by
    push_cast
    exact le_min hvqT hvqS
  rw [← hT _ hvw (by push_cast; exact min_le_left _ _),
    ← hS _ hvw (by push_cast; exact min_le_right _ _),
    upperRamificationGroup_ratCast T K (lowerGroupOrder_eq_source T K) hw0,
    upperRamificationGroup_ratCast S K (lowerGroupOrder_restrictionQuotient K L E T S) hw0]
  change (upperGroupRat T.Integers (L ≃ₐ[K] L) (min qT qS)).map
      ((restrictionQuotientEquiv K L E).toMonoidHom.comp
        (QuotientGroup.mk' (restrictionKernel K L E))) = _
  rw [← Subgroup.map_map, upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq
    (source_map_lowerRamificationGroup_mk K L T (restrictionKernel K L E)) _ hw0]
  exact HerbrandBridge.map_lowerRamificationGroup_of_equivariant
    (restrictionIntegerEquiv K L E T S).symm (restrictionQuotientEquiv K L E)
    (restrictionIntegerEquiv_symm_smul K L E T S) _

variable (K₀) in
/-- The subgroup and quotient formulas and both Herbrand tower laws for finite Galois towers. -/
theorem finiteHerbrandQuotientTower : FiniteHerbrandQuotientTower K₀ K L E := by
  intro T S
  exact ⟨lowerSubgroupCompatibility K L T, herbrandNormalSubgroup K L T,
    upperQuotientCompatibility K L T, herbrandPhiTower K L E T S,
    herbrandPsiTower K L E T S, upperRestrictionCompatibility K L E T S⟩

end Tower

end Langlands.Ramification.Local
