import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof

/-!
# Herbrand's tower laws for independently presented intermediate fields

For a compatible tower `K → E → L` of actual p-adic fields with `L/K` and `E/K`
Galois, the kernel of the actual normal restriction `Gal(L/K) → Gal(E/K)` is
identified with `Gal(L/E)`, and its fixed subring in the supplied integer ring
of `L` with the supplied integer ring of `E`. The ported Herbrand theorem then
proves the Library propositions `UpperRestrictionCompatibility`,
`HerbrandPhiTower` and `HerbrandPsiTower`.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Ramification.HerbrandBridge

open IsLocalRing

universe uK uE uL

section Tower

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (L : PadicField.{uL} p)
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  (E : PadicField.{uE} p)
  [Algebra K.Carrier E.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower K.Carrier E.Carrier L.Carrier]

include K in
/-- The p-adic tower through `E` follows from the other tower compatibilities. -/
theorem padicScalarTower_of_tower : IsScalarTower (Padic p) E.Carrier L.Carrier :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Padic p) K.Carrier L.Carrier,
      IsScalarTower.algebraMap_apply K.Carrier E.Carrier L.Carrier,
      ← IsScalarTower.algebraMap_apply (Padic p) K.Carrier E.Carrier]

/-- The kernel of the actual normal restriction to `E`. -/
abbrev towerKernel [Normal K.Carrier E.Carrier] : Subgroup Gal(L.Carrier/K.Carrier) :=
  (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier).ker

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier E.Carrier] in
theorem restrictScalars_mem_towerKernel [Normal K.Carrier E.Carrier]
    (τ : L.Carrier ≃ₐ[E.Carrier] L.Carrier) :
    τ.restrictScalars K.Carrier ∈ towerKernel K L E := by
  rw [MonoidHom.mem_ker]
  ext x
  have h := AlgEquiv.restrictNormal_commutes (τ.restrictScalars K.Carrier) E.Carrier x
  rw [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes] at h
  rw [AlgEquiv.one_apply]
  exact (algebraMap E.Carrier L.Carrier).injective h

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier E.Carrier] in
theorem algebraMap_fixed_of_mem_towerKernel [Normal K.Carrier E.Carrier]
    {σ : Gal(L.Carrier/K.Carrier)} (hσ : σ ∈ towerKernel K L E) (x : E.Carrier) :
    σ (algebraMap E.Carrier L.Carrier x) = algebraMap E.Carrier L.Carrier x := by
  have h := AlgEquiv.restrictNormal_commutes σ E.Carrier x
  have h1 : σ.restrictNormal E.Carrier = 1 := hσ
  rw [h1, AlgEquiv.one_apply] at h
  exact h.symm

/-- The automorphisms of `L` over `E` are the kernel of the restriction to `E`,
with the same underlying maps. -/
def towerSubgroupEquiv [Normal K.Carrier E.Carrier] :
    (L.Carrier ≃ₐ[E.Carrier] L.Carrier) ≃* towerKernel K L E where
  toFun τ := ⟨τ.restrictScalars K.Carrier, restrictScalars_mem_towerKernel K L E τ⟩
  invFun σ :=
    { (σ : Gal(L.Carrier/K.Carrier)).toRingEquiv with
      commutes' := fun x => algebraMap_fixed_of_mem_towerKernel K L E σ.2 x }
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

variable [IsScalarTower (Padic p) E.Carrier L.Carrier] (T : L.TopologicalData)
  (S : E.TopologicalData)

omit [IsScalarTower (Padic p) K.Carrier E.Carrier] in
/-- The Library lower-group orders of `L` over `E` are the source orders of the
restriction kernel. -/
theorem lowerGroupOrder_tower [Normal K.Carrier E.Carrier] (i : ℕ) :
    letI := Padic.integerAction T K.Carrier
    Padic.lowerGroupOrder T E.Carrier i =
      IsLocalRing.lowerRamificationCard T.Integers (towerKernel K L E) i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction T E.Carrier
  exact (lowerRamificationCard_of_equivariant (RingEquiv.refl T.Integers)
    (towerSubgroupEquiv K L E) (fun _ _ => Subtype.ext rfl) i).symm

/-- The supplied integer ring of `E`, embedded in the fixed subring of the
restriction kernel. -/
def towerIntegerHom [Normal K.Carrier E.Carrier] :
    letI := Padic.integerAction T K.Carrier
    S.Integers →+* FixedPoints.subring T.Integers (towerKernel K L E) := by
  letI := Padic.integerAction T K.Carrier
  exact
  { toFun x := ⟨⟨algebraMap E.Carrier L.Carrier (x : E.Carrier),
        (PadicField.TopologicalData.relative_mem_integers_iff S T _).mpr x.2⟩,
      fun h => Subtype.ext (algebraMap_fixed_of_mem_towerKernel K L E h.2 (x : E.Carrier))⟩
    map_one' := Subtype.ext (Subtype.ext (map_one (algebraMap E.Carrier L.Carrier)))
    map_mul' x y := Subtype.ext (Subtype.ext
      (map_mul (algebraMap E.Carrier L.Carrier) (x : E.Carrier) (y : E.Carrier)))
    map_zero' := Subtype.ext (Subtype.ext (map_zero (algebraMap E.Carrier L.Carrier)))
    map_add' x y := Subtype.ext (Subtype.ext
      (map_add (algebraMap E.Carrier L.Carrier) (x : E.Carrier) (y : E.Carrier))) }

omit [IsScalarTower (Padic p) K.Carrier E.Carrier] in
@[simp] theorem towerIntegerHom_coe [Normal K.Carrier E.Carrier] (x : S.Integers) :
    letI := Padic.integerAction T K.Carrier
    (((towerIntegerHom K L E T S x : FixedPoints.subring T.Integers (towerKernel K L E)) :
      T.Integers) : L.Carrier) = algebraMap E.Carrier L.Carrier (x : E.Carrier) := rfl

omit [IsScalarTower (Padic p) K.Carrier E.Carrier] in
theorem towerIntegerHom_bijective [IsGalois E.Carrier L.Carrier] [Normal K.Carrier E.Carrier] :
    Function.Bijective (towerIntegerHom K L E T S) := by
  letI := Padic.integerAction T K.Carrier
  constructor
  · intro x y h
    exact Subtype.ext ((algebraMap E.Carrier L.Carrier).injective
      (congrArg (fun z : FixedPoints.subring T.Integers (towerKernel K L E) =>
        ((z : T.Integers) : L.Carrier)) h))
  · intro z
    have hfix : ∀ f : Gal(L.Carrier/E.Carrier),
        f ((z : T.Integers) : L.Carrier) = ((z : T.Integers) : L.Carrier) := fun f =>
      congrArg Subtype.val (z.2 (towerSubgroupEquiv K L E f))
    obtain ⟨e, he⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      ((z : T.Integers) : L.Carrier)).mpr hfix
    have hmem : e ∈ S.Integers :=
      (PadicField.TopologicalData.relative_mem_integers_iff S T e).mp
        (he ▸ (z : T.Integers).2)
    exact ⟨⟨e, hmem⟩, Subtype.ext (Subtype.ext he)⟩

/-- The fixed subring of the restriction kernel in the supplied integer ring of
`L` is the supplied integer ring of `E`. -/
def towerIntegerEquiv [IsGalois E.Carrier L.Carrier] [Normal K.Carrier E.Carrier] :
    letI := Padic.integerAction T K.Carrier
    FixedPoints.subring T.Integers (towerKernel K L E) ≃+* S.Integers :=
  (RingEquiv.ofBijective (towerIntegerHom K L E T S)
    (towerIntegerHom_bijective K L E T S)).symm

theorem towerIntegerHom_smul [Normal K.Carrier E.Carrier] (σ : Gal(L.Carrier/K.Carrier))
    (x : S.Integers) :
    letI := Padic.integerAction T K.Carrier
    letI := Padic.integerAction S K.Carrier
    towerIntegerHom K L E T S
        ((AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier σ) • x) =
      (QuotientGroup.mk σ : Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) •
        towerIntegerHom K L E T S x := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  apply Subtype.ext
  apply Subtype.ext
  change algebraMap E.Carrier L.Carrier ((σ.restrictNormal E.Carrier) (x : E.Carrier)) =
    σ (algebraMap E.Carrier L.Carrier (x : E.Carrier))
  exact AlgEquiv.restrictNormal_commutes σ E.Carrier (x : E.Carrier)

/-- The quotient by the restriction kernel is the Galois group of `E`. -/
def towerQuotientEquiv [IsGalois K.Carrier L.Carrier] [Normal K.Carrier E.Carrier] :
    (Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) ≃* Gal(E.Carrier/K.Carrier) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective _)

theorem towerIntegerEquiv_smul [IsGalois K.Carrier L.Carrier] [IsGalois E.Carrier L.Carrier]
    [Normal K.Carrier E.Carrier]
    (g : Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E)
    (a : letI := Padic.integerAction T K.Carrier
      FixedPoints.subring T.Integers (towerKernel K L E)) :
    letI := Padic.integerAction T K.Carrier
    letI := Padic.integerAction S K.Carrier
    towerIntegerEquiv K L E T S (g • a) =
      towerQuotientEquiv K L E g • towerIntegerEquiv K L E T S a := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  induction g using QuotientGroup.induction_on with
  | H σ =>
    apply (towerIntegerHom_bijective K L E T S).1
    have h1 : towerIntegerHom K L E T S (towerIntegerEquiv K L E T S
        ((QuotientGroup.mk σ : Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) • a)) =
        (QuotientGroup.mk σ : Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) • a :=
      (RingEquiv.ofBijective (towerIntegerHom K L E T S)
        (towerIntegerHom_bijective K L E T S)).apply_symm_apply _
    have h2 : towerIntegerHom K L E T S (towerIntegerEquiv K L E T S a) = a :=
      (RingEquiv.ofBijective (towerIntegerHom K L E T S)
        (towerIntegerHom_bijective K L E T S)).apply_symm_apply _
    rw [h1]
    change _ = towerIntegerHom K L E T S
      ((AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier σ) •
        towerIntegerEquiv K L E T S a)
    rw [towerIntegerHom_smul, h2]

/-- A subgroup whose image in the quotient is a source lower group of the
fixed subring restricts to the corresponding Library lower group of `E`. -/
theorem map_restrictNormalHom_eq_tower [IsGalois K.Carrier L.Carrier]
    [IsGalois E.Carrier L.Carrier] [Normal K.Carrier E.Carrier]
    (X : Subgroup Gal(L.Carrier/K.Carrier)) (i : ℕ)
    (hX : letI := Padic.integerAction T K.Carrier
      X.map (QuotientGroup.mk' (towerKernel K L E)) =
        IsLocalRing.lowerRamificationGroup (FixedPoints.subring T.Integers (towerKernel K L E))
          (Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) i) :
    X.map (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier) =
      Padic.lowerRamificationGroup S K.Carrier i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  have hf : AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier =
      (towerQuotientEquiv K L E : _ →* _).comp (QuotientGroup.mk' (towerKernel K L E)) :=
    MonoidHom.ext fun _ => rfl
  rw [hf, ← Subgroup.map_map, hX]
  exact map_lowerRamificationGroup_of_equivariant (towerIntegerEquiv K L E T S)
    (towerQuotientEquiv K L E) (towerIntegerEquiv_smul K L E T S) i

/-- The Library lower-group orders of `E` over `K` are the source orders of the
quotient acting on the fixed subring. -/
theorem lowerGroupOrder_towerQuotient [IsGalois K.Carrier L.Carrier]
    [IsGalois E.Carrier L.Carrier] [Normal K.Carrier E.Carrier] (i : ℕ) :
    letI := Padic.integerAction T K.Carrier
    Padic.lowerGroupOrder S K.Carrier i =
      IsLocalRing.lowerRamificationCard (FixedPoints.subring T.Integers (towerKernel K L E))
        (Gal(L.Carrier/K.Carrier) ⧸ towerKernel K L E) i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  exact lowerRamificationCard_of_equivariant (towerIntegerEquiv K L E T S)
    (towerQuotientEquiv K L E) (towerIntegerEquiv_smul K L E T S) i

/-- The phi tower law, for every real argument. -/
theorem herbrandPhi_tower [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] (u : ℝ) :
    Padic.herbrandPhi T K.Carrier u =
      Padic.herbrandPhi S K.Carrier (Padic.herbrandPhi T E.Carrier u) := by
  letI := Padic.integerAction T K.Carrier
  haveI := finiteDimensional_carrier K L
  have hrat : ∀ q : ℚ, Padic.herbrandPhi T K.Carrier q =
      Padic.herbrandPhi S K.Carrier (Padic.herbrandPhi T E.Carrier q) := by
    intro q
    rcases le_or_gt q 0 with hq | hq
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      rw [Padic.herbrandPhi_of_nonpos T _ hq', Padic.herbrandPhi_of_nonpos T _ hq',
        Padic.herbrandPhi_of_nonpos S _ hq']
    · have hH := herbrandPhi_ratCast T E.Carrier (lowerGroupOrder_tower K L E T) hq.le
      have hφ0 : 0 ≤ IsLocalRing.herbrandPhi T.Integers (towerKernel K L E) q := by
        have h := Padic.herbrandPhi_pos T E.Carrier (by exact_mod_cast hq : (0 : ℝ) < q)
        rw [hH] at h
        exact_mod_cast h.le
      rw [herbrandPhi_ratCast T K.Carrier (lowerGroupOrder_eq_source T K.Carrier) hq.le, hH,
        herbrandPhi_ratCast S K.Carrier (lowerGroupOrder_towerQuotient K L E T S) hφ0,
        IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
          (source_map_lowerRamificationGroup_mk K L T (towerKernel K L E)) hq.le]
  have hcont : Continuous fun u => Padic.herbrandPhi S K.Carrier
      (Padic.herbrandPhi T E.Carrier u) :=
    (Padic.herbrandPhi_continuous S K.Carrier).comp (Padic.herbrandPhi_continuous T _)
  exact congrFun (Continuous.ext_on Rat.denseRange_cast
    (Padic.herbrandPhi_continuous T K.Carrier) hcont (by rintro _ ⟨q, rfl⟩; exact hrat q)) u

theorem herbrandPhiTower [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] : Padic.HerbrandPhiTower K L E T S :=
  fun u _ => herbrandPhi_tower K L E T S u

/-- The inverse tower law, for every real argument. -/
theorem herbrandPsi_tower [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] (v : ℝ) :
    Padic.herbrandPsi T K.Carrier v =
      Padic.herbrandPsi T E.Carrier (Padic.herbrandPsi S K.Carrier v) := by
  apply (Padic.herbrandPhi_strictMono T K.Carrier).injective
  rw [Padic.herbrandPhi_herbrandPsi, herbrandPhi_tower K L E T S, Padic.herbrandPhi_herbrandPsi,
    Padic.herbrandPhi_herbrandPsi]

theorem herbrandPsiTower [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] : Padic.HerbrandPsiTower K L E T S :=
  fun v _ => herbrandPsi_tower K L E T S v

/-- Herbrand's theorem in upper numbering for the actual normal restriction to `E`. -/
theorem upperRestrictionCompatibility_aux [IsGalois K.Carrier L.Carrier]
    [IsGalois K.Carrier E.Carrier] [IsGalois E.Carrier L.Carrier] (v : ℝ) (hv : -1 ≤ v) :
    (Padic.upperRamificationGroup T K.Carrier v).map
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier) =
        Padic.upperRamificationGroup S K.Carrier v := by
  letI := Padic.integerAction T K.Carrier
  haveI := finiteDimensional_carrier K L
  haveI := finiteDimensional_carrier K E
  rcases hv.eq_or_lt with rfl | hv
  · rw [Padic.upperRamificationGroup_neg_one, Padic.upperRamificationGroup_neg_one,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨qT, hqT0, hvqT, hT⟩ := exists_rat_upperRamificationGroup_eq T K.Carrier hv
  obtain ⟨qS, hqS0, hvqS, hS⟩ := exists_rat_upperRamificationGroup_eq S K.Carrier hv
  have hw0 : (0 : ℚ) ≤ min qT qS := le_min hqT0 hqS0
  have hvw : v ≤ ((min qT qS : ℚ) : ℝ) := by
    push_cast
    exact le_min hvqT hvqS
  rw [← hT _ hvw (by push_cast; exact min_le_left _ _),
    ← hS _ hvw (by push_cast; exact min_le_right _ _),
    upperRamificationGroup_ratCast T K.Carrier (lowerGroupOrder_eq_source T K.Carrier) hw0,
    upperRamificationGroup_ratCast S K.Carrier (lowerGroupOrder_towerQuotient K L E T S) hw0]
  exact map_restrictNormalHom_eq_tower K L E T S _ _
    (IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
      (source_map_lowerRamificationGroup_mk K L T (towerKernel K L E)) _ hw0)

omit [IsScalarTower (Padic p) E.Carrier L.Carrier] in
theorem upperRestrictionCompatibility [IsGalois K.Carrier L.Carrier]
    [IsGalois K.Carrier E.Carrier] [IsGalois E.Carrier L.Carrier] :
    Padic.UpperRestrictionCompatibility K L E T S := by
  haveI := padicScalarTower_of_tower K L E
  exact upperRestrictionCompatibility_aux K L E T S

end Tower

end Langlands.Ramification.HerbrandBridge
