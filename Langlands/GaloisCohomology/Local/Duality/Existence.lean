import Langlands.GaloisCohomology.Local.Duality.Main

/-!
# The existence theorem for norm groups containing `n`-th powers

For a nonarchimedean local field `K`, a separable closure `Ksep`, an integer `n` invertible in `K`
and a subgroup `H ⊆ Kˣ` containing `Kˣⁿ`, there is a finite abelian extension `F/K` inside `Ksep`
with norm group `N(Fˣ) = H` (`exists_isAbelianGalois_fieldNormSubgroup_eq`).

The proof is the Kummer argument through local duality in degree one. Let `X = H¹(G, ℤ/n)` (the
characters of `G = Gal(Ksep/K)` of order dividing `n`) and `Y = H¹(G, μ_n) ≅ Kˣ/Kˣⁿ` (Kummer). The
cup product `X × Y → H²(G, μ_n) ≅ ℤ/n` is perfect (`Duality/Main.lean`). Let `A ⊆ X` be the
annihilator of the image of `H`, and `F` the fixed field of the common kernel of the characters in
`A`. A norm from `F` is a norm from the field of every character of `A`, so its Kummer class is
orthogonal to `A`, hence (double annihilator) lies in the image of `H`: `N(Fˣ) ⊆ H`. And
`[Kˣ : N(Fˣ)] = [F : K] = |G/N| ≤ |A| = [Kˣ : H]` (norm index; `G/N` embeds into `Hom(A, ℤ/n)`),
so `N(Fˣ) = H`. The argument is carried out over the fixed field of an open subgroup and then
transported to `K` itself.
-/

noncomputable section

open CategoryTheory

universe u

namespace Langlands.ProfiniteCohomology

section Characters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

theorem zmodCocycleHom_sub (z z' : cocycles (zmodRep.{u} G n) 1) (g : G) :
    zmodCocycleHom (z - z') g = zmodCocycleHom z g - zmodCocycleHom z' g := by
  simp [zmodCocycleHom, cochainOf, map_sub]
  rfl

theorem zmodCocycleHom_add (z z' : cocycles (zmodRep.{u} G n) 1) (g : G) :
    zmodCocycleHom (z + z') g = zmodCocycleHom z g + zmodCocycleHom z' g := by
  simp [zmodCocycleHom, cochainOf, map_add]
  rfl

/-- For trivial coefficients, a class of degree one determines its cocycle. -/
theorem zmodCocycleHom_eq_of_cohomologyπ_eq {z z' : cocycles (zmodRep.{u} G n) 1}
    (h : cohomologyπ _ 1 z = cohomologyπ _ 1 z') : zmodCocycleHom z = zmodCocycleHom z' := by
  have h0 := (cohomologyπ_one_eq_zero_iff_of_trivial (zmodRep.{u} G n) (fun _ _ => rfl)
    (z - z')).1 (by rw [map_sub, h, sub_self])
  funext g
  have h1 : zmodCocycleHom (z - z') g = 0 := congrArg ULift.down (h0 g)
  rw [zmodCocycleHom_sub, sub_eq_zero] at h1
  exact h1

end Characters

end Langlands.ProfiniteCohomology

namespace Langlands.GaloisCohomology.Local

open Langlands.ProfiniteCohomology ClassFieldTheory.Local IntermediateField GroupCoh

section Open

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_mul (W : Subgroup Gal(Ksep/K)) (a b : (fixedField W)ˣ) :
    unitsInvariantOpen W (a * b) = unitsInvariantOpen W a + unitsInvariantOpen W b := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep)
    (a * b)) = Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) +
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) b)
  rw [map_mul]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_injective (W : Subgroup Gal(Ksep/K)) :
    Function.Injective (unitsInvariantOpen (K := K) (Ksep := Ksep) W) := by
  intro a b h
  have h1 := congrArg (fun v : (Rep.res W.subtype (unitsModule K Ksep)).ρ.invariants =>
    ((Additive.toMul (v : Rep.res W.subtype (unitsModule K Ksep)) : Ksepˣ) : Ksep)) h
  simp only [coe_unitsInvariantOpen, toMul_ofMul, Units.coe_map, MonoidHom.coe_ofClass] at h1
  exact Units.ext (Subtype.ext h1)

/-- The Kummer map `Eˣ → H¹(U, μ_n)` of the fixed field `E` of an open subgroup `U`. -/
def kummerHom (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Additive (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →+
      cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 1 :=
  AddMonoidHom.mk' (fun a => (δ (kummerSequenceRes_shortExact n (U : Subgroup Gal(Ksep/K)) hn)
      0 1 rfl).hom ((zeroIso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a.toMul)))
    fun a b => by rw [toMul_add, unitsInvariantOpen_mul, map_add, map_add]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem kummerHom_apply (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (a : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ) :
    kummerHom hn U (Additive.ofMul a) = (δ (kummerSequenceRes_shortExact n
      (U : Subgroup Gal(Ksep/K)) hn) 0 1 rfl).hom
        ((zeroIso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem kummerHom_surjective (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Surjective (kummerHom hn U) := fun y => by
  obtain ⟨a, ha⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  exact ⟨Additive.ofMul a, ha⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A unit with trivial Kummer class is an `n`-th power. -/
theorem exists_pow_eq_of_kummerHom_eq_zero (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ) (hb : kummerHom hn U (Additive.ofMul b) = 0) :
    ∃ c, c ^ n = b := by
  obtain ⟨w, hw⟩ := (δ_zeroIso_inv_eq_zero_iff
    (kummerSequenceRes_shortExact n (U : Subgroup Gal(Ksep/K)) hn) _).1 hb
  obtain ⟨c, rfl⟩ := exists_unitsInvariantOpen_eq (U : Subgroup Gal(Ksep/K)) w
  refine ⟨c, unitsInvariantOpen_injective (U : Subgroup Gal(Ksep/K)) ?_⟩
  simp only [toMul_ofMul] at hw
  rw [unitsInvariantOpen_pow, ← hw]
  apply Subtype.ext
  exact (kummerSequenceRes_g_hom_apply n (U : Subgroup Gal(Ksep/K)) _).symm

/-- The character `Gal(Ksep/E) → ℤ/n` of a class of `H¹(U, ℤ/n)`. -/
def classChar (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) : ZMod n :=
  zmodCocycleHom (cohomologyπ_surjective _ 1 x).choose (galFixedFieldEquivOpen U σ)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem classChar_cohomologyπ (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    classChar U (cohomologyπ _ 1 z) σ = zmodCocycleHom z (galFixedFieldEquivOpen U σ) := by
  rw [classChar, zmodCocycleHom_eq_of_cohomologyπ_eq
    (cohomologyπ_surjective _ 1 (cohomologyπ _ 1 z)).choose_spec]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem classChar_add (U : OpenSubgroup Gal(Ksep/K))
    (x y : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    classChar U (x + y) σ = classChar U x σ + classChar U y σ := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  obtain ⟨z', rfl⟩ := cohomologyπ_surjective _ 1 y
  rw [← map_add, classChar_cohomologyπ, classChar_cohomologyπ, classChar_cohomologyπ,
    zmodCocycleHom_add]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem classChar_mul (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    classChar U x (σ * τ) = classChar U x σ + classChar U x τ := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  rw [classChar_cohomologyπ, classChar_cohomologyπ, classChar_cohomologyπ, map_mul,
    zmodCocycleHom_mul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem classChar_one (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1) :
    classChar U x 1 = 0 := by
  have h := classChar_mul U x 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem classChar_inv (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    classChar U x σ⁻¹ = -classChar U x σ := by
  have h := classChar_mul U x σ⁻¹ σ
  rw [inv_mul_cancel, classChar_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_charKer_openChar_iff (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) :
    σ ∈ charKer (charAdd (openChar n U z)) ↔ classChar U (cohomologyπ _ 1 z) σ = 0 := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  rw [mem_charKer, charAdd_apply, openChar_apply, AddEquiv.map_eq_zero_iff, classChar_cohomologyπ,
    toMul_ofMul]
  exact ⟨fun h => zmodToQZ_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem isOpen_charKer_openChar (U : OpenSubgroup Gal(Ksep/K))
    (z : cocycles (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1) :
    IsOpen (charKer (charAdd (openChar n U z)) :
      Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) := by
  have e : (charKer (charAdd (openChar n U z)) :
      Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) =
      (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0} := by
    ext g
    exact mem_charKer
  rw [e]
  exact (isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)

end Open

section ExistenceOpen

open LocalFieldTheory

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For a subgroup `H ⊆ Eˣ` containing `Eˣⁿ` (`E` the fixed field of `U`), a unit whose Kummer class
lies in the image of `H` lies in `H`. -/
theorem mem_of_kummerHom_mem_map (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    {H : Subgroup (fixedField (U : Subgroup Gal(Ksep/K)))ˣ}
    (hH : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      (fixedField (U : Subgroup Gal(Ksep/K)))ˣ).range ≤ H)
    (b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ)
    (hb : kummerHom (Ksep := Ksep) hn U (Additive.ofMul b) ∈
      (Subgroup.toAddSubgroup H).map (kummerHom (Ksep := Ksep) hn U)) : b ∈ H := by
  obtain ⟨a, ha, hκ⟩ := hb
  have h0 : kummerHom (Ksep := Ksep) hn U (Additive.ofMul (b * (Additive.toMul a)⁻¹)) = 0 := by
    rw [ofMul_mul, ofMul_inv, ofMul_toMul, map_add, map_neg, hκ, add_neg_cancel]
  obtain ⟨c, hc⟩ := exists_pow_eq_of_kummerHom_eq_zero hn U _ h0
  have hcH : c ^ n ∈ H := hH (x := c ^ n) ⟨c, rfl⟩
  rw [hc] at hcH
  have ha' : Additive.toMul a ∈ H := ha
  simpa using H.mul_mem hcH ha'

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For a subgroup `H ⊆ Eˣ` containing `Eˣⁿ` (`E` the fixed field of `U`), the quotient of
`H¹(U, μ_n)` by the Kummer image of `H` has `[Eˣ : H]` elements. -/
theorem card_quotient_map_kummerHom (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    {H : Subgroup (fixedField (U : Subgroup Gal(Ksep/K)))ˣ}
    (hH : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      (fixedField (U : Subgroup Gal(Ksep/K)))ˣ).range ≤ H) :
    Nat.card (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 1 ⧸
      (Subgroup.toAddSubgroup H).map (kummerHom (Ksep := Ksep) hn U)) = H.index := by
  set κ := kummerHom (Ksep := Ksep) hn U
  set S := (Subgroup.toAddSubgroup H).map κ
  let ψ := (QuotientAddGroup.mk' S).comp κ
  have hψs : Function.Surjective ψ :=
    (QuotientAddGroup.mk'_surjective S).comp (kummerHom_surjective hn U)
  have hψker : ψ.ker = Subgroup.toAddSubgroup H := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    constructor
    · intro ha
      have := mem_of_kummerHom_mem_map hn U hH (Additive.toMul a) (by rwa [ofMul_toMul])
      exact this
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv, hψker,
    ← AddSubgroup.index, Subgroup.index_toAddSubgroup]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
/-- The fixed field of an open normal subgroup `N` of `Gal(Ksep/E)` containing all commutators is a
finite abelian extension of `E`. -/
theorem finiteDimensional_isAbelianGalois_fixedField_of_commutator_mem {E : Type*} [Field E]
    [Algebra E Ksep] [IsGalois E Ksep] (N : Subgroup Gal(Ksep/E)) (hNnormal : N.Normal)
    (hNopen : IsOpen (N : Set Gal(Ksep/E))) (hcomm : ∀ σ τ : Gal(Ksep/E), σ * τ * σ⁻¹ * τ⁻¹ ∈ N) :
    FiniteDimensional E (fixedField N) ∧ IsAbelianGalois E (fixedField N) := by
  set F := fixedField N with hFdef
  have hfix : F.fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, Subgroup.isClosed_of_isOpen N hNopen⟩
  have hfin : FiniteDimensional E F :=
    (InfiniteGalois.isOpen_iff_finite F).1 (by rw [hfix]; exact hNopen)
  have hgal : IsGalois E F :=
    (InfiniteGalois.normal_iff_isGalois F).1 (by rw [hfix]; infer_instance)
  have hc : ∀ σ' τ' : Gal(F/E), σ' * τ' = τ' * σ' := by
    intro σ' τ'
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := F) (E := Ksep) σ'
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := F) (E := Ksep) τ'
    have hk : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom F).ker := by
      rw [F.restrictNormalHom_ker, hfix]
      exact hcomm σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have key : ∀ {M : Type _} [Group M] (x y : M), x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
      intro M _ x y hxy
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
    exact key _ _ hk
  exact ⟨hfin, { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hc⟩⟩ }⟩

/-- A subgroup `H` of `Eˣ` (`E` the fixed field of `U`) containing the norm group of a finite
abelian extension `F` of `E`, with `[F : E] ≤ [Eˣ : H]` and `[Eˣ : H]` finite, is that norm group. -/
theorem fieldNormSubgroup_eq_of_le_of_finrank_le (U : OpenSubgroup Gal(Ksep/K))
    (F : IntermediateField (fixedField (U : Subgroup Gal(Ksep/K))) Ksep)
    [FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K))) F]
    [IsAbelianGalois (fixedField (U : Subgroup Gal(Ksep/K))) F]
    (H : Subgroup (fixedField (U : Subgroup Gal(Ksep/K)))ˣ)
    (hle : DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F ≤ H)
    (hHpos : 0 < H.index)
    (hfinrank : Module.finrank (fixedField (U : Subgroup Gal(Ksep/K))) F ≤ H.index) :
    DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F = H := by
  let := LocalField.FiniteExtension.normedField K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.valuativeRel K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.isLocalField K (fixedField (U : Subgroup Gal(Ksep/K)))
  have hidx := index_fieldNormSubgroup_of_isAbelianGalois (fixedField (U : Subgroup Gal(Ksep/K))) F
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hidx] at h1
  have hrel : (DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F).relIndex H = 1 := by
    have h2 : (DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F).relIndex H * H.index ≤
        1 * H.index := by rw [h1, one_mul]; exact hfinrank
    have h3 := Nat.le_of_mul_le_mul_right h2 hHpos
    have h4 : (DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F).relIndex H ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact Module.finrank_pos.ne' h1.symm
    omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.1 hrel)

/-- The existence theorem over the fixed field `E` of an open subgroup `U` (with the Library's
spectral local-field structure): every subgroup `H ⊆ Eˣ` containing `Eˣⁿ` is the norm group of a
finite abelian extension of `E` inside `Ksep`. -/
theorem exists_fieldNormSubgroup_eq_of_range_pow_le (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (H : Subgroup (fixedField (U : Subgroup Gal(Ksep/K)))ˣ)
    (hH : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      (fixedField (U : Subgroup Gal(Ksep/K)))ˣ).range ≤ H) :
    ∃ F : IntermediateField (fixedField (U : Subgroup Gal(Ksep/K))) Ksep,
      FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K))) F ∧
      IsAbelianGalois (fixedField (U : Subgroup Gal(Ksep/K))) F ∧
      DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F = H := by
  have : NeZero n := ⟨fun h0 => hn (by simp [h0])⟩
  set X := cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1
  set Y := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 1
  set β := bilinAddHom (cupPairing (zmodMulPairing n
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n))
    (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hn)))
    (show 1 + 1 = 2 from rfl)) with hβ
  set t := (rootsOfUnityInvariant hn U).toAddMonoidHom with ht
  have hP : IsPerfectPairing β t :=
    isPerfectPairing_rootsOfUnityInvariant hn U (cardCohomologyOneLe K Ksep n hn U)
  have hYfin : Finite Y := finite_cohomology_one_res_rootsOfUnityModule K Ksep hn U
  have hXfin : Finite X := Finite.of_injective _ hP.1.1
  have hY : ∀ y : Y, n • y = 0 := nsmul_cohomology_eq_zero _
    (nsmul_res_rootsOfUnityModule_eq_zero hn _) 1
  have hX : ∀ x : X, n • x = 0 := nsmul_cohomology_eq_zero _ (nsmul_zmodRep_eq_zero _ n) 1
  set κ := kummerHom (Ksep := Ksep) hn U
  set S : AddSubgroup Y := (Subgroup.toAddSubgroup H).map κ
  set A := leftAnnihilator β t S
  -- the common kernel `N` of the characters of `A`
  let N : Subgroup Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K)))) :=
    { carrier := {σ | ∀ x ∈ A, classChar U x σ = 0}
      mul_mem' := fun ha hb x hx => by rw [classChar_mul, ha x hx, hb x hx, add_zero]
      one_mem' := fun x _ => classChar_one U x
      inv_mem' := fun ha x hx => by rw [classChar_inv, ha x hx, neg_zero] }
  have hmemN : ∀ σ, σ ∈ N ↔ ∀ x ∈ A, classChar U x σ = 0 := fun σ => Iff.rfl
  have hNnormal : N.Normal := ⟨fun σ hσ τ x hx => by
    rw [classChar_mul, classChar_mul, classChar_inv, hσ x hx, add_zero, add_neg_cancel]⟩
  have hcomm : ∀ σ τ : Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K)))), σ * τ * σ⁻¹ * τ⁻¹ ∈ N := fun σ τ x _ => by
    rw [classChar_mul, classChar_mul, classChar_mul, classChar_inv, classChar_inv]
    abel
  have hker_open : ∀ x : X, IsOpen {σ : Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K)))) | classChar U x σ = 0} := fun x => by
    obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
    have e : {σ : Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K)))) | classChar U (cohomologyπ _ 1 z) σ = 0} =
        (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K))))) := by
      ext σ
      exact (mem_charKer_openChar_iff hn U z σ).symm
    rw [e]
    exact isOpen_charKer_openChar U z
  have hNopen : IsOpen (N : Set Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K))))) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) (Filter.mem_of_superset
      ((Filter.biInter_mem (Set.toFinite (A : Set X))).2 fun x _ =>
        (hker_open x).mem_nhds (classChar_one U x)) ?_)
    intro σ hσ x hx
    exact Set.mem_iInter₂.1 hσ x hx
  -- the field `F`
  set F := fixedField N with hFdef
  have hfix : F.fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, Subgroup.isClosed_of_isOpen N hNopen⟩
  obtain ⟨hfin, habel⟩ :=
    finiteDimensional_isAbelianGalois_fixedField_of_commutator_mem N hNnormal hNopen hcomm
  have hgal : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) F := habel.toIsGalois
  -- units whose Kummer class lies in `S` lie in `H`
  have hS : ∀ b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ, κ (Additive.ofMul b) ∈ S → b ∈ H :=
    mem_of_kummerHom_mem_map hn U hH
  -- norms from `F` lie in `H`
  have hle : DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) F ≤ H := by
    intro b hb
    refine hS b (mem_of_forall_leftAnnihilator hX hY hP S fun x hx => ?_)
    obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
    set Fz := fixedField (charKer (charAdd (openChar n U z)))
    have hFz : Fz ≤ F := by
      refine IntermediateField.fixedField_antitone ?_
      intro σ hσ
      exact (mem_charKer_openChar_iff hn U z σ).2 (hσ _ hx)
    have hFzfin : FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K))) Fz :=
      (InfiniteGalois.isOpen_iff_finite Fz).1 (by
        rw [InfiniteGalois.fixingSubgroup_fixedField ⟨_, Subgroup.isClosed_of_isOpen _
          (isOpen_charKer_openChar U z)⟩]
        exact isOpen_charKer_openChar U z)
    have hbz : b ∈ DiscreteValuationField.fieldNormSubgroup (fixedField (U : Subgroup Gal(Ksep/K))) Fz := by
      let := (IntermediateField.inclusion hFz).toRingHom.toAlgebra
      have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K))) Fz F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact DiscreteValuationField.fieldNormSubgroup_le_of_tower (fixedField (U : Subgroup Gal(Ksep/K))) F Fz hb
    obtain ⟨y, hy⟩ := (exists_norm_iff_mem_fieldNormSubgroup Fz b).2 hbz
    have h0 := (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z b).2 ⟨y, hy⟩
    have h1 : β (cohomologyπ _ 1 z) (κ (Additive.ofMul b)) = 0 := h0
    rw [h1, map_zero]
  refine ⟨F, hfin, habel, ?_⟩
  -- `[F : (fixedField (U : Subgroup Gal(Ksep/K)))] ≤ |A|`
  have hfinrank : Module.finrank (fixedField (U : Subgroup Gal(Ksep/K))) F ≤ Nat.card A := by
    rw [← IsGalois.card_aut_eq_finrank]
    have hker : (AlgEquiv.restrictNormalHom F).ker = N := by rw [F.restrictNormalHom_ker, hfix]
    have e1 : Gal(Ksep/(fixedField (U : Subgroup Gal(Ksep/K)))) ⧸ N ≃*
        Gal(F/(fixedField (U : Subgroup Gal(Ksep/K)))) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective Ksep))
    rw [← Nat.card_congr e1.toEquiv]
    exact card_quotient_le_of_pairing A (classChar U) (fun x y σ => classChar_add U x y σ)
      (fun x σ τ => classChar_mul U x σ τ) N hmemN
  have hAS : Nat.card A * Nat.card S = Nat.card Y := card_annihilator_left hY hP S
  have hYS := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S
  have hquot : Nat.card (Y ⧸ S) = H.index := card_quotient_map_kummerHom hn U hH
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hAcard : Nat.card A = H.index := by
    rw [hYS, hquot] at hAS
    exact Nat.eq_of_mul_eq_mul_right hSpos hAS
  -- conclusion
  have hHpos : 0 < H.index := by rw [← hAcard]; exact Nat.card_pos
  exact fieldNormSubgroup_eq_of_le_of_finrank_le U F H hle hHpos (hAcard ▸ hfinrank)

end ExistenceOpen

section Existence

open LocalFieldTheory

variable (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- **Existence theorem** for norm groups containing `n`-th powers: for `n` invertible in `K`, every
subgroup `H ⊆ Kˣ` containing `Kˣⁿ` is the norm group `N(Eˣ)` of a finite abelian extension `E` of
`K` inside `Ksep`. -/
theorem exists_isAbelianGalois_fieldNormSubgroup_eq {n : ℕ} (hn : (n : K) ≠ 0) (H : Subgroup Kˣ)
    (hH : (powMonoidHom n : Kˣ →* Kˣ).range ≤ H) :
    ∃ E : IntermediateField K Ksep, FiniteDimensional K E ∧ IsAbelianGalois K E ∧
      DiscreteValuationField.fieldNormSubgroup K E = H := by
  -- the fixed field of `⊤` is `K`
  have hfr : Module.finrank K (fixedField ((⊤ : OpenSubgroup Gal(Ksep/K)) :
      Subgroup Gal(Ksep/K))) = 1 := by
    rw [← index_openSubgroup ⊤]
    exact Subgroup.index_top
  have hbot := IntermediateField.finrank_eq_one_iff.1 hfr
  have hsurj : Function.Surjective (algebraMap K
      (fixedField ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)))) := by
    intro x
    have hx : (x : Ksep) ∈ (⊥ : IntermediateField K Ksep) := by
      rw [← hbot]
      exact x.2
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hx
    exact ⟨a, Subtype.ext ha⟩
  set E₀ := fixedField ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))
  let e : K ≃ₐ[K] E₀ :=
    AlgEquiv.ofBijective (Algebra.ofId K E₀) ⟨(algebraMap K E₀).injective, hsurj⟩
  have he : ∀ a : K, (e a : E₀) = algebraMap K E₀ a := fun a => rfl
  let ι : Kˣ ≃* E₀ˣ := Units.mapEquiv e.toMulEquiv
  have hι : ∀ a : Kˣ, ((ι a : E₀ˣ) : E₀) = algebraMap K E₀ a := fun a => rfl
  let H₀ : Subgroup E₀ˣ := H.map ι.toMonoidHom
  have hH₀ : (powMonoidHom n : E₀ˣ →* E₀ˣ).range ≤ H₀ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := ι.surjective c
    exact ⟨a ^ n, hH (x := a ^ n) ⟨a, rfl⟩, by simp⟩
  obtain ⟨F₀, hfin₀, habel₀, hnorm₀⟩ :=
    exists_fieldNormSubgroup_eq_of_range_pow_le hn ⊤ H₀ hH₀
  have hfinK : FiniteDimensional K F₀ := Module.Finite.trans E₀ F₀
  have hfinK' : FiniteDimensional K (F₀.restrictScalars K) := hfinK
  refine ⟨F₀.restrictScalars K, hfinK', ?_, ?_⟩
  · -- Galois and abelian: the automorphisms over `K` and over `E₀ = K` are the same
    have hcomm : ∀ σ : F₀ ≃ₐ[K] F₀, ∀ x : E₀, σ (algebraMap E₀ F₀ x) = algebraMap E₀ F₀ x := by
      intro σ x
      obtain ⟨a, rfl⟩ := hsurj x
      rw [← IsScalarTower.algebraMap_apply, σ.commutes]
    let res : Gal(F₀/E₀) ≃* (F₀ ≃ₐ[K] F₀) :=
      MulEquiv.ofBijective (AlgEquiv.restrictScalarsHom K)
        ⟨AlgEquiv.restrictScalars_injective K, fun σ =>
          ⟨{ σ with commutes' := hcomm σ }, AlgEquiv.ext fun _ => rfl⟩⟩
    have hcard : Nat.card (F₀ ≃ₐ[K] F₀) = Module.finrank K F₀ := by
      rw [← Nat.card_congr res.toEquiv, IsGalois.card_aut_eq_finrank,
        ← Module.finrank_mul_finrank K E₀ F₀, hfr, one_mul]
    have hgal : IsGalois K F₀ := IsGalois.of_card_aut_eq_finrank (F := K) (E := F₀) hcard
    have hab : IsMulCommutative (F₀ ≃ₐ[K] F₀) := ⟨⟨fun σ τ => by
      obtain ⟨σ', rfl⟩ := res.surjective σ
      obtain ⟨τ', rfl⟩ := res.surjective τ
      rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm σ' τ']⟩⟩
    have : IsAbelianGalois K F₀ := { toIsGalois := hgal, toIsMulCommutative := hab }
    exact this
  · -- norm groups
    have hnormK : ∀ y : F₀, Algebra.norm K y = e.symm (Algebra.norm E₀ y) := by
      intro y
      rw [← Algebra.norm_norm (R := K) (S := E₀)]
      obtain ⟨b, hb⟩ := hsurj (Algebra.norm E₀ y)
      rw [← hb, Algebra.norm_algebraMap, hfr, pow_one]
      exact (e.symm_apply_apply b).symm
    have key : ∀ a : Kˣ, a ∈ DiscreteValuationField.fieldNormSubgroup K F₀ ↔ a ∈ H := by
      intro a
      constructor
      · rintro ⟨y, hy⟩
        have hy' : Algebra.norm K (y : F₀) = (a : K) := congrArg Units.val hy
        rw [hnormK] at hy'
        have hmem : ι a ∈ H₀ := by
          rw [← hnorm₀, ← exists_norm_iff_mem_fieldNormSubgroup F₀ (ι a)]
          refine ⟨y, ?_⟩
          rw [hι, ← hy', ← he, e.apply_symm_apply]
        obtain ⟨a', ha', haa⟩ := hmem
        rwa [show a' = a from ι.injective haa] at ha'
      · intro ha
        have hmem : ι a ∈ H₀ := ⟨a, ha, rfl⟩
        rw [← hnorm₀, ← exists_norm_iff_mem_fieldNormSubgroup F₀ (ι a)] at hmem
        obtain ⟨y, hy⟩ := hmem
        have hy0 : y ≠ 0 := by
          rintro rfl
          rw [Algebra.norm_zero] at hy
          exact (ι a).ne_zero hy.symm
        refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
        change Algebra.norm K y = (a : K)
        rw [hnormK, hy, hι, ← he, e.symm_apply_apply]
    ext a
    exact key a

end Existence

end Langlands.GaloisCohomology.Local
