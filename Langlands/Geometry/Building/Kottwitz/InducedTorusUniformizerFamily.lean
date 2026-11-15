import Langlands.Geometry.Building.Kottwitz.CompositumUniformizer
import Langlands.Geometry.Building.Kottwitz.PermutationCoinvariants
import Langlands.Geometry.Building.Kottwitz.InertiaCoinvariants
import Langlands.Geometry.Building.Kottwitz.InducedTorusNormValue
import Mathlib.FieldTheory.PrimitiveElement

/-! # Equivariant uniformizer families for permutation index sets -/

noncomputable section

universe u

set_option linter.unusedSectionVars false

open scoped IntermediateField

namespace Langlands.Geometry.Building.Kottwitz

namespace UniformizerFamily

open PermutationCoinvariants

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  {J : Type u} [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J]
  (act : (E ≃ₐ[F] E) →* Equiv.Perm J)
  (hact : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
    σ • j = act (σ.restrictNormal E) j)

local notation "Ω" => SeparableClosure F

/-! ### Fixed fields of stabilizers -/

/-- The stabilizer of an index in `Gal(E/F)`. -/
def stab (p : J) : Subgroup (E ≃ₐ[F] E) :=
  (MulAction.stabilizer (Equiv.Perm J) p).comap act

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem mem_stab {σ : E ≃ₐ[F] E} {p : J} : σ ∈ stab F E act p ↔ act σ p = p :=
  Iff.rfl

/-- The fixed field of the stabilizer of `p`, inside `F^sep`. -/
def fixedOmega (p : J) : IntermediateField F (SeparableClosure F) :=
  (IntermediateField.fixedField (stab F E act p)).map E.val

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem fixedOmega_le (p : J) : fixedOmega F E act p ≤ E := by
  rintro y ⟨z, -, rfl⟩
  exact z.2

include hact in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
/-- An automorphism of `F^sep` fixes the fixed field of the stabilizer of `p` iff it fixes `p`. -/
theorem forall_fixedOmega_iff (σ : Ω ≃ₐ[F] Ω) (p : J) :
    (∀ y ∈ fixedOmega F E act p, σ y = y) ↔ σ • p = p := by
  rw [hact, ← mem_stab F E act,
    ← IntermediateField.fixingSubgroup_fixedField (stab F E act p),
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z hz
    apply Subtype.ext
    rw [← h (z : Ω) ⟨z, hz, rfl⟩]
    exact AlgEquiv.restrictNormal_commutes σ E z
  · rintro h y ⟨z, hz, rfl⟩
    have h' := AlgEquiv.restrictNormal_commutes σ E z
    rw [h z hz] at h'
    exact h'.symm

include hact in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
/-- Two automorphisms agree on the fixed field of the stabilizer of `p` iff they move `p`
to the same index. -/
theorem forall_eq_iff (σ σ' : Ω ≃ₐ[F] Ω) (p : J) :
    (∀ y ∈ fixedOmega F E act p, σ y = σ' y) ↔ σ • p = σ' • p := by
  have h := forall_fixedOmega_iff F E act hact (σ'⁻¹ * σ) p
  rw [mul_smul, inv_smul_eq_iff] at h
  rw [← h]
  refine forall₂_congr fun y _ => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]

/-! ### Primitive elements of the fixed fields -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem finiteDimensional_fixedOmega (p : J) : FiniteDimensional F (fixedOmega F E act p) :=
  LinearEquiv.finiteDimensional
    ((IntermediateField.fixedField (stab F E act p)).equivMap E.val).toLinearEquiv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem exists_adjoin_eq (p : J) :
    ∃ α : Ω, IntermediateField.adjoin F {α} = fixedOmega F E act p := by
  have := finiteDimensional_fixedOmega F E act p
  have : Algebra.IsSeparable F (fixedOmega F E act p) :=
    Algebra.isSeparable_tower_bot_of_isSeparable F (fixedOmega F E act p) Ω
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F (fixedOmega F E act p)
  refine ⟨a, ?_⟩
  have h := congrArg (fun N : IntermediateField F (fixedOmega F E act p) =>
    N.map (fixedOmega F E act p).val) ha
  change IntermediateField.adjoin F {(fixedOmega F E act p).val a} = _
  simpa only [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val] using h

/-- A primitive element of the fixed field of the stabilizer of `p`. -/
def prim (p : J) : Ω := (exists_adjoin_eq F E act p).choose

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem adjoin_prim (p : J) :
    IntermediateField.adjoin F {prim F E act p} = fixedOmega F E act p :=
  (exists_adjoin_eq F E act p).choose_spec

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem prim_mem (p : J) : prim F E act p ∈ fixedOmega F E act p := by
  rw [← adjoin_prim F E act p]
  exact IntermediateField.mem_adjoin_simple_self F _

/-! ### Inertia and automorphisms over the maximal unramified extension -/

theorem restrictScalars_mem_inertia (τ : Ω ≃ₐ[UnramifiedClosure F] Ω) :
    τ.restrictScalars F ∈ relativeInertia F (UnramifiedClosure F) Ω := by
  rw [relativeInertia, MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro a
  apply (algebraMap (UnramifiedClosure F) Ω).injective
  change algebraMap (UnramifiedClosure F) Ω
      ((τ.restrictScalars F).restrictNormal (UnramifiedClosure F) a) =
    algebraMap (UnramifiedClosure F) Ω a
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

/-- An inertia element, regarded as an automorphism over `K`. -/
def inertiaToK (h : Ω ≃ₐ[F] Ω) (hh : h ∈ relativeInertia F (UnramifiedClosure F) Ω) :
    Ω ≃ₐ[UnramifiedClosure F] Ω :=
  AlgEquiv.ofRingEquiv (f := h.toRingEquiv) (fun a => by
    have h1 := AlgEquiv.restrictNormal_commutes h (UnramifiedClosure F) a
    have h2 : h.restrictNormal (UnramifiedClosure F) = 1 := hh
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm)

theorem inertiaToK_restrictScalars (h : Ω ≃ₐ[F] Ω)
    (hh : h ∈ relativeInertia F (UnramifiedClosure F) Ω) :
    (inertiaToK F h hh).restrictScalars F = h :=
  AlgEquiv.ext fun _ => rfl

/-! ### Counting inertia orbits -/

open scoped Classical in
include hact in
/-- The inertia orbit of `p` has as many elements as the degree of `K(α_p)/K`. -/
theorem card_orbit_eq_finrank (p : J) :
    (Finset.univ.filter (fun i => orbitClass (relativeInertia F (UnramifiedClosure F) Ω) i =
        orbitClass (relativeInertia F (UnramifiedClosure F) Ω) p)).card =
      Module.finrank (UnramifiedClosure F)
        (IntermediateField.adjoin (UnramifiedClosure F) {prim F E act p}) := by
  have : IsGalois (UnramifiedClosure F) Ω :=
    IsGalois.tower_top_of_isGalois F (UnramifiedClosure F) Ω
  set α := prim F E act p with hαdef
  have hint : IsIntegral (UnramifiedClosure F) α := Algebra.IsIntegral.isIntegral α
  rw [IntermediateField.adjoin.finrank hint,
    ← Polynomial.card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable _ α)
      (Normal.splits inferInstance α)]
  have hroot : ∀ β : (minpoly (UnramifiedClosure F) α).rootSet Ω,
      ∃ τ : Ω ≃ₐ[UnramifiedClosure F] Ω, τ α = β := fun β =>
    minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _)
      (Polynomial.mem_rootSet'.mp β.2).2
  have hmove : ∀ τ τ' : Ω ≃ₐ[UnramifiedClosure F] Ω,
      τ α = τ' α ↔ τ.restrictScalars F • p = τ'.restrictScalars F • p := by
    intro τ τ'
    rw [← forall_eq_iff F E act hact]
    constructor
    · intro h y hy
      have hext := IntermediateField.algHom_ext_of_eq_adjoin F (adjoin_prim F E act p).symm
        (φ₁ := (τ.restrictScalars F).toAlgHom.comp (fixedOmega F E act p).val)
        (φ₂ := (τ'.restrictScalars F).toAlgHom.comp (fixedOmega F E act p).val)
        (by
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact h)
      exact DFunLike.congr_fun hext ⟨y, hy⟩
    · intro h
      exact h α (prim_mem F E act p)
  let f : (minpoly (UnramifiedClosure F) α).rootSet Ω → J :=
    fun β => (hroot β).choose.restrictScalars F • p
  have hfinj : Function.Injective f := by
    intro β β' hβ
    apply Subtype.ext
    rw [← (hroot β).choose_spec, ← (hroot β').choose_spec]
    exact (hmove _ _).mpr hβ
  have himage : Finset.univ.filter (fun i =>
      orbitClass (relativeInertia F (UnramifiedClosure F) Ω) i =
        orbitClass (relativeInertia F (UnramifiedClosure F) Ω) p) = Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [orbitClass_eq_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      let τ := inertiaToK F h hh
      have hτroot : τ α ∈ (minpoly (UnramifiedClosure F) α).rootSet Ω := by
        rw [Polynomial.mem_rootSet']
        refine ⟨Polynomial.map_ne_zero (minpoly.ne_zero hint), ?_⟩
        have h3 : Polynomial.aeval (τ α) (minpoly (UnramifiedClosure F) α) =
            τ (Polynomial.aeval α (minpoly (UnramifiedClosure F) α)) :=
          Polynomial.aeval_algHom_apply τ.toAlgHom α _
        rw [h3, minpoly.aeval, map_zero]
      refine ⟨⟨τ α, hτroot⟩, ?_⟩
      have h4 := (hmove (hroot ⟨τ α, hτroot⟩).choose τ).mp (hroot ⟨τ α, hτroot⟩).choose_spec
      rw [inertiaToK_restrictScalars] at h4
      exact h4
    · rintro ⟨β, -, rfl⟩
      exact ⟨_, restrictScalars_mem_inertia F _, rfl⟩
  rw [himage, Finset.card_image_of_injective _ hfinj]
  exact Finset.card_univ

include hact in
/-- The orbit sum of the constant function one is the degree of `K(α_p)/K`. -/
theorem orbitFunSum_one_eq_finrank (p : J) :
    orbitFunSum (relativeInertia F (UnramifiedClosure F) Ω) (fun _ => (1 : ℤ)) p =
      Module.finrank (UnramifiedClosure F)
        (IntermediateField.adjoin (UnramifiedClosure F) {prim F E act p}) := by
  classical
  unfold orbitFunSum
  rw [Finset.sum_boole, card_orbit_eq_finrank F E act hact p]

/-! ### Uniformizers of the composita -/

/-- The compositum `K(α_p)` of `K` with the fixed field of the stabilizer of `p`. -/
def compositum (p : J) : IntermediateField (UnramifiedClosure F) Ω :=
  IntermediateField.adjoin (UnramifiedClosure F) {prim F E act p}

instance compositum_finiteDimensional (p : J) :
    FiniteDimensional (UnramifiedClosure F) (compositum F E act p) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

omit [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem compositum_restrictScalars (p : J) :
    (compositum F E act p).restrictScalars F =
      LocalGalois.Separable.inertiaFixedField F ⊔ fixedOmega F E act p := by
  change (IntermediateField.adjoin (LocalGalois.Separable.inertiaFixedField F)
    {prim F E act p}).restrictScalars F = _
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, adjoin_prim]

omit [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem fixedOmega_le_compositum (p : J) :
    ∀ x ∈ fixedOmega F E act p, x ∈ compositum F E act p := by
  intro x hx
  have h : x ∈ (compositum F E act p).restrictScalars F := by
    rw [compositum_restrictScalars]
    exact (le_sup_right : fixedOmega F E act p ≤ _) hx
  exact h

omit [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem compositum_le_sup (p : J) :
    ∀ x ∈ compositum F E act p,
      x ∈ LocalGalois.Separable.inertiaFixedField F ⊔ fixedOmega F E act p := by
  intro x hx
  have h : x ∈ (compositum F E act p).restrictScalars F := hx
  rwa [compositum_restrictScalars] at h

omit [IsGalois F E] [Fintype J] [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J] in
theorem exists_unif (p : J) : ∃ a : fixedOmega F E act p,
    normalizedIntermediateValuation F (compositum F E act p)
      ⟨a, fixedOmega_le_compositum F E act p a a.2⟩ = WithZero.exp (-1) :=
  CompositumUniformizer.exists_uniformizer_of_le_sup F (fixedOmega F E act p)
    (compositum F E act p) (compositum_le_sup F E act p) (fixedOmega_le_compositum F E act p)

/-- A uniformizer of `K(α_p)` lying in the fixed field of the stabilizer of `p`. -/
def unif (p : J) : Ω := ((exists_unif F E act p).choose : Ω)

theorem unif_mem (p : J) : unif F E act p ∈ fixedOmega F E act p :=
  (exists_unif F E act p).choose.2

theorem unif_val (p : J) :
    normalizedIntermediateValuation F (compositum F E act p)
      ⟨unif F E act p, fixedOmega_le_compositum F E act p _ (unif_mem F E act p)⟩ =
        WithZero.exp (-1) :=
  (exists_unif F E act p).choose_spec

theorem unif_ne_zero (p : J) : unif F E act p ≠ 0 := by
  intro h
  have hv := unif_val F E act p
  have h0 : (⟨unif F E act p, fixedOmega_le_compositum F E act p _ (unif_mem F E act p)⟩ :
      compositum F E act p) = 0 := Subtype.ext h
  rw [h0, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-! ### Valuations in a larger field -/

/-- The normalized valuation of an element of a subfield, in a finite extension. -/
theorem normalizedIntermediateValuation_of_le
    (M L : IntermediateField (UnramifiedClosure F) Ω)
    [FiniteDimensional (UnramifiedClosure F) M] [FiniteDimensional (UnramifiedClosure F) L]
    (hML : M ≤ L) (w : Ω) (hwM : w ∈ M) (n : ℤ)
    (hw : normalizedIntermediateValuation F M ⟨w, hwM⟩ = WithZero.exp n) :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := Algebra.toModule
    normalizedIntermediateValuation F L ⟨w, hML hwM⟩ =
      WithZero.exp (Module.finrank M L • n) := by
  let : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  let : Module M L := Algebra.toModule
  rw [← normalizedIntermediateValuation_norm F M L hML]
  have hn : Algebra.norm M (⟨w, hML hwM⟩ : L) = ⟨w, hwM⟩ ^ Module.finrank M L :=
    Algebra.norm_algebraMap (⟨w, hwM⟩ : M)
  rw [hn, map_pow, hw, WithZero.exp_nsmul]

/-- Units of `L` with the same spectral value have the same integer order. -/
theorem orderUnits_eq_of_val (L : IntermediateField (UnramifiedClosure F) Ω)
    [FiniteDimensional (UnramifiedClosure F) L] (z z' : Lˣ)
    (h : LocalGalois.Separable.sepClosureValuation F ((z : L) : Ω) =
      LocalGalois.Separable.sepClosureValuation F ((z' : L) : Ω)) :
    IntegerValuation.orderUnits (normalizedIntermediateValuation F L) z =
      IntegerValuation.orderUnits (normalizedIntermediateValuation F L) z' := by
  apply Multiplicative.toAdd.injective
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd]
  have hv : normalizedIntermediateValuation F L (z : L) =
      normalizedIntermediateValuation F L (z' : L) :=
    ((normalizedIntermediateValuation_spec' F L).1.eq_iff).mpr h
  rw [hv]

/-! ### Representatives of Galois orbits -/

/-- A representative of the Galois orbit of `j`. -/
def rep (j : J) : J :=
  Quotient.out (Quotient.mk'' j : MulAction.orbitRel.Quotient (Ω ≃ₐ[F] Ω) J)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
theorem exists_smul_rep (j : J) : ∃ g : Ω ≃ₐ[F] Ω, g • rep F j = j := by
  have h : (Quotient.mk'' (rep F j) : MulAction.orbitRel.Quotient (Ω ≃ₐ[F] Ω) J) =
      Quotient.mk'' j :=
    Quotient.out_eq' _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
theorem rep_smul (σ : Ω ≃ₐ[F] Ω) (j : J) : rep F (σ • j) = rep F j := by
  unfold rep
  congr 1
  apply Quotient.sound'
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit j σ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
theorem rep_rep (j : J) : rep F (rep F j) = rep F j := by
  obtain ⟨g, hg⟩ := exists_smul_rep F j
  have h := rep_smul F g (rep F j)
  rw [hg] at h
  exact h.symm

/-- An automorphism moving the representative of the orbit of `j` to `j`. -/
def mover (j : J) : Ω ≃ₐ[F] Ω := (exists_smul_rep F j).choose

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype J] in
theorem mover_smul (j : J) : mover F j • rep F j = j := (exists_smul_rep F j).choose_spec

/-! ### The equivariant uniformizer family -/

/-- The family of uniformizers, transported from the orbit representatives. -/
def fam (j : J) : Ω := mover F j (unif F E act (rep F j))

include hact in
theorem fam_smul (σ : Ω ≃ₐ[F] Ω) (j : J) : fam F E act (σ • j) = σ (fam F E act j) := by
  unfold fam
  have hrep := rep_smul F σ j
  have h1 : mover F (σ • j) • rep F j = (σ * mover F j) • rep F j := by
    rw [mul_smul, mover_smul, ← hrep, mover_smul]
  rw [hrep]
  exact (forall_eq_iff F E act hact _ _ (rep F j)).mpr h1 _ (unif_mem F E act (rep F j))

omit [FiniteDimensional F E] in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem smul_mem (σ : Ω ≃ₐ[F] Ω) {x : Ω} (hx : x ∈ E) : σ x ∈ E := by
  have h : σ x = ((σ.restrictNormal E ⟨x, hx⟩ : E) : Ω) :=
    (AlgEquiv.restrictNormal_commutes σ E ⟨x, hx⟩).symm
  rw [h]
  exact Subtype.mem _

theorem fam_mem (j : J) : fam F E act j ∈ E :=
  smul_mem F E _ (fixedOmega_le F E act _ (unif_mem F E act (rep F j)))

theorem fam_ne_zero (j : J) : fam F E act j ≠ 0 :=
  (map_ne_zero (mover F j)).mpr (unif_ne_zero F E act (rep F j))

/-- The family as units of `E`. -/
def famUnits (j : J) : Eˣ :=
  Units.mk0 ⟨fam F E act j, fam_mem F E act j⟩
    (fun h => fam_ne_zero F E act j (congrArg Subtype.val h))

theorem coe_famUnits (j : J) : ((famUnits F E act j : E) : Ω) = fam F E act j := rfl

include hact in
/-- The family is `Gal(E/F)`-equivariant. -/
theorem famUnits_act (τ : E ≃ₐ[F] E) (j : J) :
    famUnits F E act (act τ j) = Units.map τ.toMonoidHom (famUnits F E act j) := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) τ
  have hj : act (AlgEquiv.restrictNormalHom E σ) j = σ • j := (hact σ j).symm
  apply Units.ext
  apply Subtype.ext
  rw [hj]
  change fam F E act (σ • j) = ((σ.restrictNormal E (famUnits F E act j) : E) : Ω)
  rw [fam_smul F E act hact]
  exact (AlgEquiv.restrictNormal_commutes σ E (famUnits F E act j : E)).symm

/-! ### Orbit sums of the orders of the family -/

variable (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] (hEL : ∀ x ∈ E, x ∈ L)

/-- The integer order in `L` of the family. -/
def famOrder (j : J) : ℤ :=
  (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
    (Units.map (InducedCocharacterBasis.inclusionHom F E L hEL) (famUnits F E act j))).toAdd

include hact in
theorem famOrder_smul (σ : Ω ≃ₐ[F] Ω) (j : J) :
    famOrder F E act L hEL (σ • j) = famOrder F E act L hEL j := by
  unfold famOrder
  congr 1
  apply orderUnits_eq_of_val
  change LocalGalois.Separable.sepClosureValuation F (fam F E act (σ • j)) =
    LocalGalois.Separable.sepClosureValuation F (fam F E act j)
  rw [fam_smul F E act hact]
  exact CompositumUniformizer.sepClosureValuation_map F σ _

set_option synthInstance.maxHeartbeats 200000 in
include hact in
/-- The orbit sums of the orders of the family all equal `[L : K]`. -/
theorem orbitFunSum_famOrder (j : J) :
    orbitFunSum (relativeInertia F (UnramifiedClosure F) Ω) (famOrder F E act L hEL) j =
      Module.finrank (UnramifiedClosure F) L := by
  set H := relativeInertia F (UnramifiedClosure F) Ω with hH
  set f := famOrder F E act L hEL with hfdef
  have hinv : ∀ (σ : Ω ≃ₐ[F] Ω) i, f (σ • i) = f i := famOrder_smul F E act hact L hEL
  have hconst : ∀ i, orbitFunSum H f i = f i * orbitFunSum H (fun _ => (1 : ℤ)) i := by
    intro i
    have h := orbitFunSum_mul_const H f (fun _ => (1 : ℤ)) i (fun i' hi' => by
      obtain ⟨h, -, rfl⟩ := (orbitClass_eq_iff H).mp hi'
      exact hinv h i)
    simpa only [mul_one] using h
  have hS : orbitFunSum H f j = orbitFunSum H f (rep F j) := by
    have h1 := orbitFunSum_comp_smul H f (mover F j) j
    have h2 : (fun i => f ((mover F j)⁻¹ • i)) = f := funext fun i => hinv _ i
    rw [h2] at h1
    rw [h1]
    congr 1
    rw [inv_smul_eq_iff]
    exact (mover_smul F j).symm
  rw [hS, hconst, orbitFunSum_one_eq_finrank F E act hact]
  set p := rep F j with hp
  have hfam : fam F E act p = unif F E act p := by
    unfold fam
    have hfix := (forall_fixedOmega_iff F E act hact (mover F p) (rep F p)).mpr
      (by rw [mover_smul, hp, rep_rep])
    rw [hp, rep_rep] at hfix ⊢
    exact hfix _ (unif_mem F E act _)
  have hML : compositum F E act p ≤ L :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (hEL _ (fixedOmega_le F E act p (prim_mem F E act p)))
  let alg : Algebra (compositum F E act p) L := (IntermediateField.inclusion hML).toAlgebra
  let : SMul (compositum F E act p) L := alg.toSMul
  let : Module (compositum F E act p) L := Algebra.toModule
  have : IsScalarTower (UnramifiedClosure F) (compositum F E act p) L :=
    IsScalarTower.of_algebraMap_eq (R := UnramifiedClosure F) (S := compositum F E act p)
      (A := L) (fun _ => rfl)
  have hval : normalizedIntermediateValuation F L
      ⟨unif F E act p, hML (fixedOmega_le_compositum F E act p _ (unif_mem F E act p))⟩ =
        WithZero.exp (Module.finrank (compositum F E act p) L • (-1 : ℤ)) :=
    normalizedIntermediateValuation_of_le F (compositum F E act p) L hML (unif F E act p)
      (fixedOmega_le_compositum F E act p _ (unif_mem F E act p)) (-1) (unif_val F E act p)
  have hf : f p = (Module.finrank (compositum F E act p) L : ℤ) := by
    rw [hfdef, famOrder, IntegerValuation.orderUnits_toAdd]
    have hpt : ((Units.map (InducedCocharacterBasis.inclusionHom F E L hEL)
        (famUnits F E act p) : Lˣ) : L) =
        ⟨unif F E act p, hML (fixedOmega_le_compositum F E act p _ (unif_mem F E act p))⟩ :=
      Subtype.ext hfam
    rw [hpt, hval, WithZero.log_exp]
    simp
  have : Module.Free (compositum F E act p) L := Module.Free.of_divisionRing _ _
  have htower := Module.finrank_mul_finrank (UnramifiedClosure F) (compositum F E act p) L
  rw [hf, ← htower]
  push_cast
  exact mul_comm _ _

include hact in
/-- A uniformizer family: a `Gal(E/F)`-equivariant family of units of `E` whose `L`-orders
have orbit sums `[L : K]` on every inertia orbit. -/
theorem exists_family :
    ∃ u : J → Eˣ, (∀ (τ : E ≃ₐ[F] E) (j : J), u (act τ j) = Units.map τ.toMonoidHom (u j)) ∧
      ∀ j, orbitFunSum (relativeInertia F (UnramifiedClosure F) Ω)
        (fun i => (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
          (Units.map (InducedCocharacterBasis.inclusionHom F E L hEL) (u i))).toAdd) j =
        Module.finrank (UnramifiedClosure F) L :=
  ⟨famUnits F E act, famUnits_act F E act hact, orbitFunSum_famOrder F E act hact L hEL⟩

end UniformizerFamily

end Langlands.Geometry.Building.Kottwitz
