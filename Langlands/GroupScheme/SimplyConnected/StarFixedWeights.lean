import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.Galois.Basic

/-! # Star-fixed weights and coset sums of star translates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-! ### Coset sums for a group acting by linear automorphisms -/

section CosetSum

variable {Γ : Type*} [Group Γ] {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (ρ : Γ →* (M ≃ₗ[R] M)) (H : Subgroup Γ)

/-- The sum of the translates `ρ g m` over the left cosets `g H`, using the chosen
representative `q.out` of each coset `q`. Different cosets giving the same translate
contribute separately. -/
def equivCosetSum (m : M) : M :=
  ∑ᶠ q : Γ ⧸ H, ρ q.out m

theorem equivCosetSum_def (m : M) : equivCosetSum ρ H m = ∑ᶠ q : Γ ⧸ H, ρ q.out m :=
  rfl

/-- The stabilizer of an element for the action `ρ`. -/
def equivStabilizer (m : M) : Subgroup Γ where
  carrier := {g | ρ g m = m}
  one_mem' := by
    change ρ 1 m = m
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change ρ g m = m at hg
    change ρ h m = m at hh
    change ρ (g * h) m = m
    rw [map_mul, LinearEquiv.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g m = m at hg
    change ρ g⁻¹ m = m
    conv_lhs => rw [← hg]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

@[simp] theorem mem_equivStabilizer (m : M) (g : Γ) :
    g ∈ equivStabilizer ρ m ↔ ρ g m = m :=
  Iff.rfl

variable {ρ H}

/-- For an `H`-fixed element, the translate only depends on the left coset. -/
theorem apply_eq_of_coset_eq {m : M} (hm : ∀ h ∈ H, ρ h m = m) {g g' : Γ}
    (hgg' : (g : Γ ⧸ H) = g') : ρ g m = ρ g' m := by
  have h : g⁻¹ * g' ∈ H := QuotientGroup.eq.mp hgg'
  have hg' : g' = g * (g⁻¹ * g') := by group
  rw [hg', map_mul, LinearEquiv.mul_apply, hm _ h]

/-- Independence of representatives: any choice of one representative in each coset gives
the coset sum. -/
theorem finsum_section_eq_equivCosetSum {m : M} (hm : ∀ h ∈ H, ρ h m = m)
    (s : Γ ⧸ H → Γ) (hs : ∀ q, (s q : Γ ⧸ H) = q) :
    ∑ᶠ q, ρ (s q) m = equivCosetSum ρ H m := by
  refine finsum_congr fun q => ?_
  exact apply_eq_of_coset_eq hm ((hs q).trans (QuotientGroup.out_eq' q).symm)

/-- Independence of representatives, for a left transversal `S` of `H`. -/
theorem finsum_transversal_eq_equivCosetSum {m : M} (hm : ∀ h ∈ H, ρ h m = m)
    {S : Set Γ} (hS : Subgroup.IsComplement S (H : Set Γ)) :
    ∑ᶠ s : S, ρ s m = equivCosetSum ρ H m := by
  rw [← finsum_comp_equiv hS.leftQuotientEquiv]
  exact finsum_section_eq_equivCosetSum hm (fun q => (hS.leftQuotientEquiv q : Γ))
    (Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hS)

/-- Independence of representatives, for a finite set of representatives. -/
theorem sum_transversal_eq_equivCosetSum {m : M} (hm : ∀ h ∈ H, ρ h m = m)
    (S : Finset Γ) (hS : Subgroup.IsComplement (S : Set Γ) (H : Set Γ)) :
    ∑ s ∈ S, ρ s m = equivCosetSum ρ H m := by
  rw [← finsum_transversal_eq_equivCosetSum hm hS]
  exact (finsum_mem_coe_finset (fun g => ρ g m) S).symm.trans
    (finsum_set_coe_eq_finsum_mem (f := fun g => ρ g m) (S : Set Γ)).symm

/-- The coset sum as a finite sum. -/
theorem equivCosetSum_eq_sum [Fintype (Γ ⧸ H)] (m : M) :
    equivCosetSum ρ H m = ∑ q : Γ ⧸ H, ρ q.out m :=
  finsum_eq_sum_of_fintype _

variable (ρ H) in
theorem equivCosetSum_add [Finite (Γ ⧸ H)] (m m' : M) :
    equivCosetSum ρ H (m + m') = equivCosetSum ρ H m + equivCosetSum ρ H m' := by
  simp only [equivCosetSum_def, map_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

variable (ρ H) in
theorem equivCosetSum_zero : equivCosetSum ρ H (0 : M) = 0 := by
  simp [equivCosetSum_def]

/-- Invariance of the coset sum under the whole group. -/
theorem apply_equivCosetSum [Finite (Γ ⧸ H)] {m : M} (hm : ∀ h ∈ H, ρ h m = m) (g : Γ) :
    ρ g (equivCosetSum ρ H m) = equivCosetSum ρ H m := by
  rw [equivCosetSum_def, map_finsum _ (Set.toFinite _)]
  simp only [← LinearEquiv.mul_apply, ← map_mul]
  rw [← finsum_comp_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (Γ ⧸ H))]
  refine finsum_section_eq_equivCosetSum hm _ fun q => ?_
  change ((g * (g⁻¹ • q).out : Γ) : Γ ⧸ H) = q
  calc ((g * (g⁻¹ • q).out : Γ) : Γ ⧸ H) = g • (((g⁻¹ • q).out : Γ) : Γ ⧸ H) := rfl
    _ = q := by rw [QuotientGroup.out_eq', smul_inv_smul]

/-- The coset sum over the full stabilizer is the sum over the orbit, each element once. -/
theorem equivCosetSum_equivStabilizer (m : M) :
    equivCosetSum ρ (equivStabilizer ρ m) m =
      ∑ᶠ μ ∈ Set.range (fun g : Γ => ρ g m), μ := by
  have hm : ∀ h ∈ equivStabilizer ρ m, ρ h m = m := fun h hh => hh
  have hinj : Function.Injective (fun q : Γ ⧸ equivStabilizer ρ m => ρ q.out m) := by
    intro q q' hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    change ρ (q.out⁻¹ * q'.out) m = m
    have hqq'' : ρ q.out m = ρ q'.out m := hqq'
    rw [map_mul, LinearEquiv.mul_apply, ← hqq'', ← LinearEquiv.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  have hrange : Set.range (fun g : Γ => ρ g m) =
      Set.range (fun q : Γ ⧸ equivStabilizer ρ m => ρ q.out m) := by
    ext μ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g : Γ ⧸ equivStabilizer ρ m),
        apply_eq_of_coset_eq hm (QuotientGroup.out_eq' (g : Γ ⧸ equivStabilizer ρ m))⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.out, rfl⟩
  rw [hrange, finsum_mem_range hinj, equivCosetSum_def]

/-- Multiplicities: each translate of `m` occurs `[Stab(m) : H]` times in the coset sum. -/
theorem equivCosetSum_eq_relIndex_smul [Finite (Γ ⧸ H)] {m : M} (hm : ∀ h ∈ H, ρ h m = m) :
    equivCosetSum ρ H m =
      H.relIndex (equivStabilizer ρ m) • ∑ᶠ μ ∈ Set.range (fun g : Γ => ρ g m), μ := by
  classical
  set K := equivStabilizer ρ m
  have hHK : H ≤ K := hm
  have hK : ∀ h ∈ K, ρ h m = m := fun h hh => hh
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : K.FiniteIndex := Subgroup.finiteIndex_of_le hHK
  let _ := Fintype.ofFinite (Γ ⧸ H)
  let _ := Fintype.ofFinite (Γ ⧸ K)
  let _ := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  rw [← equivCosetSum_equivStabilizer, equivCosetSum_eq_sum, equivCosetSum_eq_sum]
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he : ∀ q : Γ ⧸ H, ρ q.out m = ρ (e q).1.out m := by
    intro q
    apply apply_eq_of_coset_eq hK
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [QuotientGroup.out_eq']
      have h1 : ((g : Γ ⧸ H).out : Γ ⧸ K) = (g : Γ ⧸ K) := by
        rw [QuotientGroup.eq]
        exact hHK (QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : Γ ⧸ H)))
      rw [h1]
      rfl
  rw [Fintype.sum_congr _ _ he, Fintype.sum_equiv e (fun q => ρ (e q).1.out m)
      (fun x => ρ x.1.out m) (fun q => rfl), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Finset.smul_sum]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/-- For an element fixed by the whole group, the coset sum is `[Γ : H]` times it. -/
theorem equivCosetSum_eq_index_smul [Finite (Γ ⧸ H)] {m : M} (hm : ∀ g, ρ g m = m) :
    equivCosetSum ρ H m = H.index • m := by
  classical
  let _ := Fintype.ofFinite (Γ ⧸ H)
  rw [equivCosetSum_eq_sum, Fintype.sum_congr (fun q : Γ ⧸ H => ρ q.out m) (fun _ => m) (fun q => hm q.out), Finset.sum_const,
    Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]

end CosetSum

/-! ### Star-fixed weights -/

namespace GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k K G)

/-- The star action on the integral character lattice of the split torus `T_K`. -/
def starWeightHom :
    (K ≃ₐ[k] K) →* (characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
      characterLattice d.toSplitPinning.torus) :=
  (RootPairing.Equiv.weightHom d.toSplitPinning.rootDatum).comp
    (d.toSplitPinning.basedRootDatumAut.subtype.comp d.starAction)

@[simp] theorem starWeightHom_apply (σ : K ≃ₐ[k] K)
    (lam : characterLattice d.toSplitPinning.torus) :
    d.starWeightHom σ lam = (d.starAction σ).val.weightEquiv lam :=
  rfl

/-- The weights fixed by the star action of every element of a subgroup `H` of
`K ≃ₐ[k] K`. -/
def fixedWeights (H : Subgroup (K ≃ₐ[k] K)) :
    AddSubgroup (characterLattice d.toSplitPinning.torus) where
  carrier := {lam | ∀ σ ∈ H, (d.starAction σ).val.weightEquiv lam = lam}
  zero_mem' := fun σ _ => map_zero _
  add_mem' := by
    intro a b ha hb σ hσ
    rw [map_add, ha σ hσ, hb σ hσ]
  neg_mem' := by
    intro a ha σ hσ
    rw [map_neg, ha σ hσ]

@[simp] theorem mem_fixedWeights (H : Subgroup (K ≃ₐ[k] K))
    (lam : characterLattice d.toSplitPinning.torus) :
    lam ∈ d.fixedWeights H ↔ ∀ σ ∈ H, (d.starAction σ).val.weightEquiv lam = lam :=
  Iff.rfl

/-- The star-fixed weights: those fixed by the star action of every automorphism. -/
def starFixedWeights : AddSubgroup (characterLattice d.toSplitPinning.torus) :=
  d.fixedWeights ⊤

theorem starFixedWeights_eq_fixedWeights_top : d.starFixedWeights = d.fixedWeights ⊤ :=
  rfl

theorem mem_starFixedWeights (lam : characterLattice d.toSplitPinning.torus) :
    lam ∈ d.starFixedWeights ↔ ∀ σ : K ≃ₐ[k] K, (d.starAction σ).val.weightEquiv lam = lam :=
  ⟨fun h σ => h σ (Subgroup.mem_top σ), fun h σ _ => h σ⟩

/-- Fixed weights are antitone in the subgroup. -/
theorem fixedWeights_antitone {H H' : Subgroup (K ≃ₐ[k] K)} (hHH' : H ≤ H') :
    d.fixedWeights H' ≤ d.fixedWeights H :=
  fun _ hlam σ hσ => hlam σ (hHH' hσ)

theorem starFixedWeights_le_fixedWeights (H : Subgroup (K ≃ₐ[k] K)) :
    d.starFixedWeights ≤ d.fixedWeights H :=
  d.fixedWeights_antitone le_top

/-- Membership in `fixedWeights H` is membership of `H` in the stabilizer of the weight. -/
theorem mem_fixedWeights_iff_le_equivStabilizer (H : Subgroup (K ≃ₐ[k] K))
    (lam : characterLattice d.toSplitPinning.torus) :
    lam ∈ d.fixedWeights H ↔ H ≤ equivStabilizer d.starWeightHom lam :=
  Iff.rfl

/-! ### The coset sum `∑_{σ ∈ Γ/Γ_E} σ ⋆ λ` -/

/-- The coset sum `∑_{σ ∈ Γ/Γ_E} σ ⋆ λ` for an intermediate field `E`, with
`Γ_E = Gal(K/E)` the subgroup fixing `E` pointwise. It uses the chosen representative of
each left coset of `Γ_E`, and a weight is counted again when different cosets give it. -/
def cosetSum (E : IntermediateField k K) (lam : characterLattice d.toSplitPinning.torus) :
    characterLattice d.toSplitPinning.torus :=
  equivCosetSum d.starWeightHom E.fixingSubgroup lam

theorem cosetSum_def (E : IntermediateField k K)
    (lam : characterLattice d.toSplitPinning.torus) :
    d.cosetSum E lam =
      ∑ᶠ q : (K ≃ₐ[k] K) ⧸ E.fixingSubgroup, (d.starAction q.out).val.weightEquiv lam :=
  rfl

/-- A finite-dimensional intermediate field of a Galois extension has a fixing subgroup of
finite index. -/
theorem fixingSubgroup_finiteIndex [IsGalois k K] (E : IntermediateField k K)
    [FiniteDimensional k E] : E.fixingSubgroup.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, ← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Module.finrank_pos.ne'

theorem finite_quotient_fixingSubgroup [IsGalois k K] (E : IntermediateField k K)
    [FiniteDimensional k E] : Finite ((K ≃ₐ[k] K) ⧸ E.fixingSubgroup) := by
  have := fixingSubgroup_finiteIndex E
  infer_instance

variable {d}

/-- Independence of representatives for the coset sum. -/
theorem finsum_section_eq_cosetSum {E : IntermediateField k K}
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.fixedWeights E.fixingSubgroup)
    (s : (K ≃ₐ[k] K) ⧸ E.fixingSubgroup → (K ≃ₐ[k] K)) (hs : ∀ q, (s q : _ ⧸ _) = q) :
    ∑ᶠ q, (d.starAction (s q)).val.weightEquiv lam = d.cosetSum E lam :=
  finsum_section_eq_equivCosetSum (ρ := d.starWeightHom) hlam s hs

/-- Independence of representatives for a left transversal of `Γ_E`. -/
theorem finsum_transversal_eq_cosetSum {E : IntermediateField k K}
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.fixedWeights E.fixingSubgroup) {S : Set (K ≃ₐ[k] K)}
    (hS : Subgroup.IsComplement S (E.fixingSubgroup : Set (K ≃ₐ[k] K))) :
    ∑ᶠ σ : S, (d.starAction σ).val.weightEquiv lam = d.cosetSum E lam :=
  finsum_transversal_eq_equivCosetSum (ρ := d.starWeightHom) hlam hS

/-- Independence of representatives for a finite left transversal of `Γ_E`. -/
theorem sum_transversal_eq_cosetSum {E : IntermediateField k K}
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.fixedWeights E.fixingSubgroup) (S : Finset (K ≃ₐ[k] K))
    (hS : Subgroup.IsComplement (S : Set (K ≃ₐ[k] K)) (E.fixingSubgroup : Set (K ≃ₐ[k] K))) :
    ∑ σ ∈ S, (d.starAction σ).val.weightEquiv lam = d.cosetSum E lam :=
  sum_transversal_eq_equivCosetSum (ρ := d.starWeightHom) hlam S hS

/-- Star invariance: the coset sum is fixed by the full star action. -/
theorem cosetSum_mem_starFixedWeights [IsGalois k K] {E : IntermediateField k K}
    [FiniteDimensional k E] {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.fixedWeights E.fixingSubgroup) :
    d.cosetSum E lam ∈ d.starFixedWeights := by
  have := finite_quotient_fixingSubgroup E
  intro σ _
  exact apply_equivCosetSum (ρ := d.starWeightHom) hlam σ

variable (d) in
/-- Additivity of the coset sum. -/
theorem cosetSum_add [IsGalois k K] (E : IntermediateField k K) [FiniteDimensional k E]
    (lam mu : characterLattice d.toSplitPinning.torus) :
    d.cosetSum E (lam + mu) = d.cosetSum E lam + d.cosetSum E mu := by
  have := finite_quotient_fixingSubgroup E
  exact equivCosetSum_add _ _ lam mu

variable (d) in
theorem cosetSum_zero (E : IntermediateField k K) : d.cosetSum E 0 = 0 :=
  equivCosetSum_zero _ _

variable (d) in
/-- The coset sum as an additive map from the `Γ_E`-fixed weights to the star-fixed
weights. -/
def cosetSumHom [IsGalois k K] (E : IntermediateField k K) [FiniteDimensional k E] :
    d.fixedWeights E.fixingSubgroup →+ d.starFixedWeights where
  toFun lam := ⟨d.cosetSum E lam, cosetSum_mem_starFixedWeights lam.property⟩
  map_zero' := Subtype.ext (d.cosetSum_zero E)
  map_add' lam mu := Subtype.ext (d.cosetSum_add E lam mu)

@[simp] theorem coe_cosetSumHom_apply [IsGalois k K] (E : IntermediateField k K)
    [FiniteDimensional k E] (lam : d.fixedWeights E.fixingSubgroup) :
    (d.cosetSumHom E lam : characterLattice d.toSplitPinning.torus) = d.cosetSum E lam :=
  rfl

/-- Multiplicities: every star translate of `λ` occurs `[Stab(λ) : Γ_E]` times. -/
theorem cosetSum_eq_relIndex_smul [IsGalois k K] {E : IntermediateField k K}
    [FiniteDimensional k E] {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.fixedWeights E.fixingSubgroup) :
    d.cosetSum E lam =
      E.fixingSubgroup.relIndex (equivStabilizer d.starWeightHom lam) •
        ∑ᶠ mu ∈ Set.range (fun σ : K ≃ₐ[k] K => (d.starAction σ).val.weightEquiv lam), mu := by
  have := finite_quotient_fixingSubgroup E
  exact equivCosetSum_eq_relIndex_smul (ρ := d.starWeightHom) hlam

/-- When `Γ_E` is the full stabilizer of `λ`, the coset sum is the sum over the star orbit
of `λ`, each weight once. -/
theorem cosetSum_eq_finsum_orbit {E : IntermediateField k K}
    {lam : characterLattice d.toSplitPinning.torus}
    (hE : E.fixingSubgroup = equivStabilizer d.starWeightHom lam) :
    d.cosetSum E lam =
      ∑ᶠ mu ∈ Set.range (fun σ : K ≃ₐ[k] K => (d.starAction σ).val.weightEquiv lam), mu := by
  rw [cosetSum, hE]
  exact equivCosetSum_equivStabilizer (ρ := d.starWeightHom) lam

/-- For a star-fixed weight the coset sum is `[E : k] • λ`. -/
theorem cosetSum_of_mem_starFixedWeights [IsGalois k K] {E : IntermediateField k K}
    [FiniteDimensional k E] {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.starFixedWeights) :
    d.cosetSum E lam = Module.finrank k E • lam := by
  have := finite_quotient_fixingSubgroup E
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact equivCosetSum_eq_index_smul (ρ := d.starWeightHom)
    (fun σ => (d.mem_starFixedWeights lam).mp hlam σ)

end GaloisPinningData

end Langlands.GroupScheme
