import Langlands.BaseChange.TwistedCharacter.GLTraceRegularity
import Langlands.BaseChange.TwistedCharacter.StandardTraceSpan
import Langlands.BaseChange.TwistedCharacter.RegularComparison
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.BaseChange.TwistedCharacter.CyclicExtension
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Langlands.AllField.Group.GL.UnramifiedCharacter

/-! # Regular families of induced twisted traces in unramified parameters -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w z uI uG uV

section Product

variable {ι : Type uI} [Fintype ι] {H : ι → Type uG} [∀ i, Group (H i)]

/-- The product `m ↦ ∏ i, χ i (m i)` of characters of the factors of a finite product. -/
def piProductCharacter (χ : ∀ i, H i →* ℂˣ) : (∀ i, H i) →* ℂˣ :=
  ∏ i, (χ i).comp (Pi.evalMonoidHom H i)

@[simp]
theorem piProductCharacter_apply (χ : ∀ i, H i →* ℂˣ) (m : ∀ i, H i) :
    piProductCharacter χ m = ∏ i, χ i (m i) := by
  simp [piProductCharacter]

variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Twisting an external tensor product by a product character twists each factor. -/
theorem twist_external_piProductCharacter (χ : ∀ i, H i →* ℂˣ)
    (ρ : ∀ i, Representation ℂ (H i) (V i)) :
    twist (piProductCharacter χ) (FiniteTensor.external ρ) =
      FiniteTensor.external (fun i => twist (χ i) (ρ i)) := by
  ext m : 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change ((piProductCharacter χ m : ℂˣ) : ℂ) • FiniteTensor.external ρ m
      (PiTensorProduct.tprod ℂ x) =
    FiniteTensor.external (fun i => twist (χ i) (ρ i)) m (PiTensorProduct.tprod ℂ x)
  rw [FiniteTensor.external_tprod, FiniteTensor.external_tprod, piProductCharacter_apply,
    Units.coe_prod]
  change _ = PiTensorProduct.tprod ℂ (fun i => ((χ i (m i) : ℂˣ) : ℂ) • ρ i (m i) (x i))
  rw [MultilinearMap.map_smul_univ]

end Product

section Congruence

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {X : Type uV} [AddCommGroup X] [Module ℂ X]

/-- Equal inducing representations with intertwiners of the same underlying linear map
give the same induced twisted trace. -/
theorem twistedDistribution_inducedSigma_congr {Ξ₁ Ξ₂ : Representation ℂ (B.Levi E) X}
    (h : Ξ₁ = Ξ₂) (B₁ : Ξ₁.Equiv (Ξ₁.comp (leviAut σ B).toMonoidHom))
    (B₂ : Ξ₂.Equiv (Ξ₂.comp (leviAut σ B).toMonoidHom))
    (hB : (B₁ : X → X) = B₂)
    (h₁ : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ₁.comp (B.leviProjection E))))
    (h₂ : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ₂.comp (B.leviProjection E)))) :
    twistedDistribution μ _ h₁ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ₁ B₁).toLinearMap =
      twistedDistribution μ _ h₂ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ₂ B₂).toLinearMap := by
  subst h
  have hB' : B₁ = B₂ := Representation.Equiv.ext hB
  subst hB'
  rfl

end Congruence

section Characters

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The unramified character `g ↦ z ^ ord(det g)` of `GL_m(E)`. -/
def determinantUnramified (m : ℕ) (z : ℂˣ) : GeneralLinear m E →* ℂˣ :=
  (zpowersHom ℂˣ z).comp (determinantOrderHom E m)

theorem determinantUnramified_apply (m : ℕ) (z : ℂˣ) (g : GeneralLinear m E) :
    determinantUnramified E m z g = z ^ (determinantOrderHom E m g).toAdd := rfl

theorem isUnramifiedCharacter_determinantUnramified (m : ℕ) (z : ℂˣ) :
    IsUnramifiedCharacter (determinantUnramified E m z) := by
  intro K hK k hk
  rw [determinantUnramified_apply, determinantOrderHom_eq_one_of_mem_compact E m K hK hk]
  rfl

theorem isOpen_ker_determinantUnramified (m : ℕ) (z : ℂˣ) :
    IsOpen ((determinantUnramified E m z).ker : Set (GeneralLinear m E)) := by
  let := LocalFieldTopology.generalLinear_t2Space E m
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E m
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E m
  exact IsUnramifiedCharacter.isOpen_ker (isUnramifiedCharacter_determinantUnramified E m z)

theorem norm_determinantUnramified (m : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (g : GeneralLinear m E) : ‖(determinantUnramified E m z g : ℂ)‖ = 1 := by
  rw [determinantUnramified_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hz, one_zpow]

theorem determinantUnramified_mul (m : ℕ) (z w : ℂˣ) :
    determinantUnramified E m (z * w) = determinantUnramified E m z * determinantUnramified E m w := by
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.mul_apply, determinantUnramified_apply, mul_zpow]

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]

/-- The determinant order is invariant under the entrywise action of `σ`. -/
theorem determinantOrderHom_entrywiseAut (σ : E ≃ₐ[F] E) (m : ℕ) (g : GeneralLinear m E) :
    determinantOrderHom E m (entrywiseAut σ m g) = determinantOrderHom E m g := by
  let T := LocalFieldData.ofInstances E
  have hN := determinantNorm_entrywiseAut σ m g
  have hker : determinant (entrywiseAut σ m g) * (determinant g)⁻¹ ∈ T.normalizedAbsUnits.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change T.determinantNorm m (entrywiseAut σ m g) * (T.determinantNorm m g)⁻¹ = 1
    rw [hN, mul_inv_cancel]
  rw [← T.ker_ordUnits, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
  exact hker

theorem determinantUnramified_entrywiseAut (σ : E ≃ₐ[F] E) (m : ℕ) (z : ℂˣ)
    (g : GeneralLinear m E) :
    determinantUnramified E m z (entrywiseAut σ m g) = determinantUnramified E m z g := by
  rw [determinantUnramified_apply, determinantUnramified_apply,
    determinantOrderHom_entrywiseAut E σ m g]

end Characters

section LeviCharacters

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {N : ℕ} (C : BlockShape N) {r : ℕ}
  (g : Fin C.length → Fin r)

/-- The unramified character `m ↦ ∏ j, z (g j) ^ ord(det m_j)` of the block Levi, with the
parameters of the blocks assigned by `g`. -/
def leviUnramified (z : Fin r → ℂˣ) : C.Levi E →* ℂˣ :=
  piProductCharacter (fun j => determinantUnramified E (C.size j) (z (g j)))

theorem leviUnramified_apply (z : Fin r → ℂˣ) (m : C.Levi E) :
    leviUnramified E C g z m = ∏ j, z (g j) ^ (determinantOrderHom E (C.size j) (m j)).toAdd :=
  piProductCharacter_apply _ m

theorem isUnramifiedCharacter_leviUnramified (z : Fin r → ℂˣ) :
    IsUnramifiedCharacter (leviUnramified E C g z) := by
  intro K hK k hk
  rw [leviUnramified, piProductCharacter_apply]
  refine Finset.prod_eq_one fun j _ => ?_
  apply isUnramifiedCharacter_determinantUnramified E _ _ (K.map (Pi.evalMonoidHom _ j))
  · rw [Subgroup.coe_map]
    exact hK.image (continuous_apply j)
  · exact ⟨k, hk, rfl⟩

theorem isOpen_ker_leviUnramified (z : Fin r → ℂˣ) :
    IsOpen ((leviUnramified E C g z).ker : Set (C.Levi E)) := by
  let U : Subgroup (C.Levi E) :=
    Subgroup.pi Set.univ (fun j => (determinantUnramified E (C.size j) (z (g j))).ker)
  have hU : IsOpen (U : Set (C.Levi E)) := by
    change IsOpen (Set.pi Set.univ fun j =>
      ((determinantUnramified E (C.size j) (z (g j))).ker : Set (GeneralLinear (C.size j) E)))
    exact isOpen_set_pi Set.finite_univ (fun j _ => isOpen_ker_determinantUnramified E _ _)
  refine Subgroup.isOpen_mono (fun m hm => ?_) hU
  rw [MonoidHom.mem_ker, leviUnramified, piProductCharacter_apply]
  exact Finset.prod_eq_one fun j _ => hm j (Set.mem_univ j)

theorem norm_leviUnramified (z : Fin r → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) (m : C.Levi E) :
    ‖(leviUnramified E C g z m : ℂ)‖ = 1 := by
  rw [leviUnramified, piProductCharacter_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun j _ => norm_determinantUnramified E _ _ (hz _) _

/-- The exponent vector of `m` in the Laurent monomial `leviUnramified E C g z m`. -/
def leviUnramifiedExponent (m : C.Levi E) : Fin r → ℤ :=
  fun k => ∑ j ∈ Finset.univ.filter (fun j => g j = k),
    (determinantOrderHom E (C.size j) (m j)).toAdd

theorem leviUnramified_eq_prod_exponent (z : Fin r → ℂˣ) (m : C.Levi E) :
    ((leviUnramified E C g z m : ℂˣ) : ℂ) =
      ∏ k, ((z k ^ leviUnramifiedExponent E C g m k : ℂˣ) : ℂ) := by
  classical
  rw [leviUnramified_apply, ← Units.coe_prod]
  congr 1
  rw [← Finset.prod_fiberwise Finset.univ g
    (fun j => z (g j) ^ (determinantOrderHom E (C.size j) (m j)).toAdd)]
  have key (t : Finset (Fin C.length)) (f : Fin C.length → ℤ) (a : ℂˣ) :
      ∏ i ∈ t, a ^ f i = a ^ ∑ i ∈ t, f i := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [leviUnramifiedExponent, ← key]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]

theorem leviUnramified_leviAut (σ : E ≃ₐ[F] E) (z : Fin r → ℂˣ) (m : C.Levi E) :
    leviUnramified E C g z (leviAut σ C m) = leviUnramified E C g z m := by
  rw [leviUnramified, piProductCharacter_apply, piProductCharacter_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [leviAut_apply]
  exact determinantUnramified_entrywiseAut E σ _ _ _

end LeviCharacters

section Family

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {N : ℕ} (C : BlockShape N) {r : ℕ} (g : Fin C.length → Fin r)
  {V : Fin C.length → Type w} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
  (R : ∀ j, Representation ℂ (GeneralLinear (C.size j) E) (V j))
  (A : ∀ j, SigmaIntertwiner σ (C.size j) (R j))
  (κ : C.Levi E →* ℂˣ) (hκ : IsOpen (κ.ker : Set (C.Levi E)))
  (hκσ : ∀ m, κ (leviAut σ C m) = κ m)

/-- The half modulus of a standard block Levi is invariant under `σ`. -/
theorem leviHalfModulus_leviAut (m : C.Levi E) :
    (LocalFieldData.ofInstances E).leviHalfModulus C (leviAut σ C m) =
      (LocalFieldData.ofInstances E).leviHalfModulus C m := by
  apply Units.ext
  rw [LocalFieldData.leviHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
    leviModulus_leviAut]

/-- The inducing representation `κ ⊗ (R_1 ⊗ ⋯ ⊗ R_k)` of the family; for `κ` the half
modulus this is the normalized inducing representation. -/
def familyInducing : Representation ℂ (C.Levi E) (PiTensorProduct ℂ V) :=
  twist κ (C.blockTensor R)

/-- The tensor product of the block intertwiners on the normalized inducing representation. -/
def familyInducingIntertwiner :
    (familyInducing C R κ).Equiv ((familyInducing C R κ).comp (leviAut σ C).toMonoidHom) :=
  twistTwistedIntertwiner (leviAut σ C) κ hκσ (leviTensorIntertwiner σ C A)

omit [TopologicalSpace F] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [IsModuleTopology F E] in
theorem familyInducingIntertwiner_apply (x : PiTensorProduct ℂ V) :
    familyInducingIntertwiner σ C R A κ hκσ x = leviTensorIntertwiner σ C A x := rfl

/-- Twisting the inducing representation by the unramified Levi character twists the blocks. -/
theorem twist_familyInducing (z : Fin r → ℂˣ) :
    twist (leviUnramified E C g z) (familyInducing C R κ) =
      twist κ
        (C.blockTensor (fun j => twist (determinantUnramified E (C.size j) (z (g j))) (R j))) := by
  have h := twist_external_piProductCharacter (H := fun j => GeneralLinear (C.size j) E)
    (fun j => determinantUnramified E (C.size j) (z (g j))) R
  change twist (leviUnramified E C g z) (twist κ (FiniteTensor.external R)) =
    twist κ (FiniteTensor.external _)
  rw [← h, twist_twist, twist_twist]
  exact congrArg (fun χ : C.Levi E →* ℂˣ => twist χ (FiniteTensor.external R))
    (mul_comm (leviUnramified E C g z) κ)

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
include hκ in
theorem isAdmissible_familyInducing (hR : ∀ j, IsAdmissible (R j)) :
    IsAdmissible (familyInducing C R κ) :=
  (isAdmissible_twist_iff _ _ hκ).mpr (FiniteTensor.isAdmissible_external R hR)

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
theorem isIrreducible_familyInducing (hR : ∀ j, IsAdmissible (R j))
    (hirr : ∀ j, (R j).IsIrreducible) : (familyInducing C R κ).IsIrreducible := by
  let (j : Fin C.length) : (R j).IsIrreducible := hirr j
  exact (isIrreducible_twist_iff _ _).mpr (FiniteTensor.isIrreducible_external R
    (fun j f => (admissibleSchur_scalarEndomorphism _ (hR j) inferInstance f).exists))

include hκ in
theorem isAdmissible_familyInduced (hR : ∀ j, IsAdmissible (R j)) (z : Fin r → ℂˣ) :
    IsAdmissible (Induction.smoothInduced (C.parabolic E)
      ((twist (leviUnramified E C g z) (familyInducing C R κ)).comp (C.leviProjection E))) := by
  let T := LocalFieldData.ofInstances E
  let : CompactSpace (Induction.LeftQuotient (C.parabolic E)) :=
    AllField.Parabolic.parabolicQuotientCompact E T C
  have hX : IsAdmissible (twist (leviUnramified E C g z) (familyInducing C R κ)) :=
    (isAdmissible_twist_iff _ _ (isOpen_ker_leviUnramified E C g z)).mpr
      (isAdmissible_familyInducing C R κ hκ hR)
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _
    ((AllField.Parabolic.leviInflationAdmissibility E T C _ _).mpr hX)

variable [MeasurableSpace (GeneralLinear N E)] [BorelSpace (GeneralLinear N E)]
  [T2Space (GeneralLinear N E)] [LocallyCompactSpace (GeneralLinear N E)]
  [TotallyDisconnectedSpace (GeneralLinear N E)]
  (μ : Measure (GeneralLinear N E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The twisted trace of the unnormalized induction of the unramified twist of the
normalized inducing representation, as a function of the unramified parameters. -/
def unramifiedFamilyTrace (hR : ∀ j, IsAdmissible (R j)) (z : Fin r → ℂˣ) :
    Distribution (GeneralLinear N E) :=
  twistedDistribution μ _ (isAdmissible_familyInduced C g R κ hκ hR z)
    (TwistedPaleyWiener.inducedSigmaIntertwiner σ C
      (twist (leviUnramified E C g z) (familyInducing C R κ))
      (twistTwistedIntertwiner (leviAut σ C) (leviUnramified E C g z)
        (leviUnramified_leviAut E C g σ z) (familyInducingIntertwiner σ C R A κ hκσ))).toLinearMap

/-- Every test function evaluates the family to a Laurent polynomial in the parameters. -/
theorem unramifiedFamilyTrace_regular {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    (hR : ∀ j, IsAdmissible (R j)) (hirr : ∀ j, (R j).IsIrreducible)
    (f : SchwartzBruhat (GeneralLinear N E)) :
    ∃ q : AddMonoidAlgebra ℂ (Fin r → ℤ), ∀ z,
      unramifiedFamilyTrace σ C g R A κ hκ hκσ μ hR z f = Plancherel.finiteLaurentEvaluation z q := by
  obtain ⟨s, c, hc⟩ := sigmaInducedTraceRegularity.{u,v,w} F E σ d hd hσ N μ f C _
    (familyInducing C R κ) (isAdmissible_familyInducing C R κ hκ hR)
    (isIrreducible_familyInducing C R κ hR hirr) (familyInducingIntertwiner σ C R A κ hκσ)
  refine ⟨∑ m ∈ s, AddMonoidAlgebra.single (leviUnramifiedExponent E C g m) (c m), fun z => ?_⟩
  have h := hc (leviUnramified E C g z) (isUnramifiedCharacter_leviUnramified E C g z)
    (leviUnramified_leviAut E C g σ z) (isAdmissible_familyInduced C g R κ hκ hR z)
  change unramifiedFamilyTrace σ C g R A κ hκ hκσ μ hR z f = _ at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Plancherel.finiteLaurentEvaluation_single, leviUnramified_eq_prod_exponent, mul_comm]

omit [IsModuleTopology F E] [MeasurableSpace (GeneralLinear N E)] [BorelSpace (GeneralLinear N E)]
  [T2Space (GeneralLinear N E)] [LocallyCompactSpace (GeneralLinear N E)]
  [TotallyDisconnectedSpace (GeneralLinear N E)] in
/-- The family representation at a parameter is the induction of `κ` times the tensor of
the twisted blocks. -/
theorem nonempty_familyInduced_equiv (z : Fin r → ℂˣ) :
    Nonempty ((Induction.smoothInduced (C.parabolic E)
      ((twist (leviUnramified E C g z) (familyInducing C R κ)).comp (C.leviProjection E))).Equiv
      (Induction.smoothInduced (C.parabolic E)
        ((twist κ (C.blockTensor (fun j =>
          twist (determinantUnramified E (C.size j) (z (g j))) (R j)))).comp
            (C.leviProjection E)))) := by
  rw [twist_familyInducing]
  exact ⟨Representation.Equiv.refl _⟩

omit [TopologicalSpace F] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [IsModuleTopology F E] [MeasurableSpace (GeneralLinear N E)] [BorelSpace (GeneralLinear N E)]
  [T2Space (GeneralLinear N E)] [LocallyCompactSpace (GeneralLinear N E)]
  [TotallyDisconnectedSpace (GeneralLinear N E)] in
/-- The tensor product of block intertwiners of order dividing `d` has order dividing `d`. -/
theorem leviTensorIntertwiner_pow {d : ℕ} (hA : ∀ j, (A j).toLinearMap ^ d = 1) :
    (leviTensorIntertwiner σ C A).toLinearMap ^ d = 1 := by
  change (PiTensorProduct.map (fun j => (A j).toLinearMap)) ^ d = 1
  rw [← PiTensorProduct.map_pow]
  have h : (fun j => (A j).toLinearMap) ^ d = fun _ => 1 :=
    funext fun j => by rw [Pi.pow_apply, hA j]
  rw [h]
  exact PiTensorProduct.map_one

omit [MeasurableSpace (GeneralLinear N E)] [BorelSpace (GeneralLinear N E)]
  [T2Space (GeneralLinear N E)] [LocallyCompactSpace (GeneralLinear N E)]
  [TotallyDisconnectedSpace (GeneralLinear N E)] in
/-- If `σ ^ d = 1` and the block intertwiners have order dividing `d`, the induced
σ-intertwiner of the family has order dividing `d` at every parameter. Both hypotheses are
needed: the induced operator also moves functions on `GL_N(E)` by `entrywiseAut σ N`. -/
theorem familyIntertwiner_pow {d : ℕ} (hσ : σ ^ d = 1) (hA : ∀ j, (A j).toLinearMap ^ d = 1)
    (z : Fin r → ℂˣ) :
    (TwistedPaleyWiener.inducedSigmaIntertwiner σ C
      (twist (leviUnramified E C g z) (familyInducing C R κ))
      (twistTwistedIntertwiner (leviAut σ C) (leviUnramified E C g z)
        (leviUnramified_leviAut E C g σ z) (familyInducingIntertwiner σ C R A κ hκσ))).toLinearMap ^ d
      = 1 := by
  have hθ : (entrywiseAut σ N) ^ d = 1 := by
    change (entrywiseAutHom N) σ ^ d = 1
    rw [← map_pow, hσ, map_one]
  exact inducedTwistedIntertwiner_pow_eq_one _ _ _ _ _ _ _ _ _ _ hθ
    (leviTensorIntertwiner_pow σ C R A hA)

omit [TopologicalSpace F] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [IsModuleTopology F E] [MeasurableSpace (GeneralLinear N E)] [BorelSpace (GeneralLinear N E)]
  [T2Space (GeneralLinear N E)] [LocallyCompactSpace (GeneralLinear N E)]
  [TotallyDisconnectedSpace (GeneralLinear N E)] in
/-- Scaling the block intertwiners scales their tensor product by the product of the scalars. -/
theorem leviTensorIntertwiner_scale (c : Fin C.length → ℂˣ) :
    (leviTensorIntertwiner σ C (fun j => scaleTwistingEquiv (entrywiseAut σ (C.size j)) (c j)
      (A j))).toLinearMap = (∏ j, (c j : ℂ)) • (leviTensorIntertwiner σ C A).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change PiTensorProduct.congr _ (PiTensorProduct.tprod ℂ x) =
    (∏ j, (c j : ℂ)) • PiTensorProduct.congr _ (PiTensorProduct.tprod ℂ x)
  rw [PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod]
  change PiTensorProduct.tprod ℂ (fun j => (c j : ℂ) • (A j) (x j)) = _
  rw [MultilinearMap.map_smul_univ]
  rfl

/-- Scaling the block intertwiners scales the family by the product of the scalars. -/
theorem unramifiedFamilyTrace_scale (hR : ∀ j, IsAdmissible (R j)) (c : Fin C.length → ℂˣ)
    (z : Fin r → ℂˣ) :
    unramifiedFamilyTrace σ C g R (fun j => scaleTwistingEquiv (entrywiseAut σ (C.size j)) (c j)
      (A j)) κ hκ hκσ μ hR z = (∏ j, (c j : ℂ)) • unramifiedFamilyTrace σ C g R A κ hκ hκσ μ hR z := by
  unfold unramifiedFamilyTrace
  rw [← twistedDistribution_smul]
  congr 1
  apply LinearMap.ext
  intro f
  apply Induction.smoothFunctions_ext
  intro y
  change (leviTensorIntertwiner σ C (fun j => scaleTwistingEquiv (entrywiseAut σ (C.size j)) (c j)
      (A j))) _ = (∏ j, (c j : ℂ)) • (leviTensorIntertwiner σ C A) _
  exact LinearMap.congr_fun (leviTensorIntertwiner_scale σ C R A c) _

variable {C' : BlockShape N} {g' : Fin C'.length → Fin r}
  {V' : Fin C'.length → Type w} [∀ j, AddCommGroup (V' j)] [∀ j, Module ℂ (V' j)]
  {R' : ∀ j, Representation ℂ (GeneralLinear (C'.size j) E) (V' j)}
  {A' : ∀ j, SigmaIntertwiner σ (C'.size j) (R' j)}
  {κ' : C'.Levi E →* ℂˣ} (hκ' : IsOpen (κ'.ker : Set (C'.Levi E)))
  (hκσ' : ∀ m, κ' (leviAut σ C' m) = κ' m)

/-- Two regular families whose unitary specializations are irreducible and equivalent are
related by one root of unity on the whole parameter torus. -/
theorem unramifiedFamilyTrace_comparison {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    (hR : ∀ j, IsAdmissible (R j)) (hirr : ∀ j, (R j).IsIrreducible)
    (hA : ∀ j, (A j).toLinearMap ^ d = 1)
    (hR' : ∀ j, IsAdmissible (R' j)) (hirr' : ∀ j, (R' j).IsIrreducible)
    (hA' : ∀ j, (A' j).toLinearMap ^ d = 1)
    (hunit : ∀ z : Fin r → ℂˣ, (∀ k, ‖(z k : ℂ)‖ = 1) →
      (Induction.smoothInduced (C.parabolic E)
        ((twist κ (C.blockTensor (fun j =>
          twist (determinantUnramified E (C.size j) (z (g j))) (R j)))).comp
            (C.leviProjection E))).IsIrreducible ∧
      Nonempty ((Induction.smoothInduced (C.parabolic E)
        ((twist κ (C.blockTensor (fun j =>
          twist (determinantUnramified E (C.size j) (z (g j))) (R j)))).comp
            (C.leviProjection E))).Equiv
        (Induction.smoothInduced (C'.parabolic E)
          ((twist κ' (C'.blockTensor (fun j =>
            twist (determinantUnramified E (C'.size j) (z (g' j))) (R' j)))).comp
              (C'.leviProjection E))))) :
    ∃ c : ℂ, c ^ d = 1 ∧ ∀ z,
      unramifiedFamilyTrace σ C' g' R' A' κ' hκ' hκσ' μ hR' z =
        c • unramifiedFamilyTrace σ C g R A κ hκ hκσ μ hR z := by
  let u : (Fin r → Circle) → (Fin r → ℂˣ) := fun z i => Circle.toUnits (z i)
  have hu (z : Fin r → Circle) (k : Fin r) : ‖((u z k : ℂˣ) : ℂ)‖ = 1 := Circle.norm_coe (z k)
  let ρ (z : Fin r → Circle) := Induction.smoothInduced (C.parabolic E)
    ((twist (leviUnramified E C g (u z)) (familyInducing C R κ)).comp (C.leviProjection E))
  let π (z : Fin r → Circle) := Induction.smoothInduced (C'.parabolic E)
    ((twist (leviUnramified E C' g' (u z)) (familyInducing C' R' κ')).comp (C'.leviProjection E))
  have hρirr (z) : (ρ z).IsIrreducible := by
    obtain ⟨e⟩ := nonempty_familyInduced_equiv C g R κ (u z)
    exact (isIrreducible_iff_of_equiv e).mpr (hunit (u z) (hu z)).1
  have he (z) : Nonempty ((ρ z).Equiv (π z)) := by
    obtain ⟨e⟩ := nonempty_familyInduced_equiv C g R κ (u z)
    obtain ⟨e'⟩ := nonempty_familyInduced_equiv C' g' R' κ' (u z)
    obtain ⟨f⟩ := (hunit (u z) (hu z)).2
    exact ⟨(e.trans f).trans e'.symm⟩
  exact regularTwistedDistributionComparison μ (entrywiseAut σ N) hd
    (unramifiedFamilyTrace σ C' g' R' A' κ' hκ' hκσ' μ hR')
    (unramifiedFamilyTrace σ C g R A κ hκ hκσ μ hR)
    (unramifiedFamilyTrace_regular σ C' g' R' A' κ' hκ' hκσ' μ hd hσ hR' hirr')
    (unramifiedFamilyTrace_regular σ C g R A κ hκ hκσ μ hd hσ hR hirr)
    _ _ ρ π (fun z => isAdmissible_familyInduced C g R κ hκ hR (u z))
    (fun z => isAdmissible_familyInduced C' g' R' κ' hκ' hR' (u z)) hρirr (fun z => (he z).some)
    _ _ (fun z => familyIntertwiner_pow σ C g R A κ hκσ hσ hA (u z))
    (fun z => familyIntertwiner_pow σ C' g' R' A' κ' hκσ' hσ hA' (u z)) (fun _ => rfl)
    (fun _ => rfl)

end Family

end Langlands.BaseChange
