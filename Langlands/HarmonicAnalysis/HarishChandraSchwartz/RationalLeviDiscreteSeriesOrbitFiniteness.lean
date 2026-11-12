import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFinitenessStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Discrete-series orbits under topological group isomorphisms; Theorem VIII.1.2 for `M_I(F)`

For a topological group isomorphism `e : H ≃ₜ* G`, pulling representations back along `e`
identifies the classes of irreducible admissible representations of `G` and `H`, their fixed
vectors, their square integrability modulo corresponding central subgroups (for corresponding
Haar measures) and their orbits under corresponding unitary unramified characters. Hence the
finiteness of the sets `Θ^K` (`discreteSeriesFixedOrbits`) transfers from `H` to `G`.

Applied to `e : L(F) ≃ₜ* M_I(F)`, `L = Standard.leviScheme i ν (rootSet i ν I)` the Levi group
scheme, this derives Theorem VIII.1.2 for the actual Levi subgroup `M_I(F)` of `G(F)` from the
published statement `RationalDiscreteSeriesOrbitFinitenessStatement` for the connected reductive
group scheme `L` and its split component (`standardLeviSplitComponentStatement`). The conclusion
has the form of the hypothesis `hfin` (Theorem VIII.1.2 for `M_I(F)`) of Remark VIII.1.3.
-/

noncomputable section

universe u uG uH uV uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Classes

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] (e : H ≃ₜ* G)

/-- The pullback `A ∘ e` of an irreducible admissible representation of `G` along `e : H ≃ₜ* G`. -/
def IrreducibleAdmissibleRep.pullback
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    IrreducibleAdmissibleRep.{0, uH, uV} (k := ℂ) (G := H) :=
  ⟨SmoothRep.pullback e A.obj,
    (isIrreducible_comp_continuousMulEquiv_iff A.obj.representation e).mpr A.property.1,
    (isAdmissible_comp_continuousMulEquiv_iff A.obj.representation e).mpr A.property.2⟩

@[simp]
theorem IrreducibleAdmissibleRep.pullback_representation
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    (IrreducibleAdmissibleRep.pullback e A).obj.representation =
      A.obj.representation.comp e.toMonoidHom :=
  rfl

/-- **Pullback of classes** along `e : H ≃ₜ* G`: the class of `A ∘ e`. -/
def SmoothDualClass.pullback :
    SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) → SmoothDualClass.{0, uH, uV} (k := ℂ) (G := H) :=
  Quotient.map (IrreducibleAdmissibleRep.pullback e) (fun _ _ ⟨i⟩ =>
    ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso (SmoothRep.pullbackEquiv e
      (SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso i))))⟩)

@[simp]
theorem SmoothDualClass.pullback_mk (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    SmoothDualClass.pullback e (Quotient.mk _ A) =
      Quotient.mk _ (IrreducibleAdmissibleRep.pullback e A) :=
  rfl

/-- Pullback along `e` is injective on classes: an equivalence between `A ∘ e` and `B ∘ e` is an
equivalence between `A` and `B`, since `e` is surjective. -/
theorem SmoothDualClass.pullback_injective :
    Function.Injective (SmoothDualClass.pullback.{uG, uH, uV} e) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h A =>
  induction y using Quotient.inductionOn with
  | h B =>
  obtain ⟨i⟩ := Quotient.exact hxy
  let f := SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := H)).ι.mapIso i)
  let f' : A.obj.representation.Equiv B.obj.representation :=
    { toLinearEquiv := f.toLinearEquiv
      isIntertwining' := fun g => by
        have h := f.isIntertwining' (e.symm g)
        change f.toLinearEquiv.toLinearMap ∘ₗ A.obj.representation (e (e.symm g)) =
          B.obj.representation (e (e.symm g)) ∘ₗ f.toLinearEquiv.toLinearMap at h
        rw [e.apply_symm_apply] at h
        exact h }
  exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso f')⟩

/-- Fixed vectors: `A ∘ e` has a nonzero `K`-fixed vector iff `A` has a nonzero
`e(K)`-fixed vector. -/
theorem SmoothDualClass.hasFixedVector_pullback (K : Subgroup H)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    SmoothDualClass.HasFixedVector K (SmoothDualClass.pullback e ω) ↔
      SmoothDualClass.HasFixedVector (K.comap e.symm.toMonoidHom) ω := by
  induction ω using Quotient.inductionOn with
  | h A =>
    change fixedVectors (A.obj.representation.comp e.toMonoidHom) K ≠ ⊥ ↔
      fixedVectors A.obj.representation (K.comap e.symm.toMonoidHom) ≠ ⊥
    rw [fixedVectors_comp_mulEquiv A.obj.representation e.toMulEquiv K]
    rfl

/-- Pullback commutes with twisting: `(A ⊗ χ) ∘ e = (A ∘ e) ⊗ (χ ∘ e)`. -/
theorem SmoothDualClass.pullback_twist (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hχe : IsOpen ((χ.comp e.toMonoidHom).ker : Set H))
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    SmoothDualClass.pullback e (SmoothDualClass.twist χ hχ ω) =
      SmoothDualClass.twist (χ.comp e.toMonoidHom) hχe (SmoothDualClass.pullback e ω) := by
  induction ω using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
      (SmoothRep.mkIso (equivOfRepresentationEq rfl))⟩

end Classes

section CentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] (e : H ≃ₜ* G)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The restriction of `e` to the centers: `e` maps the center of `H` into the center of `G`. -/
def centerHomOfEquiv : Subgroup.center H →* Subgroup.center G where
  toFun z := ⟨e (z : H), by
    rw [Subgroup.mem_center_iff]
    intro g
    have hz := Subgroup.mem_center_iff.mp z.property (e.symm g)
    calc g * e (z : H) = e (e.symm g * (z : H)) := by rw [map_mul, e.apply_symm_apply]
      _ = e ((z : H) * e.symm g) := by rw [hz]
      _ = e (z : H) * g := by rw [map_mul, e.apply_symm_apply]⟩
  map_one' := Subtype.ext (map_one e)
  map_mul' x y := Subtype.ext (map_mul e (x : H) (y : H))

/-- The restriction of `e` to the centers is continuous. -/
theorem continuous_centerHomOfEquiv : Continuous (centerHomOfEquiv e) :=
  Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _

/-- A unitary central character of `ρ` gives one of `ρ ∘ e`. -/
def UnitaryCentralCharacter.pullback {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ) :
    UnitaryCentralCharacter (ρ.comp e.toMonoidHom) where
  character := c.character.comp (centerHomOfEquiv e)
  isOpen_ker := c.isOpen_ker.preimage (continuous_centerHomOfEquiv e)
  norm_eq_one _ := c.norm_eq_one _
  acts z v := c.acts (centerHomOfEquiv e z) v

/-- A unitary central character of `ρ ∘ e` gives one of `ρ`. -/
def UnitaryCentralCharacter.ofPullback {ρ : Representation ℂ G V}
    (c : UnitaryCentralCharacter (ρ.comp e.toMonoidHom)) : UnitaryCentralCharacter ρ where
  character := c.character.comp (centerHomOfEquiv e.symm)
  isOpen_ker := c.isOpen_ker.preimage (continuous_centerHomOfEquiv e.symm)
  norm_eq_one _ := c.norm_eq_one _
  acts z v := by
    have h := c.acts (centerHomOfEquiv e.symm z) v
    change ρ (e (e.symm (z : G))) v = _ at h
    rw [e.apply_symm_apply] at h
    exact h

end CentralCharacter

section SquareIntegrable

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (e : H ≃ₜ* G)
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
  (hAB : B.map e.toMulEquiv.toMonoidHom = A)

/-- The isomorphism `H/B ≃ₜ* G/A` induced by `e` when `e(B) = A`. -/
def quotientContinuousMulEquiv : (H ⧸ B) ≃ₜ* (G ⧸ A) :=
  { QuotientGroup.congr B A e.toMulEquiv hAB with
    continuous_toFun := by
      apply (QuotientGroup.isQuotientMap_mk B).continuous_iff.mpr
      exact QuotientGroup.continuous_mk.comp e.continuous
    continuous_invFun := by
      apply (QuotientGroup.isQuotientMap_mk A).continuous_iff.mpr
      exact QuotientGroup.continuous_mk.comp e.symm.continuous }

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem quotientContinuousMulEquiv_mk (h : H) :
    quotientContinuousMulEquiv e A B hAB (QuotientGroup.mk h) = QuotientGroup.mk (e h) :=
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The coefficient norms of `ρ ∘ e` on `H/B` are those of `ρ` on `G/A`, composed with the
quotient isomorphism. -/
theorem centralSubgroupCoefficientNorm_pullback {ρ : Representation ℂ G V}
    (c : UnitaryCentralCharacter ρ) (c' : UnitaryCentralCharacter (ρ.comp e.toMonoidHom))
    (ℓ : Module.Dual ℂ V) (v : V) :
    centralSubgroupCoefficientNorm B hB c' ℓ v =
      centralSubgroupCoefficientNorm A hA c ℓ v ∘ quotientContinuousMulEquiv e A B hAB := by
  funext x
  induction x using QuotientGroup.induction_on with
  | H h => rfl

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
  (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure] (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure]
  (hμ : μH.map (quotientContinuousMulEquiv e A B hAB) = μG)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
include hμ in
/-- **Square integrability transfers along `e`**: `ρ ∘ e` is square integrable modulo `B` for
`μH` iff `ρ` is square integrable modulo `A = e(B)` for `μG`, the image of `μH`. -/
theorem isSquareIntegrableModCentralSubgroup_comp_iff (ρ : Representation ℂ G V) :
    IsSquareIntegrableModCentralSubgroup B hB (ρ.comp e.toMonoidHom) μH ↔
      IsSquareIntegrableModCentralSubgroup A hA ρ μG := by
  have hφ := (quotientContinuousMulEquiv e A B hAB).toHomeomorph.measurableEmbedding
  have key : ∀ (c : UnitaryCentralCharacter ρ)
      (c' : UnitaryCentralCharacter (ρ.comp e.toMonoidHom)) (ℓ : Module.Dual ℂ V) (v : V),
      MemLp (centralSubgroupCoefficientNorm B hB c' ℓ v) 2 μH ↔
        MemLp (centralSubgroupCoefficientNorm A hA c ℓ v) 2 μG := by
    intro c c' ℓ v
    rw [centralSubgroupCoefficientNorm_pullback e A hA B hB hAB c c', ← hμ]
    exact (hφ.memLp_map_measure_iff).symm
  constructor
  · rintro ⟨hadm, c', hc'⟩
    refine ⟨(isAdmissible_comp_continuousMulEquiv_iff ρ e).mp hadm, UnitaryCentralCharacter.ofPullback e c', ?_⟩
    intro ℓ v
    refine (key (UnitaryCentralCharacter.ofPullback e c') c' ℓ v).mp ?_
    exact hc' ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mpr ℓ.property⟩
      v
  · rintro ⟨hadm, c, hc⟩
    refine ⟨(isAdmissible_comp_continuousMulEquiv_iff ρ e).mpr hadm, UnitaryCentralCharacter.pullback e c, ?_⟩
    intro ℓ v
    refine (key c (UnitaryCentralCharacter.pullback e c) ℓ v).mpr ?_
    exact hc ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mp ℓ.property⟩ v

include hμ in
/-- The pullback of a class is a discrete series modulo `B` iff the class is one modulo `A`. -/
theorem isDiscreteSeriesClass_pullback_iff (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    IsDiscreteSeriesClass B hB μH (SmoothDualClass.pullback e ω) ↔
      IsDiscreteSeriesClass A hA μG ω := by
  induction ω using Quotient.inductionOn with
  | h π => exact isSquareIntegrableModCentralSubgroup_comp_iff e A hA B hB hAB μG μH hμ _

/-- The pullback of a discrete-series class of `G` modulo `A`, a discrete-series class of `H`
modulo `B`. -/
def DiscreteSeriesClass.pullback (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    DiscreteSeriesClass.{uH, uV} B hB μH :=
  ⟨SmoothDualClass.pullback e ω.val,
    (isDiscreteSeriesClass_pullback_iff e A hA B hB hAB μG μH hμ ω.val).mpr ω.property⟩

/-- Pullback of discrete-series classes is injective. -/
theorem DiscreteSeriesClass.pullback_injective :
    Function.Injective (DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ) := by
  intro x y hxy
  exact Subtype.ext (SmoothDualClass.pullback_injective e (congrArg Subtype.val hxy))

end SquareIntegrable

section Orbits

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H] (e : H ≃ₜ* G)
  {I : Type uI} (νG : I → (G →* ℝ≥0ˣ)) (νH : I → (H →* ℝ≥0ˣ))
  (hν : ∀ i h, νG i (e h) = νH i h)

/-- **Pullback of unitary unramified characters** along `e`, when the defining characters
correspond (`νG i ∘ e = νH i`): `χ ↦ χ ∘ e`. -/
def unitaryUnramifiedPullback :
    unitaryUnramifiedCharacters νG →* unitaryUnramifiedCharacters νH where
  toFun χ := ⟨(χ.val : G →ₜ* ℂˣ).comp (e : H →ₜ* G),
    ⟨fun h hh => by
      have hh' : e h ∈ commonNormKernel νG := by
        rw [mem_commonNormKernel]
        intro i
        rw [hν i h]
        exact (mem_commonNormKernel νH h).mp hh i
      exact χ.property.1 hh',
    fun h => χ.property.2 (e h)⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NonarchimedeanGroup G] [NonarchimedeanGroup H] in
@[simp]
theorem unitaryUnramifiedPullback_apply (χ : unitaryUnramifiedCharacters νG) (h : H) :
    (unitaryUnramifiedPullback e νG νH hν χ).val h = χ.val (e h) :=
  rfl

include hν in
omit [NonarchimedeanGroup G] [NonarchimedeanGroup H] in
/-- The compatibility `νG i ∘ e = νH i` gives `νH i ∘ e⁻¹ = νG i`. -/
theorem norm_characters_symm_compat (i : I) (g : G) : νH i (e.symm g) = νG i g := by
  rw [← hν i (e.symm g), e.apply_symm_apply]

omit [NonarchimedeanGroup G] [NonarchimedeanGroup H] in
/-- Every unitary unramified character of `H` is the pullback of one of `G` (by `e⁻¹`). -/
theorem unitaryUnramifiedPullback_surjective :
    Function.Surjective (unitaryUnramifiedPullback e νG νH hν) := by
  intro ψ
  refine ⟨unitaryUnramifiedPullback e.symm νH νG (norm_characters_symm_compat e νG νH hν) ψ, ?_⟩
  apply Subtype.ext
  refine ContinuousMonoidHom.ext fun h => ?_
  change ψ.val (e.symm (e h)) = ψ.val h
  rw [e.symm_apply_apply]

variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
  (hAB : B.map e.toMulEquiv.toMonoidHom = A)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
  (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure] (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure]
  (hμ : μH.map (quotientContinuousMulEquiv e A B hAB) = μG)

/-- Pullback commutes with the action of the unitary unramified characters. -/
theorem DiscreteSeriesClass.pullback_smul (χ : unitaryUnramifiedCharacters νG)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ (χ • ω) =
      unitaryUnramifiedPullback e νG νH hν χ •
        DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ ω := by
  apply Subtype.ext
  exact SmoothDualClass.pullback_twist e _ _ _ ω.val

include hν in
/-- **Pullback of discrete-series orbits** along `e : H ≃ₜ* G`: the orbit of `ω ∘ e` under the
unitary unramified characters of `H`, for the orbit of `ω`. -/
def discreteSeriesOrbitPullback :
    DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μG νG →
      DiscreteSeriesOrbitClass.{uH, uI, uV} B hB μH νH :=
  Quotient.map (DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ) (by
    rintro a b ⟨χ, hχ⟩
    refine ⟨unitaryUnramifiedPullback e νG νH hν χ, ?_⟩
    show unitaryUnramifiedPullback e νG νH hν χ •
        DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ b =
      DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ a
    rw [← DiscreteSeriesClass.pullback_smul e νG νH hν A hA B hB hAB μG μH hμ]
    exact congrArg _ hχ)

@[simp]
theorem discreteSeriesOrbitPullback_mk (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    discreteSeriesOrbitPullback e νG νH hν A hA B hB hAB μG μH hμ (Quotient.mk _ ω) =
      Quotient.mk _ (DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ ω) :=
  rfl

/-- Pullback of orbits is injective. -/
theorem discreteSeriesOrbitPullback_injective :
    Function.Injective (discreteSeriesOrbitPullback e νG νH hν A hA B hB hAB μG μH hμ) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
  induction y using Quotient.inductionOn with
  | h b =>
  obtain ⟨ψ, hψ⟩ := Quotient.exact hxy
  obtain ⟨χ, rfl⟩ := unitaryUnramifiedPullback_surjective e νG νH hν ψ
  refine Quotient.sound ⟨χ, DiscreteSeriesClass.pullback_injective e A hA B hB hAB μG μH hμ ?_⟩
  rw [DiscreteSeriesClass.pullback_smul e νG νH hν A hA B hB hAB μG μH hμ]
  exact hψ

/-- `Θ^K_G` maps into `Θ^{e⁻¹(K)}_H`. -/
theorem discreteSeriesOrbitPullback_mem (K : Subgroup G) {x : DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μG νG}
    (hx : x ∈ discreteSeriesFixedOrbits A hA μG νG K) :
    discreteSeriesOrbitPullback e νG νH hν A hA B hB hAB μG μH hμ x ∈
      discreteSeriesFixedOrbits B hB μH νH (K.comap e.toMonoidHom) := by
  obtain ⟨ω, hω, rfl⟩ := hx
  refine ⟨DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ ω, ?_, rfl⟩
  change SmoothDualClass.HasFixedVector (K.comap e.toMonoidHom)
    (SmoothDualClass.pullback e ω.val)
  rw [SmoothDualClass.hasFixedVector_pullback]
  have hK : (K.comap e.toMonoidHom).comap e.symm.toMonoidHom = K := by
    ext g
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    change e (e.symm g) ∈ K ↔ g ∈ K
    rw [e.apply_symm_apply]
  rw [hK]
  exact hω

include hν hAB hμ in
/-- **Theorem VIII.1.2 transfers along topological group isomorphisms**: if `Θ^{e⁻¹(K)}_H` is
finite, so is `Θ^K_G`. -/
theorem finite_discreteSeriesFixedOrbits_of_pullback (K : Subgroup G)
    (hfin : (discreteSeriesFixedOrbits B hB μH νH (K.comap e.toMonoidHom) :
      Set (DiscreteSeriesOrbitClass.{uH, uI, uV} B hB μH νH)).Finite) :
    (discreteSeriesFixedOrbits A hA μG νG K :
      Set (DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μG νG)).Finite := by
  have hsub : discreteSeriesOrbitPullback e νG νH hν A hA B hB hAB μG μH hμ ''
      discreteSeriesFixedOrbits A hA μG νG K ⊆
        discreteSeriesFixedOrbits B hB μH νH (K.comap e.toMonoidHom) := by
    rintro _ ⟨x, hx, rfl⟩
    exact discreteSeriesOrbitPullback_mem e νG νH hν A hA B hB hAB μG μH hμ K hx
  exact Set.Finite.of_finite_image (hfin.subset hsub)
    (discreteSeriesOrbitPullback_injective e νG νH hν A hA B hB hAB μG μH hμ).injOn

end Orbits

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance rationalLeviOrbitIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance rationalLeviOrbitLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (I : Finset (RationalPointFamily.SimpleRoot i ν))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

-- The Levi group scheme `L` with `L(F) ≃ M_I(F)`.
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

/-- **`A_{M_I}(F)` inside `M_I(F)`**: the image of the rational points of a split component
`a : T → L` of the Levi scheme `L` under `L(F) ≃ₜ* M_I(F)` (`leviRationalPointHomeomorph`). -/
def rationalLeviSplitCenter {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : T.toGrp ⟶ 𝐋) : Subgroup 𝐌 :=
  (rationalPoints.map a).range.map
    (RationalPointFamily.leviRationalPointHomeomorph i ν I).toMulEquiv.toMonoidHom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The image of a split component is central in `M_I(F)`. -/
theorem rationalLeviSplitCenter_le_center {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : T.toGrp ⟶ 𝐋) (ha : IsSplitComponent a) :
    rationalLeviSplitCenter I a ≤ Subgroup.center 𝐌 := by
  rintro _ ⟨y, hy, rfl⟩
  exact (centerHomOfEquiv (RationalPointFamily.leviRationalPointHomeomorph i ν I)
    ⟨y, ha.isCentralSplitTorus.isCentral.range_le_center hy⟩).property

omit [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The Levi scheme `L` of `M_I(F)` has a split component (`standardLeviSplitComponentStatement`,
proved in the Library), so `rationalLeviSplitCenter I a` is available. -/
theorem exists_isSplitComponent_standardLevi (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (a : T.toGrp ⟶ 𝐋), IsSplitComponent a := by
  obtain ⟨-, T, a, -, ha, -⟩ := standardLeviSplitComponentStatement F G hG S i hi ν hν
    (RationalPointFamily.rootSet i ν I) (RationalPointFamily.rootSet_subset i ν I)
  exact ⟨T, a, ha⟩

/-- **Theorem VIII.1.2 for the actual Levi subgroup `M_I(F)`** from the published statement
`RationalDiscreteSeriesOrbitFinitenessStatement` (Waldspurger, printed p. 321, applied to the
Levi subgroups as in Remark VIII.1.3): for a split component `a` of the Levi scheme `L` (one
exists by `standardLeviSplitComponentStatement`), every Haar measure `μM` on
`M_I(F)/A_{M_I}(F)` and every compact open subgroup `L` of `M_I(F)`, the set `Θ^L_{M_I}` of
orbits of discrete series of `M_I(F)` modulo `A_{M_I}(F)` with a nonzero `L`-fixed vector is
finite. -/
theorem finite_discreteSeriesFixedOrbits_standardLevi
    (hVIII : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (a : T.toGrp ⟶ 𝐋) (ha : IsSplitComponent a)
    [(rationalLeviSplitCenter I a).Normal]
    [MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
    [BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I a)]
    (μM : Measure (𝐌 ⧸ rationalLeviSplitCenter I a)) [μM.IsHaarMeasure]
    (L : OpenSubgroup 𝐌) (hL : IsCompact (L : Set 𝐌)) :
    (discreteSeriesFixedOrbits (rationalLeviSplitCenter I a)
      (rationalLeviSplitCenter_le_center I a ha) μM
      (RationalPointFamily.leviRationalNormCharacters i ν I) L.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{u, u, uV} (rationalLeviSplitCenter I a)
          (rationalLeviSplitCenter_le_center I a ha) μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite := by
  have hLred := (standardLeviSplitComponentStatement F G hG S i hi ν hν
    (RationalPointFamily.rootSet i ν I) (RationalPointFamily.rootSet_subset i ν I)).1
  have : IsAffine 𝐋.X.left := isAffine_of_isAffineHom 𝐋.X.hom
  have : NonarchimedeanGroup (rationalPoints 𝐋) := rationalPoints_nonarchimedeanGroup 𝐋
  let e := RationalPointFamily.leviRationalPointHomeomorph i ν I
  let B := (rationalPoints.map a).range
  have : B.Normal := B.normal_of_le_center ha.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints 𝐋 ⧸ B) := borel _
  have : BorelSpace (rationalPoints 𝐋 ⧸ B) := ⟨rfl⟩
  have hAB : B.map e.toMulEquiv.toMonoidHom = rationalLeviSplitCenter I a := rfl
  let φ := quotientContinuousMulEquiv e (rationalLeviSplitCenter I a) B hAB
  let μH : Measure (rationalPoints 𝐋 ⧸ B) := μM.map φ.symm
  have hμ : μH.map φ = μM := MeasurableEquiv.map_map_symm φ.toHomeomorph.toMeasurableEquiv
  have hLo : IsOpen ((L.toSubgroup.comap e.toMonoidHom : Subgroup (rationalPoints 𝐋)) :
      Set (rationalPoints 𝐋)) := L.isOpen.preimage e.continuous
  have hLc : IsCompact ((L.toSubgroup.comap e.toMonoidHom : Subgroup (rationalPoints 𝐋)) :
      Set (rationalPoints 𝐋)) := e.toHomeomorph.isCompact_preimage.mpr hL
  have hfin := hVIII F 𝐋 hLred T a ha μH (L.toSubgroup.comap e.toMonoidHom) hLo hLc
  exact finite_discreteSeriesFixedOrbits_of_pullback e
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (fun psi => (rationalNormCharacters 𝐋 psi).toMul)
    (fun χ m => RationalPointFamily.leviRationalNormCharacters_apply_points i ν I χ m)
    (rationalLeviSplitCenter I a) (rationalLeviSplitCenter_le_center I a ha) B
    ha.isCentralSplitTorus.isCentral.range_le_center hAB μM μH hμ L.toSubgroup hfin

end Rational

end Langlands.HarishChandraSchwartz
