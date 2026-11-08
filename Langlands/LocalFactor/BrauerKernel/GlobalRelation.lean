import Langlands.LocalFactor.BrauerKernel.GaloisType
import Langlands.Global.Factors.RelativeWeilBrauer

/-! # The global relation of a Galois type decomposition -/

noncomputable section

universe uF uV u

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation ClassField.Global ClassField.Global.RelativeWeilGroup

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {e : ReciprocityFamily F}
  {z : Presentation F (Correspondence.baseExtension F)}
  (D : GaloisTypeDecomposition F e z)
  (c : FundamentalClass.ClassFamily.{u}) (k K' : Type u) [Field k] [NumberField k] [Field K']
  [NumberField K'] [Algebra k K'] [IsGalois k K']
  (θ : (K' ≃ₐ[k] K') ≃* (D.K.field ≃ₐ[F.Carrier] D.K.field))

attribute [local instance] relativeGaloisTopology

/-- The subgroup of `Gal(K'/k)` corresponding under `θ` to the Galois image of the
generator field `L_g`. -/
def globalSubgroup (g : Generator F (Correspondence.baseExtension F)) :
    Subgroup (K' ≃ₐ[k] K') :=
  (@galoisImage p _ F D.K D.normal g.extension).comap θ.toMonoidHom

/-- The global intermediate field of a generator: the fixed field of `globalSubgroup`. -/
def globalField (g : Generator F (Correspondence.baseExtension F)) : IntermediateField k K' :=
  IntermediateField.fixedField (globalSubgroup D k K' θ g)

/-- The quotient map `W_{K'/k} → Gal(K'/k) ≃ Gal(K/F)`. -/
def globalQuotient : RelativeWeilGroup c k K' →* (D.K.field ≃ₐ[F.Carrier] D.K.field) :=
  θ.toMonoidHom.comp (projection c k K')

theorem isOpen_ker_globalQuotient :
    IsOpen ((globalQuotient D c k K' θ).ker : Set (RelativeWeilGroup c k K')) := by
  have hk : (globalQuotient D c k K' θ).ker =
      galoisPreimage c k K' ((⊥ : Subgroup (D.K.field ≃ₐ[F.Carrier] D.K.field)).comap
        θ.toMonoidHom) := by
    ext t
    rfl
  rw [hk]
  exact isOpen_galoisPreimage c k K' _

theorem globalQuotient_surjective : Function.Surjective (globalQuotient D c k K' θ) :=
  θ.surjective.comp (projection_surjective c k K')

/-- A character of the Galois image of `L_g`, read on the corresponding subgroup of
`Gal(K'/k)`. -/
def globalSubgroupCharacter (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ) :
    globalSubgroup D k K' θ g →* ℂˣ :=
  χ.comp ((θ.toMonoidHom.comp (globalSubgroup D k K' θ g).subtype).codRestrict _
    (fun σ => σ.2))

/-- The inflated character of `W_{K'/𝕃_g}`, for the global field `𝕃_g` of a generator. -/
def globalCharacter (h : FundamentalClass.Restriction c)
    (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ) :
    RelativeWeilGroup c (globalField D k K' θ g) K' →ₜ* ℂˣ :=
  (ClassField.Global.RelativeWeilGroup.galoisCharacter c k K' (globalSubgroup D k K' θ g)
      (globalSubgroupCharacter D k K' θ g χ)).comp
    (ExactGrothendieckGroup.codRestrictOfRange
      (restrictionInclusion c k K' (globalField D k K' θ g) h) _
      (range_restrictionInclusion_fixedField c k K' h (globalSubgroup D k K' θ g)))

/-- Inflating from `Gal(K/F)`, through `θ` and the projection, the induction of a character
of the Galois image of `L_g` gives the induction from `W_{H'}` of the inflated character,
where `H'` is the corresponding subgroup of `Gal(K'/k)`. -/
theorem inflate_induce_globalSubgroup (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ) :
    ExactGrothendieckGroup.inflate.{u, uF, max u uV} (globalQuotient D c k K' θ)
        (isOpen_ker_globalQuotient D c k K' θ)
        (FiniteRep.ofClass (FiniteRep.induce (@galoisImage p _ F D.K D.normal g.extension)
          (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
      ExactGrothendieckGroup.continuousInduce (galoisPreimage c k K' (globalSubgroup D k K' θ g))
        (isOpen_galoisPreimage c k K' _)
        (ExactGrothendieckGroup.characterClass.{u, max u uV}
          (ClassField.Global.RelativeWeilGroup.galoisCharacter c k K' (globalSubgroup D k K' θ g)
            (globalSubgroupCharacter D k K' θ g χ))) :=
  ExactGrothendieckGroup.inflate_ofClass_induce (globalQuotient D c k K' θ)
    (isOpen_ker_globalQuotient D c k K' θ) (globalQuotient_surjective D c k K' θ)
    (@galoisImage p _ F D.K D.normal g.extension)
    (galoisPreimage c k K' (globalSubgroup D k K' θ g)) (fun _ => Iff.rfl)
    (fun _ hA => FiniteRepresentation.isContinuous_induce _
      (isOpen_galoisPreimage c k K' _) hA)
    (FiniteRep.oneDimensional χ)
    (FiniteRepresentation.characterLine.{u, max u uV}
      (ClassField.Global.RelativeWeilGroup.galoisCharacter c k K' (globalSubgroup D k K' θ g)
        (globalSubgroupCharacter D k K' θ g χ)).toMonoidHom)
    (FiniteRepresentation.characterLine_isContinuous _)
    (ULift.moduleEquiv : ULift.{max u uV} ℂ ≃ₗ[ℂ] ℂ).symm (fun _ _ => rfl)

/-- Twisting the inflated induced class by a character `Ω` of `W_{K'/k}` gives induction
along `W_{K'/𝕃_g} → W_{K'/k}` of the line of `(Ω ∘ ι) · globalCharacter`. -/
theorem continuousTwist_inflate_induce (h : FundamentalClass.Restriction c)
    (g : Generator F (Correspondence.baseExtension F))
    (χ : @galoisImage p _ F D.K D.normal g.extension →* ℂˣ)
    (Ω : RelativeWeilGroup c k K' →ₜ* ℂˣ) :
    ExactGrothendieckGroup.continuousTwist Ω
        (ExactGrothendieckGroup.inflate.{u, uF, max u uV} (globalQuotient D c k K' θ)
          (isOpen_ker_globalQuotient D c k K' θ)
          (FiniteRep.ofClass (FiniteRep.induce (@galoisImage p _ F D.K D.normal g.extension)
            (FiniteRep.classOf (FiniteRep.oneDimensional χ))))) =
      ExactGrothendieckGroup.continuousInduceAlong
        (restrictionInclusion c k K' (globalField D k K' θ g) h)
        (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
        (ExactGrothendieckGroup.characterClass.{u, max u uV}
          (Ω.comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
            globalCharacter D c k K' θ h g χ)) := by
  rw [inflate_induce_globalSubgroup, ← ExactGrothendieckGroup.continuousInduce_continuousTwist,
    ExactGrothendieckGroup.continuousTwist_characterClass,
    ExactGrothendieckGroup.continuousInduce_characterClass_eq_along
      (restrictionInclusion c k K' (globalField D k K' θ g) h)
      (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
      (galoisPreimage c k K' (globalSubgroup D k K' θ g)) (isOpen_galoisPreimage c k K' _)
      (range_restrictionInclusion_fixedField c k K' h (globalSubgroup D k K' θ g))]
  congr 2

/-- **The global relation.** For every family `Ω` of continuous characters of `W_{K'/k}`
indexed by the types, the generators of the decomposition give an actual relation
`Σ_g z(g) Ind_{W_{K'/𝕃_g}} ([(Ω (t₁ g) ∘ ι) · Y₁ g] - [(Ω (t₂ g) ∘ ι) · Y₂ g]) = 0`
in the continuous exact virtual group of `W_{K'/k}`, where `Y_i g` is the inflated character
of `θ_i g`. -/
theorem globalRelation (h : FundamentalClass.Restriction c)
    (Ω : ℂ → (RelativeWeilGroup c k K' →ₜ* ℂˣ)) :
    ∑ g ∈ z.support, z g • ExactGrothendieckGroup.continuousInduceAlong
        (restrictionInclusion c k K' (globalField D k K' θ g) h)
        (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
        (ExactGrothendieckGroup.characterClass.{u, max u uV}
            ((Ω (D.t₁ g)).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
              globalCharacter D c k K' θ h g (D.θ₁ g)) -
          ExactGrothendieckGroup.characterClass.{u, max u uV}
            ((Ω (D.t₂ g)).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
              globalCharacter D c k K' θ h g (D.θ₂ g))) =
      (0 : ContinuousVirtual.{u, uV} c k K') := by
  classical
  let π := globalQuotient D c k K' θ
  have hπ := isOpen_ker_globalQuotient D c k K' θ
  let X : ℂ → Generator F (Correspondence.baseExtension F) → ContinuousVirtual.{u, uV} c k K' :=
    fun τ g => ExactGrothendieckGroup.continuousInduceAlong
      (restrictionInclusion c k K' (globalField D k K' θ g) h)
      (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
      (ExactGrothendieckGroup.characterClass.{u, max u uV}
        ((Ω τ).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
          globalCharacter D c k K' θ h g (D.θ₁ g)))
  let X' : ℂ → Generator F (Correspondence.baseExtension F) → ContinuousVirtual.{u, uV} c k K' :=
    fun τ g => ExactGrothendieckGroup.continuousInduceAlong
      (restrictionInclusion c k K' (globalField D k K' θ g) h)
      (isOpenEmbedding_restrictionInclusion c k K' (globalField D k K' θ g) h)
      (ExactGrothendieckGroup.characterClass.{u, max u uV}
        ((Ω τ).comp (restrictionInclusion c k K' (globalField D k K' θ g) h) *
          globalCharacter D c k K' θ h g (D.θ₂ g)))
  have hτ : ∀ τ : ℂ, ∑ g ∈ z.support, z g •
      ((if D.t₁ g = τ then X τ g else 0) - (if D.t₂ g = τ then X' τ g else 0)) = 0 := by
    intro τ
    have h0 := congrArg (fun y => ExactGrothendieckGroup.continuousTwist (Ω τ)
      (ExactGrothendieckGroup.inflate.{u, uF, max u uV} π hπ y)) (D.identity τ)
    simp only [map_zero] at h0
    refine Eq.trans ?_ h0
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, map_zsmul, map_sub, map_sub]
    congr 2
    · split_ifs
      · exact (continuousTwist_inflate_induce D c k K' θ h g (D.θ₁ g) (Ω τ)).symm
      · rw [map_zero, map_zero]
    · split_ifs
      · exact (continuousTwist_inflate_induce D c k K' θ h g (D.θ₂ g) (Ω τ)).symm
      · rw [map_zero, map_zero]
  let T : Finset ℂ := z.support.image D.t₁ ∪ z.support.image D.t₂
  have hsum := Finset.sum_eq_zero (s := T) fun τ _ => hτ τ
  rw [Finset.sum_comm] at hsum
  refine Eq.trans ?_ hsum
  refine Finset.sum_congr rfl fun g hg => ?_
  have h₁ : D.t₁ g ∈ T := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)
  have h₂ : D.t₂ g ∈ T := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [h₁, h₂, ↓reduceIte]
  rw [map_sub]

end Langlands.LocalFactor.NonabelianBrauer
