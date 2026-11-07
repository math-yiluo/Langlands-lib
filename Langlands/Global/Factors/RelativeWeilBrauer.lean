import Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationStatement
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement
import Langlands.VirtualRepresentation.FiniteInflation
import Langlands.Representation.Finite.DegreeZeroBrauerProof
import Langlands.Automorphic.AssociatedDeterminantTwistStatement

/-!
# Degree-zero Brauer decompositions on relative Weil groups

From Brauer induction for `W_{E/F}` (supplied as the hypothesis
`InducedCharacterGeneration`) and the finite degree-zero Brauer theorem for
`Gal(E/F)`, every continuous virtual representation `x` of `W_{E/F}` satisfies
`x - deg x · [1] ∈ span {Ind_{W_H} ([θ] - [θ'])}`. Twisting by a continuous
character `η` and rewriting the induction from `W_H` as induction along
`W_{E/K} → W_{E/F}` for the fixed field `K` of `H` gives a decomposition of
`η ⊗ x` whose shape does not depend on `η`.
-/

noncomputable section

set_option autoImplicit false

universe u uV uG uH uW

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction of a character line is the line of the composite character. -/
theorem continuousRestrict_characterClass (φ : H →ₜ* G) (η : G →ₜ* ℂˣ) :
    continuousRestrict.{uG, uH, uW} φ (characterClass.{uG, uW} η) =
      characterClass.{uH, uW} (η.comp φ) := by
  change restrict _ _ _ _ (ofRepresentation _ _) = _
  rw [restrict_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _ (Representation.Equiv.refl _)

variable [IsTopologicalGroup G]

/-- The corestriction of a continuous homomorphism to a subgroup containing its
range. -/
def codRestrictOfRange (φ : H →ₜ* G) (S : Subgroup G) (hS : φ.toMonoidHom.range = S) :
    H →ₜ* S where
  toMonoidHom := φ.toMonoidHom.codRestrict S (fun h => hS ▸ ⟨h, rfl⟩)
  continuous_toFun := φ.continuous.subtype_mk _

/-- Induction of a character line from a subgroup `S` equals induction along any
open embedding with range `S`, of the composite character. -/
theorem continuousInduce_characterClass_eq_along (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (S : Subgroup G) [S.FiniteIndex] (hSo : IsOpen (S : Set G))
    (hS : φ.toMonoidHom.range = S) (θ : S →ₜ* ℂˣ) :
    continuousInduce S hSo (characterClass.{uG, uW} θ) =
      continuousInduceAlong φ hφ
        (characterClass.{uH, uW} (θ.comp (codRestrictOfRange φ S hS))) := by
  subst hS
  rw [continuousInduceAlong, LinearMap.comp_apply, continuousRestrict_characterClass]
  congr 2
  ext s
  change (θ s : ℂ) =
    ((θ (⟨φ (InductionAlong.rangeInverse φ.toMonoidHom hφ.injective s), _⟩)) : ℂ)
  congr 2
  exact (Subtype.ext (InductionAlong.apply_rangeInverse φ.toMonoidHom hφ.injective s)).symm

/-- Twisting `Ind_S ([θ] - [θ'])` by `η` and rewriting the induction from `S` as
induction along an open embedding `φ` with range `S`. -/
theorem continuousTwist_continuousInduce_eq_along (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (S : Subgroup G) [S.FiniteIndex] (hSo : IsOpen (S : Set G))
    (hS : φ.toMonoidHom.range = S) (η : G →ₜ* ℂˣ) (θ θ' : S →ₜ* ℂˣ) :
    continuousTwist η (continuousInduce S hSo
        (characterClass.{uG, uW} θ - characterClass.{uG, uW} θ')) =
      continuousInduceAlong φ hφ
        (characterClass.{uH, uW} (η.comp φ * θ.comp (codRestrictOfRange φ S hS)) -
          characterClass.{uH, uW} (η.comp φ * θ'.comp (codRestrictOfRange φ S hS))) := by
  have hc : ∀ ϑ : S →ₜ* ℂˣ,
      (η.comp ⟨S.subtype, continuous_subtype_val⟩ * ϑ).comp (codRestrictOfRange φ S hS) =
        η.comp φ * ϑ.comp (codRestrictOfRange φ S hS) := fun _ => by
    ext
    rfl
  rw [← continuousInduce_continuousTwist, map_sub, continuousTwist_characterClass,
    continuousTwist_characterClass, map_sub,
    continuousInduce_characterClass_eq_along φ hφ S hSo hS,
    continuousInduce_characterClass_eq_along φ hφ S hSo hS, ← map_sub, hc, hc]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.VirtualRepresentation

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

attribute [local instance] relativeGaloisTopology

/-- The degree-zero generators `Ind_{W_H} ([θ] - [θ'])` of the continuous virtual
group of `W_{E/F}`, for subgroups `H` of `Gal(E/F)` and continuous characters
`θ`, `θ'` of the inverse image `W_H`. -/
def characterDifferenceGenerators : Set (ContinuousVirtual.{u, uV} c F E) :=
  {x | ∃ (H : Subgroup (E ≃ₐ[F] E)) (θ θ' : galoisPreimage c F E H →ₜ* ℂˣ),
    x = ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E H)
      (isOpen_galoisPreimage c F E H)
      (ExactGrothendieckGroup.characterClass.{u, max u uV} θ -
        ExactGrothendieckGroup.characterClass.{u, max u uV} θ')}

/-- A character of a subgroup `S` of `Gal(E/F)`, inflated to the inverse image
`W_S`. -/
def galoisCharacter (S : Subgroup (E ≃ₐ[F] E)) (χ : S →* ℂˣ) :
    galoisPreimage c F E S →ₜ* ℂˣ where
  toMonoidHom := χ.comp ((projection c F E).subgroupComap S)
  continuous_toFun := by
    have h : Continuous ((projection c F E).subgroupComap S) :=
      ((continuousProjection c F E).continuous.comp continuous_subtype_val).subtype_mk _
    exact (continuous_of_discreteTopology (f := χ)).comp h

/-- Inflating from `Gal(E/F)` the induction of a character of `S` gives the
induction from `W_S` of the inflated character. -/
theorem inflate_induce_oneDimensional (S : Subgroup (E ≃ₐ[F] E)) (χ : S →* ℂˣ) :
    ExactGrothendieckGroup.inflate.{u, u, max u uV} (projection c F E)
        (isOpen_ker_projection c F E)
        (FiniteRep.ofClass (FiniteRep.induceHom S
          (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
      ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E S)
        (isOpen_galoisPreimage c F E S)
        (ExactGrothendieckGroup.characterClass.{u, max u uV} (galoisCharacter c F E S χ)) :=
  ExactGrothendieckGroup.inflate_ofClass_induce (projection c F E)
    (isOpen_ker_projection c F E) (projection_surjective c F E) S
    (galoisPreimage c F E S) (fun _ => Iff.rfl)
    (fun _ hA => FiniteRepresentation.isContinuous_induce _
      (isOpen_galoisPreimage c F E S) hA)
    (FiniteRep.oneDimensional χ)
    (FiniteRepresentation.characterLine.{u, max u uV}
      (galoisCharacter c F E S χ).toMonoidHom)
    (FiniteRepresentation.characterLine_isContinuous _)
    (ULift.moduleEquiv : ULift.{max u uV} ℂ ≃ₗ[ℂ] ℂ).symm (fun _ _ => rfl)

/-- Inflating the trivial character of `Gal(E/F)` gives the trivial character line. -/
theorem inflate_one :
    ExactGrothendieckGroup.inflate.{u, u, max u uV} (projection c F E)
        (isOpen_ker_projection c F E)
        (FiniteRep.ofClass (FiniteRep.classOf
          (FiniteRep.oneDimensional (1 : (E ≃ₐ[F] E) →* ℂˣ)))) =
      ExactGrothendieckGroup.characterClass.{u, max u uV}
        (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) := by
  rw [ExactGrothendieckGroup.inflate_ofClass, ExactGrothendieckGroup.inflateClass_classOf]
  apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact (FiniteRepresentation.inflateEquiv (projection c F E) _
    (Representation.Equiv.mk
      ((ULift.moduleEquiv : ULift.{max u uV} ℂ ≃ₗ[ℂ] ℂ).symm)
      (fun _ => LinearMap.ext fun _ => rfl) :
      Representation.Equiv (FiniteRep.oneDimensional (1 : (E ≃ₐ[F] E) →* ℂˣ)).ρ
        (FiniteRepresentation.characterLine.{u, max u uV}
          (1 : (E ≃ₐ[F] E) →* ℂˣ)).representation)).trans
    (Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => LinearMap.ext fun _ => rfl))

/-- `Ind_{W_H} [1] - [Gal(E/F) : H] · [1]` lies in the span of the degree-zero
generators: inflation of the finite degree-zero Brauer theorem for `Gal(E/F)`. -/
theorem induce_one_sub_mem_span (H : Subgroup (E ≃ₐ[F] E)) :
    ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E H)
        (isOpen_galoisPreimage c F E H)
        (ExactGrothendieckGroup.characterClass.{u, max u uV}
          (1 : galoisPreimage c F E H →ₜ* ℂˣ)) -
      ((galoisPreimage c F E H).index : ℤ) •
        ExactGrothendieckGroup.characterClass.{u, max u uV}
          (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (characterDifferenceGenerators.{u, uV} c F E) := by
  classical
  let Q := E ≃ₐ[F] E
  let : Fintype Q := Fintype.ofFinite Q
  let Φ := ExactGrothendieckGroup.inflate.{u, u, max u uV} (projection c F E)
    (isOpen_ker_projection c F E)
  let one : FiniteRep.VirtualRep ℂ Q :=
    FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional (1 : Q →* ℂˣ)))
  let x : FiniteRep.VirtualRep ℂ Q :=
    FiniteRep.ofClass (FiniteRep.induceHom H
      (FiniteRep.classOf (FiniteRep.oneDimensional (1 : H →* ℂˣ)))) -
      (H.index : ℤ) • one
  have hx : FiniteRep.virtualCharacter (k := ℂ) (G := Q) x 1 = 0 := by
    have h1 : FiniteRep.ofClass (FiniteRep.induceHom H
        (FiniteRep.classOf (FiniteRep.oneDimensional (1 : H →* ℂˣ)))) =
        FiniteRep.virtualInduce H
          (FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional (1 : H →* ℂˣ)))) :=
      (FiniteRep.virtualMap_ofClass _ _).symm
    simp only [x, one, h1, map_sub, map_zsmul, Pi.sub_apply, Pi.smul_apply,
      FiniteRep.DegreeZeroBrauer.virtualCharacter_induce,
      FiniteRep.DegreeZeroBrauer.ind_at_one, FiniteRep.virtualCharacter_ofClass,
      FiniteRep.character_classOf, FiniteRep.character_oneDimensional,
      MonoidHom.one_apply, Units.val_one, mul_one]
    have hcard : (Nat.card Q : ℂ) = (H.index : ℂ) * (Nat.card H : ℂ) := by
      exact_mod_cast H.index_mul_card.symm
    have hpos : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [zsmul_eq_mul, mul_one, Int.cast_natCast, hcard]
    field_simp
    ring
  have hxmem : x ∈ FiniteRep.degreeZeroBrauerSpan Q := by
    rw [FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer Q]
    exact hx
  have hgal1 : galoisCharacter c F E H 1 = 1 := by
    ext
    rfl
  have hΦx : Φ x = ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E H)
        (isOpen_galoisPreimage c F E H)
        (ExactGrothendieckGroup.characterClass.{u, max u uV}
          (1 : galoisPreimage c F E H →ₜ* ℂˣ)) -
      ((galoisPreimage c F E H).index : ℤ) •
        ExactGrothendieckGroup.characterClass.{u, max u uV}
          (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) := by
    simp only [Φ, x, one, map_sub, map_zsmul]
    rw [inflate_induce_oneDimensional, inflate_one, hgal1,
      Subgroup.index_comap_of_surjective H (projection_surjective c F E)]
  rw [← hΦx]
  have hmap : Submodule.map Φ (FiniteRep.degreeZeroBrauerSpan Q) ≤
      Submodule.span ℤ (characterDifferenceGenerators.{u, uV} c F E) := by
    rw [FiniteRep.degreeZeroBrauerSpan, Submodule.map_span_le]
    rintro _ ⟨S, χ, χ', rfl⟩
    rw [FiniteRep.virtualInduce, map_sub, FiniteRep.virtualMap_ofClass,
      FiniteRep.virtualMap_ofClass, map_sub, inflate_induce_oneDimensional,
      inflate_induce_oneDimensional, ← map_sub]
    exact Submodule.subset_span ⟨S, _, _, rfl⟩
  exact hmap (Submodule.mem_map_of_mem hxmem)

/-- Global degree-zero Brauer: given Brauer induction for `W_{E/F}`, every
continuous virtual representation `x` satisfies
`x - deg x · [1] ∈ span {Ind_{W_H} ([θ] - [θ'])}`. -/
theorem sub_degree_smul_mem_span (hgen : InducedCharacterGeneration.{u, uV} c F E)
    (x : ContinuousVirtual.{u, uV} c F E) :
    x - ExactGrothendieckGroup.degree _ x •
        ExactGrothendieckGroup.characterClass.{u, max u uV}
          (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (characterDifferenceGenerators.{u, uV} c F E) := by
  have hx : x ∈ Submodule.span ℤ (inducedCharacterGenerators.{u, uV} c F E) := by
    rw [hgen]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨H, θ, rfl⟩ := hy
    rw [ExactGrothendieckGroup.continuousInduce, ExactGrothendieckGroup.degree_induce,
      ExactGrothendieckGroup.degree_characterClass, mul_one]
    have key : ExactGrothendieckGroup.induce (galoisPreimage c F E H) _ _
          (fun _ hA => FiniteRepresentation.isContinuous_induce _
            (isOpen_galoisPreimage c F E H) hA)
          (ExactGrothendieckGroup.characterClass.{u, max u uV} θ) -
        ((galoisPreimage c F E H).index : ℤ) •
          ExactGrothendieckGroup.characterClass.{u, max u uV}
            (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) =
        ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E H)
            (isOpen_galoisPreimage c F E H)
            (ExactGrothendieckGroup.characterClass.{u, max u uV} θ -
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (1 : galoisPreimage c F E H →ₜ* ℂˣ)) +
          (ExactGrothendieckGroup.continuousInduce (galoisPreimage c F E H)
              (isOpen_galoisPreimage c F E H)
              (ExactGrothendieckGroup.characterClass.{u, max u uV}
                (1 : galoisPreimage c F E H →ₜ* ℂˣ)) -
            ((galoisPreimage c F E H).index : ℤ) •
              ExactGrothendieckGroup.characterClass.{u, max u uV}
                (1 : RelativeWeilGroup c F E →ₜ* ℂˣ)) := by
      rw [map_sub]
      change _ = ExactGrothendieckGroup.continuousInduce _ _ _ -
        ExactGrothendieckGroup.continuousInduce _ _ _ + _
      unfold ExactGrothendieckGroup.continuousInduce
      abel
    rw [key]
    exact add_mem (Submodule.subset_span ⟨H, θ, 1, rfl⟩) (induce_one_sub_mem_span c F E H)
  | zero =>
    simp
  | add y z _ _ hy hz =>
    rw [map_add, add_smul]
    convert add_mem hy hz using 1
    abel
  | smul a y _ hy =>
    rw [map_zsmul, smul_eq_mul, mul_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hy

section Reciprocity

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

/-- The character `χ ∘ τ_F` of `W_{E/F}` for a continuous character `χ` of `C_F`,
as a continuous character: on the open subgroup `C_E` it is
`a ↦ χ(N_{E/F} a)⁻¹`, which is continuous. -/
def continuousReciprocityCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    RelativeWeilGroup c F E →ₜ* ℂˣ where
  toMonoidHom := reciprocityCharacter c F E χ
  continuous_toFun := by
    refine continuous_of_continuousAt_one (reciprocityCharacter c F E χ) ?_
    rw [← map_one (inclusion c F E), ← (isOpenEmbedding_inclusion c F E).continuousAt_iff]
    have hfun : (reciprocityCharacter c F E χ) ∘ (inclusion c F E) =
        fun a => (χ (ideleClassNorm (K := F) (L := E) a))⁻¹ := by
      funext a
      simp only [Function.comp_apply, reciprocityCharacter_apply, transfer_inclusion]
    rw [hfun]
    exact ((χ.continuous.comp (continuous_ideleClassNorm (K := F) (L := E))).inv).continuousAt

@[simp]
theorem continuousReciprocityCharacter_toMonoidHom (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    (continuousReciprocityCharacter c F E χ).toMonoidHom = reciprocityCharacter c F E χ :=
  rfl

end Reciprocity

section FixedField

omit [NumberField F] [NumberField E] [IsGalois F E] in
/-- The image of `Gal(E/K)` in `Gal(E/F)` is the fixing subgroup of `K`. -/
theorem range_restrictScalarsHom (K : IntermediateField F E) :
    (AlgEquiv.restrictScalarsHom F : (E ≃ₐ[K] E) →* (E ≃ₐ[F] E)).range =
      K.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩ y
    exact τ.commutes ⟨y.1, y.2⟩
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

variable (h : FundamentalClass.Restriction c)

/-- The image of `W_{E/K}` for the fixed field `K` of `H` is the inverse image
`W_H`. -/
theorem range_restrictionInclusion_fixedField (H : Subgroup (E ≃ₐ[F] E)) :
    (restrictionInclusion c F E (IntermediateField.fixedField H) h).toMonoidHom.range =
      galoisPreimage c F E H := by
  rw [range_restrictionInclusion, range_restrictScalarsHom,
    IntermediateField.fixingSubgroup_fixedField]

/-- The twisted degree-zero decomposition: given Brauer induction for `W_{E/F}`,
every continuous virtual representation `x` of `W_{E/F}` has finitely many
intermediate fields `K i`, integers `r i` and pairs of continuous characters
`θ i`, `θ' i` of `W_{E/K i}` such that, for every continuous character `η`,
`η ⊗ x = deg x · [η] + Σ r i · Ind_{W_{E/K i}} ([η θ i] - [η θ' i])`, with `η`
restricted to `W_{E/K i}`. The data do not depend on `η`. -/
theorem exists_twist_decomposition (hgen : InducedCharacterGeneration.{u, uV} c F E)
    (x : ContinuousVirtual.{u, uV} c F E) :
    ∃ (n : ℕ) (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
      (θ θ' : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ),
      ∀ η : RelativeWeilGroup c F E →ₜ* ℂˣ,
        ExactGrothendieckGroup.continuousTwist η x =
          ExactGrothendieckGroup.degree _ x •
              ExactGrothendieckGroup.characterClass.{u, max u uV} η +
            ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
              (restrictionInclusion c F E (K i) h)
              (isOpenEmbedding_restrictionInclusion c F E (K i) h)
              (ExactGrothendieckGroup.characterClass.{u, max u uV}
                  (η.comp (restrictionInclusion c F E (K i) h) * θ i) -
                ExactGrothendieckGroup.characterClass.{u, max u uV}
                  (η.comp (restrictionInclusion c F E (K i) h) * θ' i)) := by
  classical
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp (sub_degree_smul_mem_span c F E hgen x)
  choose H θ₀ θ₀' hg using fun i => (g i).2
  refine ⟨n, f, fun i => IntermediateField.fixedField (H i),
    fun i => (θ₀ i).comp (ExactGrothendieckGroup.codRestrictOfRange _ _
      (range_restrictionInclusion_fixedField c F E h (H i))),
    fun i => (θ₀' i).comp (ExactGrothendieckGroup.codRestrictOfRange _ _
      (range_restrictionInclusion_fixedField c F E h (H i))), fun η => ?_⟩
  have hx : x = ExactGrothendieckGroup.degree _ x •
      ExactGrothendieckGroup.characterClass.{u, max u uV}
        (1 : RelativeWeilGroup c F E →ₜ* ℂˣ) +
      ∑ i, f i • (g i : ContinuousVirtual.{u, uV} c F E) := by
    rw [hfg]
    abel
  conv_lhs => rw [hx]
  have hη : η * 1 = η := by
    ext
    simp
  rw [map_add, map_zsmul, ExactGrothendieckGroup.continuousTwist_characterClass, hη, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hg i,
    ExactGrothendieckGroup.continuousTwist_continuousInduce_eq_along
      (restrictionInclusion c F E (IntermediateField.fixedField (H i)) h)
      (isOpenEmbedding_restrictionInclusion c F E (IntermediateField.fixedField (H i)) h)
      (galoisPreimage c F E (H i)) (isOpen_galoisPreimage c F E (H i))
      (range_restrictionInclusion_fixedField c F E h (H i))]

end FixedField



section Local

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

variable (h : FundamentalClass.Restriction c)

/-- Restriction of a twisted decomposition to a local Weil group: if the local
restriction formula holds at `z` for the local map `ιd` and each intermediate
field `K i`, the restriction along `ιd` of
`d · [η] + Σ r i · Ind_{W_{E/K i}} ([α i] - [β i])` is
`d · [η ∘ ιd] + Σ r i · Σ_{u | z} Ind_{W_{K_u}}^{W_{F_z}} ([α i ∘ ιu] - [β i ∘ ιu])`,
for local maps `ιu` whose transfer is inverse geometric local reciprocity. -/
theorem exists_continuousRestrict_decomposition {z : Langlands.Global.FinitePlace F}
    (ιd : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    {n : ℕ} (K : Fin n → IntermediateField F E)
    (hloc : ∀ i, LocalInducedRestriction.{max u uV, u} c F (K i) E h z ιd) :
    ∃ ιu : ∀ (i : Fin n) (u : FinitePlacesAbove (K i) z),
        Weil.Local.localWeilGroup (towerPadicField z u.1) →ₜ* RelativeWeilGroup c (K i) E,
      (∀ (i : Fin n) (u : FinitePlacesAbove (K i) z)
          (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z u.1)),
        LocalClassField.GeometricWeilReciprocityRelation (towerPadicField z u.1)
            (towerPadicField z u.1).canonicalTopologicalData eu →
          ∀ y : Weil.Local.localWeilGroup (towerPadicField z u.1),
            transfer c (K i) E (ιu i u y) =
              (IdeleClassGroup.ofAdicCompletion (𝓞 (K i)) (K i) u.1
                (LocalFactor.RankOne.reciprocityUnits (towerPadicField z u.1) eu y))⁻¹) ∧
      ∀ (d : ℤ) (r : Fin n → ℤ) (η : RelativeWeilGroup c F E →ₜ* ℂˣ)
        (α β : ∀ i, RelativeWeilGroup c (K i) E →ₜ* ℂˣ),
        ExactGrothendieckGroup.continuousRestrict ιd
            (d • ExactGrothendieckGroup.characterClass.{u, max u uV} η +
              ∑ i, r i • ExactGrothendieckGroup.continuousInduceAlong
                (restrictionInclusion c F E (K i) h)
                (isOpenEmbedding_restrictionInclusion c F E (K i) h)
                (ExactGrothendieckGroup.characterClass.{u, max u uV} (α i) -
                  ExactGrothendieckGroup.characterClass.{u, max u uV} (β i))) =
          d • ExactGrothendieckGroup.characterClass.{u, max u uV} (η.comp ιd) +
            ∑ i, r i • ∑ u : FinitePlacesAbove (K i) z,
              ExactGrothendieckGroup.continuousInduceAlong (completionWeilMap z u.1)
                (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
                (ExactGrothendieckGroup.characterClass.{u, max u uV} ((α i).comp (ιu i u)) -
                  ExactGrothendieckGroup.characterClass.{u, max u uV} ((β i).comp (ιu i u))) := by
  choose ιu hτ hres using hloc
  refine ⟨ιu, hτ, fun d r η α β => ?_⟩
  rw [map_add, map_zsmul, ExactGrothendieckGroup.continuousRestrict_characterClass, map_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul, hres i]
  refine congrArg (r i • ·) (Finset.sum_congr rfl fun u _ => ?_)
  simp only [map_sub, ExactGrothendieckGroup.continuousRestrict_characterClass]

end Local

end Langlands.ClassField.Global.RelativeWeilGroup
