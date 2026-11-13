import Langlands.AlgebraicGeometry.SectionComponentOpennessProof
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk

/-! # A closed subscheme of a smooth scheme with fibres of full dimension along a section -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.ReducedBaseSmooth

open Langlands.AlgebraicGeometry

/-- A surjection from a domain onto a ring of the same finite Krull dimension is injective. -/
theorem injective_of_surjective_of_ringKrullDim_eq {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] (f : A →+* B) (hf : Function.Surjective f) (n : ℕ)
    (hA : ringKrullDim A = n) (hB : ringKrullDim B = n) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h1 := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero h) ha
  rw [hA, hB] at h1
  have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h1
  have h3 : n + 1 ≤ n := by exact_mod_cast h2
  omega

/-- Over a field, if a closed subscheme `X'` of a scheme `X` smooth of relative dimension `n`
is itself smooth of relative dimension `n`, then the connected component of `X` through the image
of a closed point of `X'` lies in `X'`. -/
theorem connectedComponent_subset_range_of_closedImmersion (k : Type u) [Field k]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    (j : X' ⟶ X) [IsClosedImmersion j] (n : ℕ) [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension n f'] (x' : X') (hx' : IsClosed ({x'} : Set X')) :
    connectedComponent (j x') ⊆ Set.range j := by
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    (Smooth.isDomain_and_isIntegrallyClosed_stalk f x).1
  have hjx : IsClosed ({j x'} : Set X) := by
    simpa [Set.image_singleton] using j.isClosedMap _ hx'
  have h1 : ringKrullDim (X.presheaf.stalk (j x')) = n :=
    fieldSmoothClosedPointStalkDimension k X f n inferInstance (j x') hjx
  have h2 : ringKrullDim (X'.presheaf.stalk x') = n :=
    fieldSmoothClosedPointStalkDimension k X' f' n inferInstance x' hx'
  have hinj := injective_of_surjective_of_ringKrullDim_eq (j.stalkMap x').hom
    (j.stalkMap_surjective x') n h1 h2
  have hiso : IsIso (j.stalkMap x') := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, j.stalkMap_surjective x'⟩
  have hgen : ∀ y : X, y ⤳ j x' → y ∈ Set.range j := by
    intro y hy
    have hy' : y ∈ Set.range (X.fromSpecStalk (j x')) := by
      rw [Scheme.range_fromSpecStalk]; exact hy
    obtain ⟨z, rfl⟩ := hy'
    obtain ⟨w, rfl⟩ := (Spec.map (j.stalkMap x')).surjective z
    refine ⟨X'.fromSpecStalk x' w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]
  obtain ⟨hopen, -⟩ := isOpen_irreducibleComponent_of_isDomain_stalk hdom (j x')
  have hclopen : IsClopen (irreducibleComponent (j x')) :=
    ⟨isClosed_irreducibleComponent, hopen⟩
  refine (hclopen.connectedComponent_subset mem_irreducibleComponent).trans ?_
  have hirr : IsIrreducible (irreducibleComponent (j x')) := isIrreducible_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [isClosed_irreducibleComponent.closure_eq] at hg
  exact (hg.mem_closed_set_iff j.isClosedEmbedding.isClosed_range).1
    (hgen _ (hg.specializes mem_irreducibleComponent))

section Fiber

variable {T Z Y : Scheme.{u}} (p : Z ⟶ T) (i : Y ⟶ Z)

/-- The morphism induced by `i` on residue fibres over `T`. -/
def fiberMap (t : T) : (i ≫ p).fiber t ⟶ p.fiber t :=
  pullback.map (i ≫ p) (T.fromSpecResidueField t) p (T.fromSpecResidueField t) i (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans (Category.id_comp _).symm)

@[reassoc (attr := simp)]
theorem fiberMap_fiberι (t : T) : fiberMap p i t ≫ p.fiberι t = (i ≫ p).fiberι t ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberMap_fiberToSpecResidueField (t : T) :
    fiberMap p i t ≫ p.fiberToSpecResidueField t = (i ≫ p).fiberToSpecResidueField t := by
  simp [fiberMap, Scheme.Hom.fiberToSpecResidueField]

instance [IsClosedImmersion i] (t : T) : IsClosedImmersion (fiberMap p i t) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl
    (Category.id_comp _).symm

variable (e : T ⟶ Y) (he : e ≫ i ≫ p = 𝟙 T)

include he in
theorem comp_section : (e ≫ i) ≫ p = 𝟙 T := by rw [Category.assoc, he]

theorem fiberSection_comp_fiberMap (t : T) :
    SectionComponent.fiberSection (i ≫ p) e he t ≫ fiberMap p i t =
      SectionComponent.fiberSection p (e ≫ i) (comp_section p i e he) t := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ fiberMap p i t ≫ p.fiberι t = _ ≫ p.fiberι t
    rw [fiberMap_fiberι, SectionComponent.fiberSection_fiberι_assoc,
      SectionComponent.fiberSection_fiberι]
  · rw [Category.assoc]
    change _ ≫ fiberMap p i t ≫ p.fiberToSpecResidueField t = _ ≫ p.fiberToSpecResidueField t
    rw [fiberMap_fiberToSpecResidueField, SectionComponent.fiberSection_toSpec,
      SectionComponent.fiberSection_toSpec]

theorem fiberMap_fiberPoint (t : T) :
    fiberMap p i t (SectionComponent.fiberPoint (i ≫ p) e he t) =
      SectionComponent.fiberPoint p (e ≫ i) (comp_section p i e he) t := by
  change (SectionComponent.fiberSection (i ≫ p) e he t ≫ fiberMap p i t) _ = _
  rw [fiberSection_comp_fiberMap]
  rfl

theorem isClosed_fiberPoint [LocallyOfFiniteType (i ≫ p)] (t : T) :
    IsClosed ({SectionComponent.fiberPoint (i ≫ p) e he t} : Set ((i ≫ p).fiber t)) := by
  have hcomp : SectionComponent.fiberSection (i ≫ p) e he t ≫
      (i ≫ p).fiberToSpecResidueField t = 𝟙 _ :=
    SectionComponent.fiberSection_toSpec _ _ _ _
  have : LocallyOfFiniteType (SectionComponent.fiberSection (i ≫ p) e he t ≫
      (i ≫ p).fiberToSpecResidueField t) := by
    rw [hcomp]; infer_instance
  have : LocallyOfFiniteType (SectionComponent.fiberSection (i ≫ p) e he t) :=
    locallyOfFiniteType_of_comp _ ((i ≫ p).fiberToSpecResidueField t)
  have hcl : (IsLocalRing.closedPoint (T.residueField t) : Spec (T.residueField t)) ∈
      closedPoints (Spec (T.residueField t)) :=
    IsLocalRing.isClosed_singleton_closedPoint _
  have := (SectionComponent.fiberSection (i ≫ p) e he t).closePoints_subset_preimage_closedPoints
    hcl
  rwa [Set.mem_preimage, mem_closedPoints_iff] at this

/-- Over each point, the component of the fibre of `p` through the section lies in the closed
subscheme. -/
theorem componentSet_subset_range [IsClosedImmersion i] (n : ℕ) [SmoothOfRelativeDimension n p]
    (hY : ∀ t, SmoothOfRelativeDimension n ((i ≫ p).fiberToSpecResidueField t)) :
    SectionComponent.componentSet p (e ≫ i) (comp_section p i e he) ⊆ Set.range i := by
  rintro _ ⟨t, z, hz, rfl⟩
  have : Smooth p := SmoothOfRelativeDimension.smooth n p
  have : SmoothOfRelativeDimension n ((i ≫ p).fiberToSpecResidueField t) := hY t
  have : SmoothOfRelativeDimension n (p.fiberToSpecResidueField t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _
      (inferInstanceAs (SmoothOfRelativeDimension n p))
  rw [← fiberMap_fiberPoint p i e he t] at hz
  obtain ⟨w, rfl⟩ := connectedComponent_subset_range_of_closedImmersion (T.residueField t)
    (p.fiberToSpecResidueField t) ((i ≫ p).fiberToSpecResidueField t) (fiberMap p i t) n
    _ (isClosed_fiberPoint p i e he t) hz
  refine ⟨(i ≫ p).fiberι t w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← fiberMap_fiberι, Scheme.Hom.comp_apply]

end Fiber

/-- **Core of the reduced-base argument.** Let `p : Z → T` be smooth of relative dimension `n`
over a reduced scheme, let `i : Y → Z` be a closed immersion and `e` a section of `i ≫ p`. If
every fibre of `i ≫ p` is smooth of relative dimension `n`, then `i ≫ p` is smooth on an open
neighbourhood of the section. -/
theorem exists_smooth_open_of_closedImmersion {T Z Y : Scheme.{u}} [IsReduced T] (p : Z ⟶ T)
    (n : ℕ) [SmoothOfRelativeDimension n p] [QuasiCompact p] [QuasiSeparated p]
    (i : Y ⟶ Z) [IsClosedImmersion i] (e : T ⟶ Y) (he : e ≫ i ≫ p = 𝟙 T)
    (hY : ∀ t, SmoothOfRelativeDimension n ((i ≫ p).fiberToSpecResidueField t)) :
    ∃ W : Y.Opens, Set.range e ⊆ W ∧ Smooth (W.ι ≫ i ≫ p) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth n p
  have hopen : IsOpen (SectionComponent.componentSet p (e ≫ i) (comp_section p i e he)) :=
    SectionComponent.flatFinitePresentationOpenness Z T p (e ≫ i) (comp_section p i e he)
      inferInstance inferInstance inferInstance inferInstance
      (smoothGeometricallyReduced Z T p inferInstance)
  let U0 : Z.Opens := ⟨_, hopen⟩
  have hU0 : (U0 : Set Z) ⊆ Set.range i := componentSet_subset_range p i e he n hY
  refine ⟨i ⁻¹ᵁ U0, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact SectionComponent.section_mem_componentSet p (e ≫ i) (comp_section p i e he) t
  · have : IsReduced U0 := SmoothReducedBase.isReduced_of_smooth_of_isReduced (U0.ι ≫ p)
    have : Surjective (i ∣_ U0) := by
      constructor
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := hU0 hz
      exact ⟨⟨y, show y ∈ i ⁻¹ᵁ U0 from hz⟩, Subtype.ext (morphismRestrict_base_coe i U0 _)⟩
    have : IsIso (i ∣_ U0) := isIso_of_isClosedImmersion_of_surjective _
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

end Langlands.GroupScheme.ReducedBaseSmooth
