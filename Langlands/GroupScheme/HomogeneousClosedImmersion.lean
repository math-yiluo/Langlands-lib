import Langlands.GroupScheme.SchemeActionOrbit
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Closed equivariant embeddings of homogeneous reduced schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousClosedImmersion

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X Y : Over (Spec (CommRingCat.of k))}

/-- The reduced closed subscheme on the topological image of a morphism with
closed image, with its structure over the base field. -/
abbrev reducedClosedImage (f : X ⟶ Y) (hclosed : IsClosed (Set.range f.left)) :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal
    (⟨Set.range f.left, hclosed⟩ : Closeds Y.left)).subschemeι ≫ Y.hom)

/-- The canonical inclusion of the reduced closed image into the target. -/
abbrev reducedClosedImageι (f : X ⟶ Y) (hclosed : IsClosed (Set.range f.left)) :
    reducedClosedImage f hclosed ⟶ Y :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal
    (⟨Set.range f.left, hclosed⟩ : Closeds Y.left)).subschemeι

/-- A rational point in a finite-type morphism's topological image has an actual
rational lift over an algebraically closed field. -/
theorem exists_rational_lift [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (hy : y.left (IsLocalRing.closedPoint k) ∈ Set.range f.left) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, x ≫ f = y := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hybase : y.left ≫ Y.hom = 𝟙 _ := by simp
  have hyclosed : IsClosed ({y.left (IsLocalRing.closedPoint k)} : Set Y.left) :=
    ((pointEquivClosedPoint Y.hom) ⟨y.left, hybase⟩).property
  obtain ⟨z, hz⟩ := hy
  have hne : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint k)}).Nonempty := ⟨z, hz⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
    (hyclosed.preimage f.left.continuous).isLocallyClosed
  change IsClosed ({z} : Set X.left) at hzc
  let x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom z hzc) (pointOfClosedPoint_comp X.hom z hzc)
  refine ⟨x, Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq Y.hom
    (Over.w (x ≫ f)) hybase
  change (pointOfClosedPoint X.hom z hzc ≫ f.left) (IsLocalRing.closedPoint k) = _
  exact (congrArg f.left (pointOfClosedPoint_apply X.hom z hzc
    (IsLocalRing.closedPoint k))).trans hz

section Equivariance

variable {H : GroupScheme (Spec (CommRingCat.of k))}
variable (a : SchemeAction H X) (b : SchemeAction H Y) (f : X ⟶ Y)
variable (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X) (x : T ⟶ X),
  a.act g x ≫ f = b.act g (x ≫ f))

include hf

omit [IsAlgClosed k] in
/-- Equivariance identifies the square of actual rational translations. -/
theorem translation_comp (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    a.translation g ≫ f = f ≫ b.translation g := by
  rw [SchemeAction.translation, hf, b.comp_translation]
  simp only [Category.id_comp]

variable [IsReduced X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
variable [LocallyOfFiniteType Y.hom] [Mono f.left]

/-- A reduced homogeneous scheme embedded equivariantly as a closed topological
subset of a finite-type scheme is actually a closed subscheme. -/
theorem isClosedImmersion_of_closed_range
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (htrans : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X, a.act g x = y)
    (hclosed : IsClosed (Set.range f.left)) : IsClosedImmersion f.left := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Set.range f.left, hclosed⟩ : Closeds Y.left)
  let O := reducedClosedImage f hclosed
  let i : O ⟶ Y := reducedClosedImageι f hclosed
  have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hred : IsReduced O.left :=
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).1
  let := hi
  let := hred
  have hrange : Set.range i.left = Set.range f.left := by
    change Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk]
  have hker : I.subschemeι.ker ≤ f.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2
      f.left Set.Subset.rfl
  let c : X ⟶ O := Over.homMk (IsClosedImmersion.lift I.subschemeι f.left hker) (by
    change IsClosedImmersion.lift I.subschemeι f.left hker ≫ (I.subschemeι ≫ Y.hom) = _
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
    exact Over.w f)
  have hc : c ≫ i = f := Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  have hcmono : Mono c.left := by
    have : Mono (c.left ≫ i.left) := by
      change Mono (c ≫ i).left
      rw [hc]
      infer_instance
    exact mono_of_mono c.left i.left
  have hcsurj : Surjective c.left := by
    constructor
    intro o
    obtain ⟨z, hz⟩ := hrange.subset ⟨o, rfl⟩
    refine ⟨z, i.left.isClosedEmbedding.injective ?_⟩
    change (c ≫ i).left z = i.left o
    rw [hc]
    exact hz
  let := hcmono
  let := hcsurj
  have hOft : LocallyOfFiniteType O.hom := by
    change LocallyOfFiniteType (I.subschemeι ≫ Y.hom)
    infer_instance
  let := hOft
  have hOnoeth : IsLocallyNoetherian O.left := LocallyOfFiniteType.isLocallyNoetherian O.hom
  let := hOnoeth
  have : QuasiSeparated O.hom := inferInstance
  have hcft : LocallyOfFiniteType c.left := by
    have : LocallyOfFiniteType (c.left ≫ O.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp c.left O.hom
  have hcqc : QuasiCompact c.left := by
    have : QuasiCompact (c.left ≫ O.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp c.left O.hom
  let := hcft
  let := hcqc
  -- Each ambient translation restricts to the reduced closed image.
  have ht_range (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
      Set.range (i ≫ b.translation g).left ⊆ Set.range f.left := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨z, hz⟩ := hrange.subset ⟨o, rfl⟩
    refine ⟨(a.translation g).left z, ?_⟩
    have he := congrArg (fun q : X ⟶ Y => q.left z) (translation_comp a b f hf g)
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hz] using he
  have ht_ker (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
      I.subschemeι.ker ≤ (i ≫ b.translation g).left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2
      _ (ht_range g)
  let t (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) : O ⟶ O :=
    Over.homMk (IsClosedImmersion.lift I.subschemeι (i ≫ b.translation g).left (ht_ker g))
      (by
        change IsClosedImmersion.lift I.subschemeι _ _ ≫ (I.subschemeι ≫ Y.hom) = _
        rw [← Category.assoc, IsClosedImmersion.lift_fac]
        exact Over.w (i ≫ b.translation g))
  have ht (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
      t g ≫ i = i ≫ b.translation g :=
    Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  have ht_iso (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) : IsIso (t g) := by
    refine ⟨⟨t g⁻¹, ?_, ?_⟩⟩ <;> apply (cancel_mono i).mp
    · rw [Category.assoc, ht, ← Category.assoc, ht, Category.assoc]
      change i ≫ (b.translationIso g).hom ≫ (b.translationIso g).inv = _
      simp
    · rw [Category.assoc, ht, ← Category.assoc, ht, Category.assoc]
      change i ≫ (b.translationIso g).inv ≫ (b.translationIso g).hom = _
      simp
  have ht_comm (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
      a.translation g ≫ c = c ≫ t g := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hc, Category.assoc, ht, ← Category.assoc, hc]
    exact translation_comp a b f hf g
  have hrat : ∀ o : O.left, IsClosed ({o} : Set O.left) →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X,
        (a.act g x ≫ c).left (IsLocalRing.closedPoint k) = o := by
    intro o hoc
    let y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O :=
      Over.homMk (pointOfClosedPoint O.hom o hoc) (pointOfClosedPoint_comp O.hom o hoc)
    obtain ⟨z, hz⟩ := exists_rational_lift c y (c.left.surjective (y.left (IsLocalRing.closedPoint k)))
    obtain ⟨g, hg⟩ := htrans z
    refine ⟨g, ?_⟩
    rw [hg, hz]
    exact pointOfClosedPoint_apply O.hom o hoc _
  obtain ⟨U, hUne, hU⟩ := OrbitMapFlat.exists_open_flatNear c.left
    ((x ≫ c).left (IsLocalRing.closedPoint k))
  have : JacobsonSpace O.left := LocallyOfFiniteType.jacobsonSpace O.hom
  have hcover : ∀ o : O.left,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X, (t g).left o ∈ U := by
    by_contra! hne
    obtain ⟨o, ho⟩ := hne
    let Z : Set O.left := ⋂ g, (t g).left ⁻¹' (U : Set O.left)ᶜ
    have hZ : IsClosed Z := isClosed_iInter fun g =>
      U.isOpen.isClosed_compl.preimage (t g).left.continuous
    obtain ⟨d, hdZ, hd⟩ := nonempty_inter_closedPoints
      ⟨o, Set.mem_iInter.mpr ho⟩ hZ.isLocallyClosed
    obtain ⟨u, huU, hu⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
    obtain ⟨g₁, hg₁⟩ := hrat d hd
    obtain ⟨g₂, hg₂⟩ := hrat u hu
    have hmove : (a.act g₁ x ≫ c) ≫ t (g₂ * g₁⁻¹) = a.act g₂ x ≫ c := by
      rw [Category.assoc, ← ht_comm, ← Category.assoc, a.comp_translation]
      have hunit : toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ :=
        toUnit_unique _ _
      rw [hunit, Category.id_comp, ← a.act_mul, mul_assoc, inv_mul_cancel, mul_one]
    have he := congrArg (fun q : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O =>
      q.left (IsLocalRing.closedPoint k)) hmove
    have hdu : (t (g₂ * g₁⁻¹)).left d = u := by
      rw [← hg₁, ← hg₂, ← he]
      rfl
    exact Set.mem_iInter.mp hdZ (g₂ * g₁⁻¹) (by rw [hdu]; exact huU)
  have hcflat : Flat c.left := by
    apply OrbitMapFlat.flat_of_forall_flatNear
    intro z
    obtain ⟨g, hg⟩ := hcover (c.left z)
    have he : (a.translation g).left ≫ c.left = c.left ≫ (t g).left :=
      congrArg (fun q : X ⟶ O => q.left) (ht_comm g)
    let : IsIso (a.translation g).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (a.translationIso g).hom))
    let : IsIso (t g) := ht_iso g
    let : IsIso (t g).left := inferInstanceAs (IsIso ((Over.forget _).map (t g)))
    apply OrbitMapFlat.flatNear_of_comm c.left (a.translation g).left (t g).left he z
    apply hU
    rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    exact hg
  let := hcflat
  have : IsIso c.left := Flat.isIso_of_surjective_of_mono c.left
  rw [← hc, Over.comp_left]
  infer_instance

end Equivariance

end Langlands.GroupScheme.HomogeneousClosedImmersion
