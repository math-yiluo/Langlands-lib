import Langlands.AlgebraicGeometry.FiniteEtale.CoverPowerLift
import Langlands.AlgebraicGeometry.FiniteEtale.FixedPointSection
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Galois.Basic

/-! # Pointed Galois refinements of split finite étale field covers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable (K K' Ω : Type u) [Field K] [Field K'] [Field Ω]
  [Algebra K K'] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]

/-- The geometric point of the larger field maps to the geometric point of the
smaller field defined by the same scalar tower. -/
theorem fieldGeometricPoint_comp :
    Spec.algebraMap K' Ω ≫ Spec.algebraMap K K' = Spec.algebraMap K Ω := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (hs : ∀ Y : Cover (Spec (.of K)), Finite (Fiber (Spec.algebraMap K Ω) Y))
  (ht : ∀ Y : Cover (Spec (.of K')), Finite (Fiber (Spec.algebraMap K' Ω) Y))
  (Y : Cover (Spec (.of K)))

/-- A geometric lift fixed by the larger field's pointed group descends to an
actual point over that field. -/
def ringPointOfFixedGeometricLift [IsAlgClosed Ω] (x : Fiber (Spec.algebraMap K Ω) Y)
    (hx : ∀ g : FundamentalGroup (Spec.algebraMap K' Ω) ht,
      fundamentalGroupMap (Spec.algebraMap K K') (Spec.algebraMap K' Ω)
        (Spec.algebraMap K Ω) (fieldGeometricPoint_comp K K' Ω) ht hs g • x = x) :
    {y : RingPoint K Y.obj K' //
      ringTestMap K (IsScalarTower.toAlgHom K K' Ω) ≫ y = x} := by
  let f := Spec.algebraMap K K'
  let t := Spec.algebraMap K' Ω
  let s := Spec.algebraMap K Ω
  let h := fieldGeometricPoint_comp K K' Ω
  let Y' := (pullbackFunctor f).obj Y
  let e := pullbackFiberEquiv f t s h Y
  let x' : Fiber t Y' := e x
  have hx' (g : FundamentalGroup t ht) : g • x' = x' :=
    (pullbackFiberEquiv_smul f t s h ht hs g Y x).symm.trans (congrArg e (hx g))
  let σ := sectionOfFixedGeometricLift t ht Y' x' hx'
  let y : RingPoint K Y.obj K' := Over.homMk (σ.val ≫ pullback.fst Y.obj.hom f) (by
    change (σ.val ≫ pullback.fst Y.obj.hom f) ≫ Y.obj.hom = f
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hσ : σ.val ≫ pullback.snd Y.obj.hom f = 𝟙 _ := σ.property.1
    rw [hσ, Category.id_comp])
  refine ⟨y, Over.OverMorphism.ext ?_⟩
  change t ≫ σ.val ≫ pullback.fst Y.obj.hom f = x.left
  rw [← Category.assoc, σ.property.2]
  exact pullbackFiberEquiv_apply_left_fst f t s h Y x

/-- A pointed refinement by an actual finite Galois extension of the base
field, embedded in the supplied splitting field. -/
structure GaloisFieldCoverLift (x : Fiber (Spec.algebraMap K Ω) Y) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra K extension]
  [finite : Module.Finite K extension]
  [galois : IsGalois K extension]
  embedding : extension →ₐ[K] K'
  lift : Fiber (Spec.algebraMap K Ω) (fieldExtensionCover K extension)
  map : fieldExtensionCover K extension ⟶ Y
  map_lift : lift ≫ map.hom = x

attribute [instance] GaloisFieldCoverLift.field GaloisFieldCoverLift.algebra
  GaloisFieldCoverLift.finite GaloisFieldCoverLift.galois

/-- If the pointed group of `K'` fixes the whole fibre, the normal closure
of the residue field of any chosen lift embeds in `K'` and refines the cover
through that lift. -/
def splitFieldCoverRefinement [CharZero K] [IsAlgClosed Ω]
    (x : Fiber (Spec.algebraMap K Ω) Y)
    (hfix : ∀ (g : FundamentalGroup (Spec.algebraMap K' Ω) ht)
      (z : Fiber (Spec.algebraMap K Ω) Y),
      fundamentalGroupMap (Spec.algebraMap K K') (Spec.algebraMap K' Ω)
        (Spec.algebraMap K Ω) (fieldGeometricPoint_comp K K' Ω) ht hs g • z = z) :
    GaloisFieldCoverLift K K' Ω Y x := by
  letI : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let A := AffineCoordinateRing K Y.obj
  let i := affineSchemeOverIso K Y.obj
  let f := CommRingCat.ofHom (affineCoordinateMap K Y.obj)
  have hf : IsFinite (Spec.map f) := by
    change IsFinite (Spec.algebraMap K A)
    rw [affineCoordinateSpecMap]
    infer_instance
  letI : Module.Finite K A :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff f).mp hf)
  let a : A →ₐ[K] Ω := affineRingPointEquiv K A Ω (x ≫ i.hom)
  letI : Module.Finite K a.range :=
    Module.Finite.of_surjective a.rangeRestrict.toLinearMap a.rangeRestrict_surjective
  let L := Algebra.IsAlgebraic.toIntermediateField a.range
  letI : Module.Finite K L := ‹Module.Finite K a.range›
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let aL : A →ₐ[K] L := a.rangeRestrict
  let u := IsScalarTower.toAlgHom K K' Ω
  have hσ (σ : L →ₐ[K] Ω) : σ.fieldRange ≤ u.fieldRange := by
    let z : Fiber (Spec.algebraMap K Ω) Y := ringTestMap K (σ.comp aL) ≫ i.inv
    obtain ⟨y, hy⟩ := ringPointOfFixedGeometricLift K K' Ω hs ht Y z (fun g => hfix g z)
    let b : A →ₐ[K] K' := affineRingPointEquiv K A K' (y ≫ i.hom)
    have hb : ringTestMap K b = y ≫ i.hom := ringTestMap_affineRingPointEquiv K _
    have he : ringTestMap K (u.comp b) = ringTestMap K (σ.comp aL) := by
      rw [ringTestMap_comp, hb, ← Category.assoc, hy]
      simp [z]
    have hab : u.comp b = σ.comp aL := by
      have hm := Spec.map_injective (congrArg (fun p => Over.Hom.left p) he)
      ext c
      exact congrArg (fun (r : CommRingCat.of A ⟶ CommRingCat.of Ω) => r c) hm
    rintro _ ⟨l, rfl⟩
    obtain ⟨c, hc⟩ := a.rangeRestrict_surjective l
    exact ⟨b c, (DFunLike.congr_fun hab c).trans (congrArg σ hc)⟩
  let M := IntermediateField.normalClosure K L Ω
  have hM : M ≤ u.fieldRange := normalClosure_le_iff.mpr hσ
  letI : IsNormalClosure K L M :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun c =>
      IsAlgClosed.splits ((minpoly K c).map (algebraMap K Ω)))
  letI : Normal K M := IsNormalClosure.normal (K := L)
  letI : IsGalois K M := ⟨⟩
  let l : L →ₐ[K] M := (normalClosure.algHomEquiv K L Ω).symm L.val
  have hl : M.val.comp l = L.val :=
    (normalClosure.algHomEquiv K L Ω).apply_symm_apply L.val
  refine
    { extension := M
      embedding := u.equivFieldRange.symm.toAlgHom.comp (IntermediateField.inclusion hM)
      lift := ringTestMap K M.val
      map := ObjectProperty.homMk (ringTestMap K (l.comp aL) ≫ i.inv)
      map_lift := ?_ }
  change ringTestMap K M.val ≫ ringTestMap K (l.comp aL) ≫ i.inv = x
  rw [← Category.assoc, ← ringTestMap_comp, ← AlgHom.comp_assoc, hl]
  change ringTestMap K a ≫ i.inv = x
  rw [ringTestMap_affineRingPointEquiv, Category.assoc, i.hom_inv_id, Category.comp_id]

end Langlands.AlgebraicGeometry.FiniteEtale
