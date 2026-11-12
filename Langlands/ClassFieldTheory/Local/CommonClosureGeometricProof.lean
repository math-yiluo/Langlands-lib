import Langlands.ClassFieldTheory.Local.CommonClosureGeometricStatement
import Langlands.Correspondence.BaseGeometricResidue

/-!
# Normalized common-closure reciprocity families are geometric

The base clause is the Library's `Correspondence.isGeometricReciprocity_of_isBaseReciprocity`.
For a finite extension `E` of `F`, every finite abelian extension `L` of `E` is moved into the
algebraic closure of `F` through `extensionClosureEquiv`. The norm relation of the family at the
image of `E` then identifies the finite kernels of the transported candidate with the norm
groups of `L` over `E`.
-/

noncomputable section

namespace Langlands.LocalClassField.CommonClosureGeometric

open LocalFactor LocalFactor.CommonClosure Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (g : F.Carrier →ₐ[Padic p] E.Carrier)

local instance commonClosureGeometricCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance commonClosureGeometricTopology : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology
local instance commonClosureGeometricImageTopology :
    TopologicalSpace (extensionFiniteIntermediate F E g).field :=
  (CommonClosure.canonicalData F (extensionFiniteIntermediate F E g)).topology

/-- The intermediate field of the closure of `F` corresponding to a finite abelian
extension `L` of `E` under the closure isomorphism `extensionClosureEquiv F E g`. -/
def imageField (L : LocalFiniteAbelianExtension E) :
    IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  (L.field.toIntermediateField.toSubfield.comap
    (extensionClosureEquiv F E g).toRingHom).toIntermediateField (by
      intro x
      change extensionClosureLift F E g (algebraMap F.Carrier _ x) ∈ L.field.toIntermediateField
      rw [extensionClosureLift_algebraMap]
      exact L.field.toIntermediateField.algebraMap_mem (g x))

theorem mem_imageField (L : LocalFiniteAbelianExtension E) (x : AlgebraicClosure F.Carrier) :
    x ∈ imageField F E g L ↔
      extensionClosureEquiv F E g x ∈ L.field.toIntermediateField :=
  Iff.rfl

/-- The image of `E` lies in the image of every finite abelian extension of `E`. -/
theorem extensionIntermediateField_le_imageField (L : LocalFiniteAbelianExtension E) :
    (extensionFiniteIntermediate F E g).field ≤ imageField F E g L := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F E g y).mp hy
  rw [mem_imageField, extensionClosureEquiv_apply, extensionClosureLift_fieldEmbedding]
  exact L.field.toIntermediateField.algebraMap_mem x

/-- The closure isomorphism restricted to `L` and its image field. -/
def imageFieldEquiv (L : LocalFiniteAbelianExtension E) :
    L.field ≃+* imageField F E g L where
  toFun x := ⟨(extensionClosureEquiv F E g).symm x, by
    rw [mem_imageField, RingEquiv.apply_symm_apply]
    exact x.property⟩
  invFun y := ⟨extensionClosureEquiv F E g y, y.property⟩
  left_inv x := Subtype.ext ((extensionClosureEquiv F E g).apply_symm_apply x)
  right_inv y := Subtype.ext ((extensionClosureEquiv F E g).symm_apply_apply y)
  map_mul' x y := Subtype.ext (map_mul (extensionClosureEquiv F E g).symm
    (x : AlgebraicClosure E.Carrier) y)
  map_add' x y := Subtype.ext (map_add (extensionClosureEquiv F E g).symm
    (x : AlgebraicClosure E.Carrier) y)

/-- The field isomorphism from `E` to its image in the closure of `F`. -/
abbrev baseEquiv : E.Carrier ≃+* (extensionFiniteIntermediate F E g).field :=
  letI := ((extensionFiniteIntermediate F E g).asPadicField (p := p)).algebra
  (extensionIntermediatePadicEquiv F E g).toRingEquiv

/-- The two field isomorphisms form a commuting square with the algebra maps. -/
theorem imageFieldEquiv_compatible (L : LocalFiniteAbelianExtension E) :
    letI : Algebra (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
      (IntermediateField.inclusion (extensionIntermediateField_le_imageField F E g L)).toAlgebra
    (algebraMap (extensionFiniteIntermediate F E g).field (imageField F E g L)).comp
        (baseEquiv F E g).toRingHom =
      (imageFieldEquiv F E g L).toRingHom.comp (algebraMap E.Carrier L.field) := by
  let : Algebra (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
    (IntermediateField.inclusion (extensionIntermediateField_le_imageField F E g L)).toAlgebra
  ext x
  rfl

instance imageField_finiteDimensional (L : LocalFiniteAbelianExtension E) :
    FiniteDimensional F.Carrier (imageField F E g L) := by
  let : Algebra (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
    (IntermediateField.inclusion (extensionIntermediateField_le_imageField F E g L)).toAlgebra
  have : IsScalarTower F.Carrier (extensionFiniteIntermediate F E g).field
      (imageField F E g L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
    Module.Finite.of_equiv_equiv (baseEquiv F E g) (imageFieldEquiv F E g L)
      (imageFieldEquiv_compatible F E g L)
  exact FiniteDimensional.trans F.Carrier (extensionFiniteIntermediate F E g).field _

/-- The image field as a finite intermediate extension of the closure of `F`. -/
def imageExtension (L : LocalFiniteAbelianExtension E) : FiniteIntermediateExtension F.Carrier :=
  ⟨imageField F E g L, inferInstance⟩

/-- Restriction to `L` is trivial exactly when the image in `G_F` fixes the image field. -/
theorem restriction_eq_one_iff (L : LocalFiniteAbelianExtension E)
    (σ : Field.absoluteGaloisGroup E.Carrier) :
    L.restriction σ = 1 ↔
      extensionGaloisMap F E g σ ∈ (imageField F E g L).fixingSubgroup := by
  have hker : L.restriction σ = 1 ↔
      ∀ y ∈ L.field.toIntermediateField, AlgEquiv.toAlgHom σ y = y := by
    change σ ∈ L.restriction.toMonoidHom.ker ↔ _
    rw [show L.restriction.toMonoidHom.ker = L.field.toIntermediateField.fixingSubgroup from
      L.field.toIntermediateField.restrictNormalHom_ker]
    exact IntermediateField.mem_fixingSubgroup_iff _ _
  have hfix : extensionGaloisMap F E g σ ∈ (imageField F E g L).fixingSubgroup ↔
      ∀ x ∈ imageField F E g L, AlgEquiv.toAlgHom (extensionGaloisMap F E g σ) x = x :=
    IntermediateField.mem_fixingSubgroup_iff _ _
  rw [hker, hfix]
  constructor
  · intro h x hx
    apply (extensionClosureEquiv F E g).injective
    rw [extensionClosureEquiv_apply, extensionClosureEquiv_apply,
      extensionClosureLift_galoisMap]
    exact h _ hx
  · intro h y hy
    obtain ⟨x, rfl⟩ := (extensionClosureEquiv F E g).surjective y
    have hx : x ∈ imageField F E g L := hy
    have h1 := extensionClosureLift_galoisMap F E g σ x
    rw [h x hx] at h1
    exact h1.symm

/-- The image of a standalone Weil element comes from the Weil abelianization of the
image field exactly when its Galois projection restricts trivially to `L`. -/
theorem projection_mem_range_iff (L : LocalFiniteAbelianExtension E) (w : localWeilGroup E) :
    abelianizationProjection _ (extensionImageWeilEquiv F E g w) ∈
        ((extensionFiniteIntermediate F E g).weilAbelianInclusion (imageExtension F E g L)
          (extensionIntermediateField_le_imageField F E g L)
          (localResidueDegree F)).toMonoidHom.range ↔
      L.restriction (localProjection E w) = 1 := by
  let j := extensionImageWeilEquiv F E g
  let χ : pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E g).field
      (localResidueDegree F) →ₜ* L.galoisGroup :=
    L.restriction.comp ((localProjection E).comp
      (j.symm : pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E g).field
        (localResidueDegree F) →ₜ* localWeilGroup E))
  have hproj : ∀ u : pullbackFixingSubgroup F.Carrier
      (extensionFiniteIntermediate F E g).field (localResidueDegree F),
      extensionGaloisMap F E g (localProjection E (j.symm u)) =
        Weil.projection (localResidueDegree F) u.1 := by
    intro u
    change localProjection F (extensionWeilMap F E g (j.symm u)) = _
    rw [← extensionImageWeilEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
    rfl
  constructor
  · rintro ⟨a, ha⟩
    have hχ := congrArg (abelianizationLift χ) ha
    change _ = χ (j w) at hχ
    have hw : χ (j w) = L.restriction (localProjection E w) := by
      change L.restriction (localProjection E (j.symm (j w))) = _
      rw [ContinuousMulEquiv.symm_apply_apply]
    rw [← hw, ← hχ]
    induction a using QuotientGroup.induction_on with
    | H v =>
      change L.restriction (localProjection E (j.symm _)) = 1
      rw [restriction_eq_one_iff F E g L, hproj]
      exact v.2
  · intro h
    have hm : (j w : localWeilGroup F) ∈ pullbackFixingSubgroup F.Carrier
        (imageExtension F E g L).field (localResidueDegree F) := by
      have h' := (restriction_eq_one_iff F E g L _).mp h
      have h2 := hproj (j w)
      rw [ContinuousMulEquiv.symm_apply_apply] at h2
      rw [h2] at h'
      exact h'
    exact ⟨QuotientGroup.mk ⟨(j w : localWeilGroup F), hm⟩, rfl⟩

/-- Norm groups over `E` correspond to norm ranges over its image in the closure of `F`. -/
theorem unitsEquiv_symm_mem_normSubgroup_iff (L : LocalFiniteAbelianExtension E)
    (x : (extensionFiniteIntermediate F E g).fieldˣ) :
    (extensionIntermediateUnitsEquiv F E g).symm x ∈ normSubgroup E.Carrier L.field ↔
      x ∈ ((extensionFiniteIntermediate F E g).unitsNorm (imageExtension F E g L)
        (extensionIntermediateField_le_imageField F E g L)).range := by
  let : Algebra (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
    (IntermediateField.inclusion (extensionIntermediateField_le_imageField F E g L)).toAlgebra
  have : IsScalarTower F.Carrier (extensionFiniteIntermediate F E g).field
      (imageField F E g L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (extensionFiniteIntermediate F E g).field (imageField F E g L) :=
    FiniteDimensional.right F.Carrier (extensionFiniteIntermediate F E g).field _
  have h := FiniteArtinTransport.mem_normSubgroup_map_iff (baseEquiv F E g)
    (imageFieldEquiv F E g L) (imageFieldEquiv_compatible F E g L)
    ((extensionIntermediateUnitsEquiv F E g).symm x)
  have hx : Units.mapEquiv (baseEquiv F E g).toMulEquiv
      ((extensionIntermediateUnitsEquiv F E g).symm x) = x := by
    conv_rhs => rw [← (extensionIntermediateUnitsEquiv F E g).apply_symm_apply x]
    apply Units.ext
    rfl
  rw [hx] at h
  exact h.symm

/-- The finite kernels of the transported candidate are the actual norm groups. -/
theorem finiteNormKernel_extensionReciprocityCandidate (eC : ReciprocityFamily F)
    (he : LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC)
    (L : LocalFiniteAbelianExtension E) :
    (finiteFamilyOfHom
      (candidateGaloisHom E.canonicalTopologicalData (localResidueDegree E)
        (extensionReciprocityCandidate F E g eC)) L).toMonoidHom.ker =
      normSubgroup E.Carrier L.field := by
  apply Subgroup.ext
  intro x
  obtain ⟨a, rfl⟩ := (extensionReciprocityCandidate F E g eC).surjective x
  induction a using QuotientGroup.induction_on with
  | H w =>
    change finiteFamilyOfHom
        (candidateGaloisHom E.canonicalTopologicalData (localResidueDegree E)
          (extensionReciprocityCandidate F E g eC)) L
        (Correspondence.reciprocityHom E (extensionReciprocityCandidate F E g eC) w) = 1 ↔
      (extensionIntermediateUnitsEquiv F E g).symm
        (eC (extensionFiniteIntermediate F E g)
          (abelianizationProjection _ (extensionImageWeilEquiv F E g w))) ∈
        normSubgroup E.Carrier L.field
    rw [Correspondence.finiteRestriction_reciprocityHom, unitsEquiv_symm_mem_normSubgroup_iff]
    have hn := ReciprocitySystemUniqueness.symm_mem_range_iff he
      (extensionFiniteIntermediate F E g) (imageExtension F E g L)
      (extensionIntermediateField_le_imageField F E g L)
      (eC (extensionFiniteIntermediate F E g)
        (abelianizationProjection _ (extensionImageWeilEquiv F E g w)))
    rw [ContinuousMulEquiv.symm_apply_apply] at hn
    exact (projection_mem_range_iff F E g L w).symm.trans hn

/-- The transported candidate satisfies the density, finite norm-residue and
compatibility relations. -/
theorem profiniteNormResidue_extensionReciprocityCandidate (eC : ReciprocityFamily F)
    (he : LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC) :
    ProfiniteNormResidueRelation
      (candidateGaloisHom E.canonicalTopologicalData (localResidueDegree E)
        (extensionReciprocityCandidate F E g eC)) := by
  let := Algebra.charZero_of_charZero (Padic p) E.Carrier
  refine ⟨FiniteArtinReconstruction.denseRange_of_finite_surjective E.Carrier _
    (Correspondence.finiteRestriction_surjective E (extensionReciprocityCandidate F E g eC)),
    ?_, ?_⟩
  · intro L
    exact ⟨finiteNormKernel_extensionReciprocityCandidate F E g eC he L,
      Correspondence.finiteRestriction_surjective E _ L⟩
  · exact ProfiniteReciprocityReconstruction.finiteFamilyOfHom_compatible E.Carrier _

end Langlands.LocalClassField.CommonClosureGeometric

namespace Langlands.LocalClassField

open LocalFactor.CommonClosure Weil.Local

universe u v

/-- Normalized common-closure reciprocity families are geometric at `F` and, after
transport, at every finite extension of `F`. -/
theorem commonClosureGeometricProof : CommonClosureGeometricStatement.{u, v} := by
  intro p _ F eC he
  refine ⟨fun e h => Correspondence.isGeometricReciprocity_of_isBaseReciprocity F e eC h he, ?_⟩
  intro E g
  exact Correspondence.isGeometricReciprocity_of_localCandidate E _
    ⟨extensionReciprocityCandidate_geometricOrder F E g eC he.2,
      CommonClosureGeometric.profiniteNormResidue_extensionReciprocityCandidate F E g eC he.1.1⟩

end Langlands.LocalClassField
