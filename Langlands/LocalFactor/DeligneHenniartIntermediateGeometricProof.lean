import Langlands.LocalFactor.DeligneHenniartIntermediateUnits
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof

/-!
# Geometricity of the intermediate components of a normalized common-closure family

For a finite intermediate field `E` of the closure of `F`, the component `eC E`, read on the
standalone Weil group of `E` through `intermediateWeilEquiv F E`, is a geometric Weil
reciprocity map of `E`. The order normalization comes from the family's normalization. Every
finite abelian extension `L` of `E` is moved into the closure of `F` through
`intermediateClosureEquiv F E`; the norm relation of the family at `E` then identifies the
finite kernels of the candidate with the norm groups of `L` over `E`.
-/

noncomputable section

universe uF

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.IntermediateGeometric

open LocalClassField LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : Extension F)

local notation "EP" => E.asPadicField (p := p)

local instance intermediateGeometricCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance intermediateGeometricTopology : TopologicalSpace E.field :=
  (fieldData F E).topology

/-- The inverse closure isomorphism sends an element of `E` in the closure of `F` to its
image in the closure of `E`. -/
theorem closureEquiv_symm_coe (y : E.field) :
    (intermediateClosureEquiv F E).symm (y : AlgebraicClosure F.Carrier) =
      algebraMap E.field (AlgebraicClosure E.field) y :=
  (intermediateClosureEquiv F E).symm.commutes y

/-- The intermediate field of the closure of `F` corresponding to a finite abelian
extension `L` of `E` under the closure isomorphism `intermediateClosureEquiv F E`. -/
def imageField (L : LocalFiniteAbelianExtension EP) :
    IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  (L.field.toIntermediateField.toSubfield.comap
    (intermediateClosureEquiv F E).symm.toRingEquiv.toRingHom).toIntermediateField (by
      intro x
      change (intermediateClosureEquiv F E).symm
        ((algebraMap F.Carrier E.field x : E.field) : AlgebraicClosure F.Carrier) ∈
          L.field.toIntermediateField
      rw [closureEquiv_symm_coe]
      exact L.field.toIntermediateField.algebraMap_mem _)

theorem mem_imageField (L : LocalFiniteAbelianExtension EP) (x : AlgebraicClosure F.Carrier) :
    x ∈ imageField F E L ↔
      (intermediateClosureEquiv F E).symm x ∈ L.field.toIntermediateField :=
  Iff.rfl

/-- `E` lies in the image of every finite abelian extension of `E`. -/
theorem field_le_imageField (L : LocalFiniteAbelianExtension EP) :
    E.field ≤ imageField F E L := by
  intro y hy
  rw [mem_imageField]
  change (intermediateClosureEquiv F E).symm ((⟨y, hy⟩ : E.field) : AlgebraicClosure F.Carrier) ∈ _
  rw [closureEquiv_symm_coe]
  exact L.field.toIntermediateField.algebraMap_mem _

/-- The closure isomorphism restricted to `L` and its image field. -/
def imageFieldEquiv (L : LocalFiniteAbelianExtension EP) :
    L.field ≃+* imageField F E L where
  toFun x := ⟨intermediateClosureEquiv F E x, by
    rw [mem_imageField, AlgEquiv.symm_apply_apply]
    exact x.property⟩
  invFun y := ⟨(intermediateClosureEquiv F E).symm y, y.property⟩
  left_inv x := Subtype.ext ((intermediateClosureEquiv F E).symm_apply_apply x)
  right_inv y := Subtype.ext ((intermediateClosureEquiv F E).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (intermediateClosureEquiv F E)
    (x : AlgebraicClosure E.field) y)
  map_add' x y := Subtype.ext (map_add (intermediateClosureEquiv F E)
    (x : AlgebraicClosure E.field) y)

/-- The identity of `E` and the restricted closure isomorphism form a commuting square with
the algebra maps. -/
theorem imageFieldEquiv_compatible (L : LocalFiniteAbelianExtension EP) :
    letI : Algebra E.field (imageField F E L) :=
      (IntermediateField.inclusion (field_le_imageField F E L)).toAlgebra
    (algebraMap E.field (imageField F E L)).comp (RingEquiv.refl E.field).toRingHom =
      (imageFieldEquiv F E L).toRingHom.comp (algebraMap (EP).Carrier L.field) := by
  let : Algebra E.field (imageField F E L) :=
    (IntermediateField.inclusion (field_le_imageField F E L)).toAlgebra
  ext x
  change (x : AlgebraicClosure F.Carrier) =
    intermediateClosureEquiv F E (algebraMap E.field (AlgebraicClosure E.field) x)
  rw [intermediateClosureEquiv_algebraMap]

instance imageField_finiteDimensional (L : LocalFiniteAbelianExtension EP) :
    FiniteDimensional F.Carrier (imageField F E L) := by
  let : Algebra E.field (imageField F E L) :=
    (IntermediateField.inclusion (field_le_imageField F E L)).toAlgebra
  have : IsScalarTower F.Carrier E.field (imageField F E L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.field (imageField F E L) :=
    Module.Finite.of_equiv_equiv (RingEquiv.refl E.field) (imageFieldEquiv F E L)
      (imageFieldEquiv_compatible F E L)
  exact FiniteDimensional.trans F.Carrier E.field _

/-- The image field as a finite intermediate extension of the closure of `F`. -/
def imageExtension (L : LocalFiniteAbelianExtension EP) : FiniteIntermediateExtension F.Carrier :=
  ⟨imageField F E L, inferInstance⟩

/-- Restriction to `L` is trivial exactly when the image in `G_F` fixes the image field. -/
theorem restriction_eq_one_iff (L : LocalFiniteAbelianExtension EP)
    (σ : Field.absoluteGaloisGroup E.field) :
    L.restriction σ = 1 ↔
      intermediateGaloisMap F E σ ∈ (imageField F E L).fixingSubgroup := by
  have hker : L.restriction σ = 1 ↔
      ∀ y ∈ L.field.toIntermediateField, AlgEquiv.toAlgHom σ y = y := by
    change σ ∈ L.restriction.toMonoidHom.ker ↔ _
    rw [show L.restriction.toMonoidHom.ker = L.field.toIntermediateField.fixingSubgroup from
      L.field.toIntermediateField.restrictNormalHom_ker]
    exact IntermediateField.mem_fixingSubgroup_iff _ _
  have hfix : intermediateGaloisMap F E σ ∈ (imageField F E L).fixingSubgroup ↔
      ∀ x ∈ imageField F E L, AlgEquiv.toAlgHom (intermediateGaloisMap F E σ) x = x :=
    IntermediateField.mem_fixingSubgroup_iff _ _
  rw [hker, hfix]
  constructor
  · intro h x hx
    have hx' : (intermediateClosureEquiv F E).symm x ∈ L.field.toIntermediateField := hx
    rw [intermediateGaloisMap_apply, h _ hx', AlgEquiv.apply_symm_apply]
  · intro h y hy
    apply (intermediateClosureEquiv F E).injective
    rw [← intermediateClosureEquiv_galoisMap]
    apply h
    rw [mem_imageField, AlgEquiv.symm_apply_apply]
    exact hy

/-- The image of a standalone Weil element comes from the Weil abelianization of the image
field exactly when its Galois projection restricts trivially to `L`. -/
theorem projection_mem_range_iff (L : LocalFiniteAbelianExtension EP) (w : localWeilGroup EP) :
    abelianizationProjection _ (intermediateWeilEquiv F E w) ∈
        (E.weilAbelianInclusion (imageExtension F E L) (field_le_imageField F E L)
          (localResidueDegree F)).toMonoidHom.range ↔
      L.restriction (localProjection EP w) = 1 := by
  let j := intermediateWeilEquiv F E
  let χ : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) →ₜ* L.galoisGroup :=
    L.restriction.comp ((localProjection EP).comp
      (j.symm : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) →ₜ*
        localWeilGroup EP))
  have hproj : ∀ u : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F),
      intermediateGaloisMap F E (localProjection EP (j.symm u)) =
        Weil.projection (localResidueDegree F) u.1 :=
    fun u => intermediateWeilEquiv_symm_projection F E u
  constructor
  · rintro ⟨a, ha⟩
    have hχ := congrArg (abelianizationLift χ) ha
    change _ = χ (j w) at hχ
    have hw : χ (j w) = L.restriction (localProjection EP w) := by
      change L.restriction (localProjection EP (j.symm (j w))) = _
      rw [ContinuousMulEquiv.symm_apply_apply]
    rw [← hw, ← hχ]
    induction a using QuotientGroup.induction_on with
    | H v =>
      change L.restriction (localProjection EP (j.symm _)) = 1
      rw [restriction_eq_one_iff F E L, hproj]
      exact v.2
  · intro h
    have hm : (j w : localWeilGroup F) ∈ pullbackFixingSubgroup F.Carrier
        (imageExtension F E L).field (localResidueDegree F) := by
      have h' := (restriction_eq_one_iff F E L _).mp h
      have h2 := hproj (j w)
      rw [ContinuousMulEquiv.symm_apply_apply] at h2
      rw [h2] at h'
      exact h'
    exact ⟨QuotientGroup.mk ⟨(j w : localWeilGroup F), hm⟩, rfl⟩

/-- Norm groups over `E` from `L` are the norm ranges over `E` from the image field. -/
theorem mem_normSubgroup_iff (L : LocalFiniteAbelianExtension EP) (x : E.fieldˣ) :
    x ∈ normSubgroup (EP).Carrier L.field ↔
      x ∈ (E.unitsNorm (imageExtension F E L) (field_le_imageField F E L)).range := by
  let : Algebra E.field (imageField F E L) :=
    (IntermediateField.inclusion (field_le_imageField F E L)).toAlgebra
  have : IsScalarTower F.Carrier E.field (imageField F E L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.field (imageField F E L) :=
    FiniteDimensional.right F.Carrier E.field _
  have h := FiniteArtinTransport.mem_normSubgroup_map_iff (RingEquiv.refl E.field)
    (imageFieldEquiv F E L) (imageFieldEquiv_compatible F E L) x
  have hx : Units.mapEquiv (RingEquiv.refl E.field).toMulEquiv x = x := by
    apply Units.ext
    rfl
  rw [hx] at h
  exact h.symm

/-- The candidate at `E` sends the image of a standalone Weil element to the component
`eC E` of the corresponding element of `W_E`. -/
theorem intermediateReciprocityCandidate_projection (eC : ReciprocityFamily F)
    (w : localWeilGroup EP) :
    intermediateReciprocityCandidate F eC E (WeilQuotients.projection (localResidueDegree EP) w) =
      eC E (abelianizationProjection _ (intermediateWeilEquiv F E w)) :=
  rfl

/-- The finite kernels of the intermediate candidate are the actual norm groups. -/
theorem finiteNormKernel (eC : ReciprocityFamily F)
    (he : LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC)
    (L : LocalFiniteAbelianExtension EP) :
    (finiteFamilyOfHom
      (candidateGaloisHom (EP).canonicalTopologicalData (localResidueDegree EP)
        (intermediateReciprocityCandidate F eC E)) L).toMonoidHom.ker =
      normSubgroup (EP).Carrier L.field := by
  apply Subgroup.ext
  intro x
  obtain ⟨a, rfl⟩ := (intermediateReciprocityCandidate F eC E).surjective x
  induction a using QuotientGroup.induction_on with
  | H w =>
    change finiteFamilyOfHom
        (candidateGaloisHom (EP).canonicalTopologicalData (localResidueDegree EP)
          (intermediateReciprocityCandidate F eC E)) L
        (Correspondence.reciprocityHom EP (intermediateReciprocityCandidate F eC E) w) = 1 ↔
      eC E (abelianizationProjection _ (intermediateWeilEquiv F E w)) ∈
        normSubgroup (EP).Carrier L.field
    rw [Correspondence.finiteRestriction_reciprocityHom, mem_normSubgroup_iff]
    have hn := ReciprocitySystemUniqueness.symm_mem_range_iff he E (imageExtension F E L)
      (field_le_imageField F E L)
      (eC E (abelianizationProjection _ (intermediateWeilEquiv F E w)))
    rw [ContinuousMulEquiv.symm_apply_apply] at hn
    exact (projection_mem_range_iff F E L w).symm.trans hn

/-- The intermediate candidate satisfies the density, finite norm-residue and compatibility
relations. -/
theorem profiniteNormResidue (eC : ReciprocityFamily F)
    (he : LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC) :
    ProfiniteNormResidueRelation
      (candidateGaloisHom (EP).canonicalTopologicalData (localResidueDegree EP)
        (intermediateReciprocityCandidate F eC E)) := by
  refine ⟨FiniteArtinReconstruction.denseRange_of_finite_surjective (EP).Carrier _
    (Correspondence.finiteRestriction_surjective EP (intermediateReciprocityCandidate F eC E)),
    ?_, ?_⟩
  · intro L
    exact ⟨finiteNormKernel F E eC he L,
      Correspondence.finiteRestriction_surjective EP _ L⟩
  · exact ProfiniteReciprocityReconstruction.finiteFamilyOfHom_compatible (EP).Carrier _

/-- On the abelianized Weil group, the base-field degree of the image in `W_E` is the
standalone degree raised to the relative residue degree. -/
theorem weilDegree_abelianizationCongr
    (w : WeilQuotients.Abelianization (localResidueDegree EP)) :
    E.weilDegree (localResidueDegree F) (abelianizationCongr (intermediateWeilEquiv F E) w) =
      WeilQuotients.degree (localResidueDegree EP) w ^
        extensionResidueDegree F EP (intermediateEmbedding F E) := by
  refine QuotientGroup.induction_on w ?_
  intro w
  exact localDegree_intermediateWeilMap F E w

/-- The family's normalization becomes the standalone normalized absolute-value formula. -/
theorem normalizedAbs (eC : ReciprocityFamily F)
    (hn : LocalClassField.CommonClosure.NormalizationRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F)
      F.canonicalTopologicalData eC)
    (w : WeilQuotients.Abelianization (localResidueDegree EP)) :
    (EP).canonicalTopologicalData.normalizedAbs
        (intermediateReciprocityCandidate F eC E w : (EP).Carrier) =
      ((EP).canonicalTopologicalData.residueCardinality : ℝ) ^
        (-Multiplicative.toAdd (WeilQuotients.degree (localResidueDegree EP) w)) := by
  change (LocalClassField.CommonClosure.canonicalData F E).normalizedAbs
    ((eC E (abelianizationCongr (intermediateWeilEquiv F E) w) : E.fieldˣ) : E.field) = _
  rw [hn, weilDegree_abelianizationCongr,
    extensionResidueCardinality F EP (intermediateEmbedding F E),
    Nat.cast_pow, toAdd_pow, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- The intermediate candidate has the plus-sign geometric order normalization. -/
theorem geometricOrder (eC : ReciprocityFamily F)
    (hn : LocalClassField.CommonClosure.NormalizationRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F)
      F.canonicalTopologicalData eC) :
    GeometricOrderRelation (EP).canonicalTopologicalData (localResidueDegree EP)
      (intermediateReciprocityCandidate F eC E) := by
  apply MonoidHom.ext
  intro w
  change Multiplicative.ofAdd ((EP).canonicalTopologicalData.ord
    (intermediateReciprocityCandidate F eC E w : (EP).Carrier)) =
      WeilQuotients.degree (localResidueDegree EP) w
  apply Multiplicative.toAdd.injective
  change (EP).canonicalTopologicalData.ord
    (intermediateReciprocityCandidate F eC E w : (EP).Carrier) = _
  have h := normalizedAbs F E eC hn w
  rw [(EP).canonicalTopologicalData.normalizedAbs_of_ne_zero
    (intermediateReciprocityCandidate F eC E w).ne_zero] at h
  have hq : (1 : ℝ) < (EP).canonicalTopologicalData.residueCardinality := by
    exact_mod_cast (EP).canonicalTopologicalData.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.IntermediateGeometric

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

/-- The intermediate components of every normalized common-closure family are geometric
Weil reciprocity maps of the intermediate fields. -/
theorem intermediateGeometricProof : IntermediateGeometricStatement.{uF} := by
  intro p _ F eC he E
  exact Correspondence.isGeometricReciprocity_of_localCandidate (E.asPadicField (p := p)) _
    ⟨IntermediateGeometric.geometricOrder F E eC he.2,
      IntermediateGeometric.profiniteNormResidue F E eC he.1.1⟩

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
