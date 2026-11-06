import Langlands.ClassFieldTheory.Local.AbelianGaloisFiniteQuotients
import Langlands.ClassFieldTheory.Local.FiniteArtin

/-! # Reconstruction from actual coherent finite Artin families -/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace FiniteArtinReconstruction

open AbelianGaloisFiniteQuotients

variable (K : Type u) [Field K] [PerfectField K]

theorem extension_antitone
    {U V : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (h : U ≤ V) : (extension K V).field ≤ (extension K U).field := by
  change fixedField K V ≤ fixedField K U
  exact IntermediateField.fixedField_le (fun _ hg => h hg)

omit [PerfectField K] in
theorem restrictionOfLE_comp
    (L M : FiniteAbelianExtension K) (h : L.field ≤ M.field) :
    (L.restrictionOfLE M h).comp M.abelianRestriction = L.abelianRestriction := by
  apply ContinuousMonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H s =>
    let : Algebra L.field M.field := (Subsemiring.inclusion h).toAlgebra
    let : IsScalarTower K L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower L.field M.field (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L.field M.field s).symm

/-- The actual open finite-restriction kernel. -/
def restrictionKernel (L : FiniteAbelianExtension K) :
    OpenSubgroup (Field.absoluteGaloisGroupAbelianization K) where
  toSubgroup := L.abelianRestriction.toMonoidHom.ker
  isOpen' := (isOpen_discrete ({1} : Set L.galoisGroup)).preimage
    L.abelianRestriction.continuous

@[simp] theorem extension_restrictionKernel (L : FiniteAbelianExtension K) :
    extension K (restrictionKernel K L) = L := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  apply Subtype.ext
  apply FiniteGaloisIntermediateField.val_injective
  change IntermediateField.fixedField
    (Subgroup.comap (absoluteAbelianizationProjection K).toMonoidHom
      L.abelianRestriction.toMonoidHom.ker) = L.field.toIntermediateField
  change IntermediateField.fixedField L.restriction.toMonoidHom.ker = _
  exact (congrArg IntermediateField.fixedField
    L.field.toIntermediateField.restrictNormalHom_ker).trans
      (InfiniteGalois.fixedField_fixingSubgroup _)

/-- Quotient transition agrees with actual restriction between the associated fields. -/
theorem quotientEquiv_map
    {U V : OpenSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (h : U ≤ V)
    (x : Field.absoluteGaloisGroupAbelianization K ⧸ U.toSubgroup) :
    quotientEquiv K V (QuotientGroup.map U.toSubgroup V.toSubgroup
      (MonoidHom.id _) h x) =
      ((extension K V).restrictionOfLE (extension K U) (extension_antitone K h))
        (quotientEquiv K U x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    exact (DFunLike.congr_fun
      (restrictionOfLE_comp K (extension K V) (extension K U)
        (extension_antitone K h)) g).symm

variable [TopologicalSpace K]

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates of a supplied finite family in the actual open group quotients. -/
def quotientFamily (a : FiniteArtinFamily K)
    (U : OpenNormalSubgroup (absoluteAbelianizationProfinite K)) :
    Kˣ →ₜ* (ProfiniteGrp.diagram (absoluteAbelianizationProfinite K)).obj U := by
  let e : (extension K U.toOpenSubgroup).galoisGroup →ₜ*
      (ProfiniteGrp.diagram (absoluteAbelianizationProfinite K)).obj U :=
    { toMonoidHom := (quotientEquiv K U.toOpenSubgroup).symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  exact e.comp (a (extension K U.toOpenSubgroup))

set_option backward.isDefEq.respectTransparency false in
theorem quotientFamily_compatible (a : FiniteArtinFamily K)
    (ha : FiniteArtinRestrictionRelation a)
    {U V : OpenNormalSubgroup (absoluteAbelianizationProfinite K)}
    (h : U ≤ V) (x : Kˣ) :
    QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id _) h
      (quotientFamily K a U x) = quotientFamily K a V x := by
  apply (quotientEquiv K V.toOpenSubgroup).injective
  refine (quotientEquiv_map K h (quotientFamily K a U x)).trans ?_
  change ((extension K V.toOpenSubgroup).restrictionOfLE
      (extension K U.toOpenSubgroup) (extension_antitone K h))
      (quotientEquiv K U.toOpenSubgroup
        ((quotientEquiv K U.toOpenSubgroup).symm (a (extension K U.toOpenSubgroup) x))) =
    quotientEquiv K V.toOpenSubgroup
      ((quotientEquiv K V.toOpenSubgroup).symm (a (extension K V.toOpenSubgroup) x))
  simp only [ContinuousMulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun
    (ha (extension K V.toOpenSubgroup) (extension K U.toOpenSubgroup)
      (extension_antitone K h)) x

set_option backward.isDefEq.respectTransparency false in
/-- The continuous homomorphism into Mathlib's actual finite-quotient limit. -/
def limitHom (a : FiniteArtinFamily K) (ha : FiniteArtinRestrictionRelation a) :
    Kˣ →ₜ* ProfiniteGrp.limit (ProfiniteGrp.diagram (absoluteAbelianizationProfinite K)) where
  toFun x := ⟨fun U => quotientFamily K a U x,
    fun _ _ f => quotientFamily_compatible K a ha (CategoryTheory.leOfHom f) x⟩
  map_one' := Subtype.ext (funext fun U => map_one (quotientFamily K a U))
  map_mul' x y := Subtype.ext (funext fun U => map_mul (quotientFamily K a U) x y)
  continuous_toFun := (continuous_pi fun U => (quotientFamily K a U).continuous).subtype_mk _

set_option backward.isDefEq.respectTransparency false in
/-- Reconstruct a continuous map from a supplied coherent finite family. -/
def reconstruct (a : FiniteArtinFamily K) (ha : FiniteArtinRestrictionRelation a) :
    Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K := by
  let e : ProfiniteGrp.limit (ProfiniteGrp.diagram (absoluteAbelianizationProfinite K)) →ₜ*
      absoluteAbelianizationProfinite K :=
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor
      (absoluteAbelianizationProfinite K)).symm
  exact e.comp (limitHom K a ha)

set_option backward.isDefEq.respectTransparency false in
/-- Every coordinate of the reconstructed homomorphism is the supplied one. -/
theorem reconstruct_quotient (a : FiniteArtinFamily K)
    (ha : FiniteArtinRestrictionRelation a)
    (U : OpenNormalSubgroup (absoluteAbelianizationProfinite K)) (x : Kˣ) :
    (QuotientGroup.mk (reconstruct K a ha x) :
      Field.absoluteGaloisGroupAbelianization K ⧸ U.toSubgroup) =
        quotientFamily K a U x := by
  exact congrArg (fun z => z.val U)
    ((ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor
      (absoluteAbelianizationProfinite K)).apply_symm_apply (limitHom K a ha x))

set_option backward.isDefEq.respectTransparency false in
/-- Reconstruction has the prescribed restriction on the field of every open kernel. -/
theorem reconstruct_extension (a : FiniteArtinFamily K)
    (ha : FiniteArtinRestrictionRelation a)
    (U : OpenNormalSubgroup (absoluteAbelianizationProfinite K)) :
    finiteFamilyOfHom (reconstruct K a ha) (extension K U.toOpenSubgroup) =
      a (extension K U.toOpenSubgroup) := by
  apply ContinuousMonoidHom.ext
  intro x
  have h := congrArg (quotientEquiv K U.toOpenSubgroup) (reconstruct_quotient K a ha U x)
  exact h.trans ((quotientEquiv K U.toOpenSubgroup).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
/-- Reconstruction preserves the supplied component at every actual finite extension. -/
theorem finiteFamilyOfHom_reconstruct (a : FiniteArtinFamily K)
    (ha : FiniteArtinRestrictionRelation a) :
    finiteFamilyOfHom (reconstruct K a ha) = a := by
  funext L
  let U : OpenNormalSubgroup (absoluteAbelianizationProfinite K) :=
    { restrictionKernel K L with
      isNormal' := inferInstanceAs L.abelianRestriction.toMonoidHom.ker.Normal }
  have hU : extension K U.toOpenSubgroup = L := extension_restrictionKernel K L
  exact hU ▸ reconstruct_extension K a ha U

omit [TopologicalSpace K] in
set_option backward.isDefEq.respectTransparency false in
/-- Actual finite restrictions separate elements of the Galois abelianization. -/
theorem finiteRestriction_separates
    (g h : Field.absoluteGaloisGroupAbelianization K)
    (heq : ∀ L : FiniteAbelianExtension K, L.abelianRestriction g = L.abelianRestriction h) :
    g = h := by
  apply ProfiniteGrp.toLimit_injective (absoluteAbelianizationProfinite K)
  apply Subtype.ext
  funext U
  exact (quotientEquiv K U.toOpenSubgroup).injective (heq (extension K U.toOpenSubgroup))

/-- Two continuous homomorphisms agreeing on all actual finite restrictions agree. -/
theorem finiteFamilyOfHom_injective :
    Function.Injective (finiteFamilyOfHom (K := K)) := by
  intro r s heq
  apply ContinuousMonoidHom.ext
  intro x
  apply finiteRestriction_separates K
  intro L
  exact DFunLike.congr_fun (congrFun heq L) x

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity onto every actual finite restriction implies density. -/
theorem denseRange_of_finite_surjective
    (r : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K)
    (hr : ∀ L : FiniteAbelianExtension K, Function.Surjective (finiteFamilyOfHom r L)) :
    DenseRange r := by
  let : CompactSpace (Field.absoluteGaloisGroupAbelianization K) :=
    inferInstanceAs (CompactSpace (absoluteAbelianizationProfinite K))
  let : TotallyDisconnectedSpace (Field.absoluteGaloisGroupAbelianization K) :=
    inferInstanceAs (TotallyDisconnectedSpace (absoluteAbelianizationProfinite K))
  apply dense_iff_inter_open.mpr
  rintro V hV ⟨g, hg⟩
  have hopen : IsOpen
      ((fun z : Field.absoluteGaloisGroupAbelianization K => g * z) ⁻¹' V) :=
    hV.preimage (continuous_const.mul continuous_id)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hopen (by simpa using hg)
  obtain ⟨x, hx⟩ := hr (extension K U.toOpenSubgroup)
    ((extension K U.toOpenSubgroup).abelianRestriction g)
  have heq : (QuotientGroup.mk g :
      Field.absoluteGaloisGroupAbelianization K ⧸ U.toSubgroup) = QuotientGroup.mk (r x) :=
    (quotientEquiv K U.toOpenSubgroup).injective hx.symm
  have hmem : g⁻¹ * r x ∈ U := QuotientGroup.eq.mp heq
  refine ⟨r x, ?_, ⟨x, rfl⟩⟩
  simpa only [Set.mem_preimage, mul_inv_cancel_left] using hU hmem

/-- A supplied finite norm-residue system reconstructs with its full profinite relation. -/
theorem reconstruct_normResidue (a : FiniteArtinFamily K)
    (ha : FiniteArtinSystemRelation a) :
    ProfiniteNormResidueRelation (reconstruct K a ha.2) := by
  have hfamily := finiteFamilyOfHom_reconstruct K a ha.2
  refine ⟨denseRange_of_finite_surjective K _ ?_, ?_⟩
  · intro L
    rw [hfamily]
    exact (ha.1 L).2
  · rw [hfamily]
    exact ha

end FiniteArtinReconstruction

end Langlands.LocalClassField
