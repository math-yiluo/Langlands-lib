import Langlands.GroupScheme.Rational.InnerFormTrivialityBaseChange
import Langlands.GroupScheme.Rational.NumberFieldCocycleCoverDescent
import Langlands.GroupScheme.Rational.NumberFieldTypeDVectorVertexHasse
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Langlands.GroupScheme.Rational.TitsIndexQuasiSplitMarking
import Langlands.GroupScheme.Rational.TrialitarianStarSign

/-! # Restriction of a quasi-split D4 cocycle to the diagram field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

section StarRestriction

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "KStar" => d.starField
local notation "b" => algebraBaseMap F KStar
local notation "GK" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : Algebra KStar (SeparableClosure KStar) :=
  (separableClosure KStar (AlgebraicClosure KStar)).algebra

local instance : IsAffineHom (GK).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType (GK).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Over the field of the diagram action, all star permutations fix the
vertices of the transported actual index. -/
theorem TitsIndexData.star_prescribedStabilizerIndex_starField
    (τ : SeparableClosure KStar ≃ₐ[KStar] SeparableClosure KStar) :
    let C := d.prescribedStabilizerIndexComparison KStar
    ∀ a : C.index.Vertex, C.index.star τ a = a := by
  let C := d.prescribedStabilizerIndexComparison KStar
  let s := AlgEquiv.autCongr (TitsIndexData.prescribedStabilizerClosureEquiv KStar) τ
  let σ := (IntermediateField.fixingSubgroupEquiv KStar).symm s
  have hσ : σ.val ∈ d.starKernel := d.starField_fixingSubgroup ▸ σ.property
  change ∀ a : C.index.Vertex, C.index.star τ a = a
  intro a
  obtain ⟨v, rfl⟩ := C.vertices.surjective a
  have h := (C.star_eq τ v).symm
  change C.index.star τ (C.vertices v) = C.vertices (d.star σ.val v) at h
  rw [(d.mem_starKernel_iff σ.val).mp hσ v] at h
  exact h

/-- The scalar-extended quasi-split group contains an actual split maximal
torus over the field of its diagram action. -/
theorem TitsIndexData.exists_splitMaximalTorus_starField (hG : IsQuasiSplit G) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of KStar))) (j : T.toGrp ⟶ GK),
      IsMaximalTorus j ∧ IsSplitTorus T.toGrp := by
  let C := d.prescribedStabilizerIndexComparison KStar
  exact ⟨C.index.pinning.torus, C.index.pinning.inclusion, C.index.maximalTorus,
    C.index.isSplitTorus_of_quasiSplit_trivialStar hG.fieldExtension
      d.star_prescribedStabilizerIndex_starField⟩

variable [NumberField F] [IsTotallyComplex F]

/-- Over the diagram field, quasi-split D4 cocycles are trivial by the
published vector-vertex Hasse kernel. -/
theorem Cocycle.isTrivial_baseChange_starField_of_quasiSplit
    (q : d.Vertex ≃ Fin 4) (hD : ∀ a c, d.cartan a c = CartanMatrix.D 4 (q a) (q c))
    (hsc : IsSimplyConnected G) (hAbs : IsAbsolutelyAlmostSimple G) (hG : IsQuasiSplit G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : (ξ.baseChangePullback b).IsTrivial := by
  let : FiniteDimensional F KStar := d.finiteDimensional_starField
  let : NumberField KStar := NumberField.of_module_finite F KStar
  let : IsTotallyComplex KStar := isTotallyComplex_of_algebra F KStar
  let C := d.prescribedStabilizerIndexComparison KStar
  let qK := C.vertices.symm.trans q
  have hDK (a c : C.index.Vertex) : C.index.cartan a c = CartanMatrix.D 4 (qK a) (qK c) := by
    simpa only [qK, Equiv.trans_apply, Equiv.apply_symm_apply] using
      (C.cartan_eq (C.vertices.symm a) (C.vertices.symm c)).trans
        (hD (C.vertices.symm a) (C.vertices.symm c))
  have hqs : IsQuasiSplit GK := hG.fieldExtension
  have hvec : ∃ a : C.index.Vertex, (qK a).val = 0 ∧ a ∈ C.index.distinguishedVertices :=
    ⟨qK.symm 0, congrArg Fin.val (qK.apply_symm_apply 0),
      C.index.mem_distinguishedVertices_of_quasiSplit hqs _⟩
  apply ξ.isTrivial_baseChangePullback_of_numberFieldKernel
    (ξ.locallyTrivial_of_totallyComplex (inferInstance : IsTotallyComplex F) hsc)
  intro M _ _ _ _ ζ hζ
  exact numberFieldTypeDVectorVertexHasse KStar GK C.index 4 qK (by decide)
    (isSimplyConnectedFieldExtension F KStar G hsc) (hAbs.baseChange_of_algebraicExtension (K := KStar))
    hDK (fun τ a _ => d.star_prescribedStabilizerIndex_starField τ a) hvec M ζ hζ

end StarRestriction

end Langlands.GroupScheme
