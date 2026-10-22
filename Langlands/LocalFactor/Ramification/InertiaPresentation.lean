import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Langlands.LocalFactor.Ramification.Descent
import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Local.ExtensionWeil
import Langlands.Weil.Representation.Predicates

/-!
# Actual finite inertia restrictions and Weil representation presentations

Constructed maps use the given fields and embeddings. Surjectivity is an explicit
argument to descent; no conductor-independence or presentation-existence law is assumed.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open IsLocalRing
open scoped ValuativeRel
open Weil.Local

universe u v
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
variable (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))

/-- The actual inclusion of the base into a finite subextension. -/
def finiteBaseEmbedding : F.Carrier →ₐ[Padic p] (absoluteFiniteExtension F L).Carrier :=
  IsScalarTower.toAlgHom (Padic p) F.Carrier L

/-- The actual finite integer ring embeds into the closure integer ring. -/
def finiteClosureIntegerMap :
    (absoluteFiniteExtension F L).canonicalTopologicalData.Integers →+*
      F.closureIntegers F.canonicalTopologicalData := by
  let E := absoluteFiniteExtension F L
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.valuativeRel
  let := (extensionIntegerMap F E (finiteBaseEmbedding F L)).toAlgebra
  have := extensionIntegers_isIntegral F E (finiteBaseEmbedding F L)
  let : IsScalarTower F.canonicalTopologicalData.Integers
      E.canonicalTopologicalData.Integers (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine (L.val.toRingHom.comp E.canonicalTopologicalData.Integers.subtype).codRestrict
    (F.closureIntegers F.canonicalTopologicalData).toSubring ?_
  intro x
  apply (LocalGalois.closureIntegers_integral F.Carrier _).mp
  exact (Algebra.IsIntegral.isIntegral (R := F.canonicalTopologicalData.Integers) x).map
    (IsScalarTower.toAlgHom F.canonicalTopologicalData.Integers
      E.canonicalTopologicalData.Integers (AlgebraicClosure F.Carrier))

@[simp] theorem finiteClosureIntegerMap_coe
    (x : (absoluteFiniteExtension F L).canonicalTopologicalData.Integers) :
    (finiteClosureIntegerMap F L x : AlgebraicClosure F.Carrier) = (x : L) := rfl

instance finiteClosureIntegerMap_isLocalHom : IsLocalHom (finiteClosureIntegerMap F L) := by
  let E := absoluteFiniteExtension F L
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.valuativeRel
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let := (LocalGalois.localIntegerMap F.Carrier).toAlgebra
  let := (finiteClosureIntegerMap F L).toAlgebra
  let := (extensionIntegerMap F E (finiteBaseEmbedding F L)).toAlgebra
  let : IsScalarTower F.canonicalTopologicalData.Integers
      E.canonicalTopologicalData.Integers (F.closureIntegers F.canonicalTopologicalData) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F.canonicalTopologicalData.Integers
      (F.closureIntegers F.canonicalTopologicalData) (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hi : Algebra.IsIntegral E.canonicalTopologicalData.Integers
      (F.closureIntegers F.canonicalTopologicalData) := by
    constructor
    intro x
    have hx := (LocalGalois.closureIntegers_integral F.Carrier (x : AlgebraicClosure F.Carrier)).mpr x.property
    have hx' : IsIntegral F.canonicalTopologicalData.Integers x :=
      (isIntegral_algHom_iff (show F.closureIntegers F.canonicalTopologicalData →ₐ[
        F.canonicalTopologicalData.Integers] AlgebraicClosure F.Carrier from
        IsScalarTower.toAlgHom _ _ _) (Subtype.val_injective)).mp hx
    exact hx'.tower_top
  apply (algebraMap_isIntegral_iff.mpr hi).isLocalHom
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : F.closureIntegers F.canonicalTopologicalData =>
    (z : AlgebraicClosure F.Carrier)) h

/-- Restriction into a finite Galois subfield preserves the actual residue kernel. -/
theorem absoluteFiniteRestriction_mem_inertia
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    absoluteFiniteRestriction F L σ ∈
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier := by
  let E := absoluteFiniteExtension F L
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  change residueHom E.canonicalTopologicalData F.Carrier (absoluteFiniteRestriction F L σ) = 1
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  apply (ResidueField.map (finiteClosureIntegerMap F L)).injective
  have hs : LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier) σ.val = 1 := σ.property
  have hx := DFunLike.congr_fun hs
    (residue _ (finiteClosureIntegerMap F L x))
  change residue _ (LocalGalois.integerAut F.Carrier (AlgebraicClosure F.Carrier)
    σ.val (finiteClosureIntegerMap F L x)) = residue _ (finiteClosureIntegerMap F L x) at hx
  change residue _ (finiteClosureIntegerMap F L
    (integerAutomorphism E.canonicalTopologicalData F.Carrier
      (absoluteFiniteRestriction F L σ) x)) = residue _ (finiteClosureIntegerMap F L x)
  rw [← hx]
  congr 1
  apply Subtype.ext
  exact σ.val.restrictNormal_commutes L (x : L)


/-- Actual restriction from absolute inertia, with its subgroup topologies. -/
def absoluteInertiaRestriction :
    F.absoluteInertia F.canonicalTopologicalData →ₜ*
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier where
  toMonoidHom := ((absoluteFiniteRestriction F L).toMonoidHom.comp
    (F.absoluteInertia F.canonicalTopologicalData).subtype).codRestrict _
      (absoluteFiniteRestriction_mem_inertia F L)
  continuous_toFun := ((absoluteFiniteRestriction F L).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem absoluteInertiaRestriction_coe
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    (absoluteInertiaRestriction F L σ : Gal(L/F.Carrier)) =
      absoluteFiniteRestriction F L σ := rfl

/-- Evaluation is restriction of the original automorphism on the same element. -/
theorem absoluteInertiaRestriction_apply
    (σ : F.absoluteInertia F.canonicalTopologicalData) (x : L) :
    ((absoluteInertiaRestriction F L σ).val x : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom σ.val (x : AlgebraicClosure F.Carrier) :=
  σ.val.restrictNormal_commutes L x

/-- The forward homomorphism of the published local inertia equivalence. -/
def weilInertiaProjection :
    localInertia F →ₜ* F.absoluteInertia F.canonicalTopologicalData :=
  ContinuousMonoidHom.toContinuousMonoidHom (localInertiaEquiv F)

@[simp] theorem weilInertiaProjection_coe (w : localInertia F) :
    (weilInertiaProjection F w : Field.absoluteGaloisGroup F.Carrier) =
      localProjection F w := rfl

/-- The specific arithmetic map used by finite-inertia presentations. -/
def weilInertiaRestriction : localInertia F →ₜ*
    inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  (absoluteInertiaRestriction F L).comp (weilInertiaProjection F)

@[simp] theorem weilInertiaRestriction_coe (w : localInertia F) :
    (weilInertiaRestriction F L w : Gal(L/F.Carrier)) =
      absoluteFiniteRestriction F L (localProjection F w) := rfl

theorem weilInertiaRestriction_apply (w : localInertia F) (x : L) :
    ((weilInertiaRestriction F L w).val x : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom (localProjection F w) (x : AlgebraicClosure F.Carrier) :=
  absoluteInertiaRestriction_apply F L (weilInertiaProjection F w) x

variable {L} {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}

/-- Restriction along an actual inclusion of finite Galois subfields. -/
def finiteGaloisRestriction (h : L ≤ M) : Gal(M/F.Carrier) →ₜ* Gal(L/F.Carrier) := by
  letI : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower F.Carrier L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact { toMonoidHom := AlgEquiv.restrictNormalHom L
          continuous_toFun := continuous_of_discreteTopology }

/-- The finite restriction evaluates via the actual inclusion. -/
theorem finiteGaloisRestriction_apply (h : L ≤ M) (σ : Gal(M/F.Carrier)) (x : L) :
    ((finiteGaloisRestriction F h σ) x : AlgebraicClosure F.Carrier) =
      (σ (IntermediateField.inclusion h x) : AlgebraicClosure F.Carrier) := by
  let : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower F.Carrier L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact congrArg (fun y : M => (y : AlgebraicClosure F.Carrier)) (σ.restrictNormal_commutes L x)

/-- Actual inclusions preserve the residue kernels under finite restriction. -/
theorem finiteGaloisRestriction_mem_inertia (h : L ≤ M)
    (σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) :
    finiteGaloisRestriction F h σ ∈
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier := by
  let EL := absoluteFiniteExtension F L
  let EM := absoluteFiniteExtension F M
  let f : EL.Carrier →ₐ[Padic p] EM.Carrier := (IntermediateField.inclusion h).restrictScalars _
  change residueHom EL.canonicalTopologicalData F.Carrier (finiteGaloisRestriction F h σ) = 1
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  apply (extensionResidueMap EL EM f).injective
  have hs := DFunLike.congr_fun σ.property
    (residue _ (extensionIntegerMap EL EM f x))
  change residue _ (integerAutomorphism EM.canonicalTopologicalData F.Carrier σ.val
    (extensionIntegerMap EL EM f x)) = residue _ (extensionIntegerMap EL EM f x) at hs
  change residue _ (extensionIntegerMap EL EM f
    (integerAutomorphism EL.canonicalTopologicalData F.Carrier
      (finiteGaloisRestriction F h σ) x)) = residue _ (extensionIntegerMap EL EM f x)
  rw [← hs]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact finiteGaloisRestriction_apply F h σ.val (x : L)

/-- Restriction between the two actual finite inertia groups. -/
def finiteInertiaRestriction (h : L ≤ M) :
    inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier →ₜ*
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier where
  toMonoidHom := ((finiteGaloisRestriction F h).toMonoidHom.comp
    (inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier).subtype).codRestrict _
      (finiteGaloisRestriction_mem_inertia F h)
  continuous_toFun := ((finiteGaloisRestriction F h).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem finiteInertiaRestriction_coe (h : L ≤ M)
    (σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) :
    (finiteInertiaRestriction F h σ : Gal(L/F.Carrier)) = finiteGaloisRestriction F h σ := rfl

/-- The absolute restriction square commutes on the actual field carriers. -/
theorem finiteInertiaRestriction_absolute (h : L ≤ M)
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    finiteInertiaRestriction F h (absoluteInertiaRestriction F M σ) =
      absoluteInertiaRestriction F L σ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (finiteGaloisRestriction_apply F h _ x).trans
    ((absoluteInertiaRestriction_apply F M σ (IntermediateField.inclusion h x)).trans
      (absoluteInertiaRestriction_apply F L σ x).symm)

/-- The Weil inertia restriction square commutes as well. -/
theorem finiteInertiaRestriction_weil (h : L ≤ M) (w : localInertia F) :
    finiteInertiaRestriction F h (weilInertiaRestriction F M w) = weilInertiaRestriction F L w :=
  finiteInertiaRestriction_absolute F h (weilInertiaProjection F w)

/-- A larger actual finite subextension has a smaller restriction kernel. -/
theorem weilInertiaRestriction_ker_le (h : L ≤ M) :
    (weilInertiaRestriction F M).toMonoidHom.ker ≤
      (weilInertiaRestriction F L).toMonoidHom.ker := by
  intro w hw
  change weilInertiaRestriction F L w = 1
  rw [← finiteInertiaRestriction_weil F h, show weilInertiaRestriction F M w = 1 from hw, map_one]

variable (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))

/-- The genuine representation restricted to the actual local Weil inertia. -/
abbrev localInertiaRepresentation : Representation ℂ (localInertia F) A :=
  A.representation.comp (localInertia F).subtype

/-- Data presenting one representation on an actual finite Galois inertia group.
Surjectivity and universal presentation existence are not fields of this structure. -/
structure FiniteInertiaPresentation where
  extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)
  kernel_le : (weilInertiaRestriction F extension).toMonoidHom.ker ≤
    (localInertiaRepresentation F A).ker

namespace FiniteInertiaPresentation

variable {F A} (P : FiniteInertiaPresentation F A)

/-- Descent along the specific arithmetic restriction, with surjectivity explicit. -/
def representation (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) :
    Representation ℂ (inertia (absoluteFiniteExtension F P.extension).canonicalTopologicalData
      F.Carrier) A :=
  descendInertiaRepresentation _ F.Carrier (weilInertiaRestriction F P.extension).toMonoidHom
    hsurj (localInertiaRepresentation F A) P.kernel_le

@[simp] theorem representation_apply
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) (w : localInertia F) :
    P.representation hsurj (weilInertiaRestriction F P.extension w) = A.representation w :=
  descendInertiaRepresentation_apply _ _ _ _ _ _ w

/-- The existing Artin expression at this particular actual presentation. -/
def artinConductor (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) : ℚ :=
  artinConductorOfQuotient _ F.Carrier (weilInertiaRestriction F P.extension).toMonoidHom
    hsurj (localInertiaRepresentation F A) P.kernel_le

/-- The existing Swan expression at this particular actual presentation. -/
def swanConductor (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) : ℚ :=
  swanConductorOfQuotient _ F.Carrier (weilInertiaRestriction F P.extension).toMonoidHom
    hsurj (localInertiaRepresentation F A) P.kernel_le

/-- Enlarging the actual finite Galois subfield preserves the presentation condition. -/
def refine (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) : FiniteInertiaPresentation F A where
  extension := M
  kernel_le := (weilInertiaRestriction_ker_le F h).trans P.kernel_le

/-- Pull the descended action back along actual finite-inertia restriction. -/
def pullback (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) :
    Representation ℂ (inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) A :=
  (P.representation hsurj).comp (finiteInertiaRestriction F h).toMonoidHom

@[simp] theorem pullback_apply
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) (w : localInertia F) :
    P.pullback hsurj M h (weilInertiaRestriction F M w) = A.representation w := by
  change P.representation hsurj
    (finiteInertiaRestriction F h (weilInertiaRestriction F M w)) = _
  rw [finiteInertiaRestriction_weil, representation_apply]

/-- When descent at the refinement is available, it is this actual pullback. -/
theorem representation_refine
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) (hM : Function.Surjective (weilInertiaRestriction F M)) :
    (P.refine M h).representation hM = P.pullback hsurj M h := by
  ext g : 1
  obtain ⟨w, rfl⟩ := hM g
  exact (representation_apply (P.refine M h) hM w).trans (P.pullback_apply hsurj M h w).symm

end FiniteInertiaPresentation

/-- A common refinement consists of actual inclusions into an actual finite Galois field.
No equality of conductor sums, ramification indices, or representations is supplied. -/
structure FiniteInertiaCommonRefinement (P Q : FiniteInertiaPresentation F A) where
  extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)
  left_le : P.extension ≤ extension
  right_le : Q.extension ≤ extension

namespace FiniteInertiaCommonRefinement

/-- The compositum of the two actual finite Galois subfields is a common refinement. -/
def compositum (P Q : FiniteInertiaPresentation F A) : FiniteInertiaCommonRefinement F A P Q where
  extension := P.extension ⊔ Q.extension
  left_le := le_sup_left
  right_le := le_sup_right

variable {F A} {P Q : FiniteInertiaPresentation F A} (R : FiniteInertiaCommonRefinement F A P Q)

/-- The left descended action pulled to the actual common field. -/
def leftRepresentation (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :=
  P.pullback hP R.extension R.left_le

/-- The right descended action pulled to the actual common field. -/
def rightRepresentation (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)) :=
  Q.pullback hQ R.extension R.right_le

@[simp] theorem leftRepresentation_apply
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) (w : localInertia F) :
    R.leftRepresentation hP (weilInertiaRestriction F R.extension w) = A.representation w :=
  P.pullback_apply hP R.extension R.left_le w

@[simp] theorem rightRepresentation_apply
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)) (w : localInertia F) :
    R.rightRepresentation hQ (weilInertiaRestriction F R.extension w) = A.representation w :=
  Q.pullback_apply hQ R.extension R.right_le w

/-- Surjectivity at the common field makes the two genuine pullbacks equal. -/
theorem representations_eq
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension))
    (hR : Function.Surjective (weilInertiaRestriction F R.extension)) :
    R.leftRepresentation hP = R.rightRepresentation hQ := by
  ext g : 1
  obtain ⟨w, rfl⟩ := hR g
  exact (R.leftRepresentation_apply hP w).trans (R.rightRepresentation_apply hQ w).symm

end FiniteInertiaCommonRefinement

end Langlands.Ramification.Padic
