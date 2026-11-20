import Langlands.GroupScheme.SimplyConnected.AbsoluteCenterCharacterRestriction
import Langlands.GroupScheme.Torus.DiagonalizableClosedCharacterSurjection
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The full centre character group as an integral quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace characterLattice

open MultiplicativeTypeGaloisExactness

/-- Restriction onto a closed subgroup of a split torus is surjective on characters. -/
theorem precompose_surjective_of_closedSubgroup_splitTorus
    {k : Type u} [Field k] {Z T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : Z ⟶ T) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup (CommGroupScheme.groupHom i)) :
    Function.Surjective (precompose i) := by
  classical
  obtain ⟨Λ, _, _, ⟨eZ⟩⟩ := exists_diagonalizableIso_of_isClosedSubgroup_splitTorus
    hT (CommGroupScheme.groupHom i) hi
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let eT := e ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  obtain ⟨p, hp⟩ := (DiagonalizableCharacter.restrictMap_bijective k Λ (I → ℤ)).2
    (eZ.inv ≫ CommGroupScheme.groupHom i ≫ eT.hom)
  have hp' : Diagonalizable.restrictMap (CommRingCat.of k) p =
      eZ.inv ≫ CommGroupScheme.groupHom i ≫ eT.hom := hp
  have hclosed : IsClosedSubgroup (Diagonalizable.restrictMap (CommRingCat.of k) p) := by
    rw [hp']
    exact IsClosedSubgroup.iso_comp eZ.symm (hi.comp_iso eT)
  have hsurj := Diagonalizable.surjective_of_isClosedSubgroup_restrictMap p hclosed
  let jZ := CommGroupScheme.isoOfGroupIso eZ
  let jT := CommGroupScheme.isoOfGroupIso eT
  let ΦZ := (DiagonalizableCharacter.evalCharacterEquiv k Λ).trans (characterLattice.congr jZ).symm
  let ΦT := (DiagonalizableCharacter.evalCharacterEquiv k (I → ℤ)).trans (characterLattice.congr jT).symm
  have hp'' : restrictHom k p = jZ.inv ≫ i ≫ jT.hom := congrArg Additive.ofMul hp'
  have hcomp (m : I → ℤ) : precompose i (ΦT m) = ΦZ (p m) := by
    change i ≫ jT.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of k) (I → ℤ) m =
      jZ.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ (p m)
    rw [← restrictHom_comp_evalCharacter k p m, hp'']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  intro χ
  obtain ⟨m, hm⟩ := hsurj (ΦZ.symm χ)
  exact ⟨ΦT m, (hcomp m).trans ((congrArg ΦZ hm).trans (ΦZ.apply_symm_apply χ))⟩

end characterLattice

namespace TitsIndexData

open Langlands.LinearAlgebra

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "Ω" => SeparableClosure K
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap K Ω)

/-- The full centre is a closed subgroup of the specified ground-field torus. -/
theorem toralCenter_isClosedSubgroup :
    IsClosedSubgroup (CommGroupScheme.groupHom d.toralCenter.torusMap) := by
  let i := d.pinning.inclusion
  let j := CommGroupScheme.groupHom d.toralCenter.torusMap
  let : IsClosedImmersion i.hom.hom.left := d.maximalTorus.2.1
  let : IsClosedImmersion (j.hom.hom.left ≫ i.hom.hom.left) := d.toralCenter.isCenter.1
  exact IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left i.hom.hom.left

/-- The actual centre in the chosen torus is of multiplicative type. -/
theorem toralCenter_isMultiplicativeType : IsMultiplicativeType d.toralCenter.group.toGrp :=
  d.maximalTorus.1.isMultiplicativeType.of_isClosedSubgroup _ d.toralCenter_isClosedSubgroup

/-- Any actual representative of the full centre is isomorphic to this toral centre. -/
def isoToralCenter {Z : GroupScheme (Spec (CommRingCat.of K))} {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : Z ≅ d.toralCenter.group.toGrp :=
  hz.isRepresentedBy.isoOfIsRepresentedBy d.toralCenter.isCenter.isRepresentedBy

/-- The actual centre characters over the separable closure all extend to the torus. -/
theorem centerCharacterRestriction_surjective : Function.Surjective d.centerCharacterRestriction := by
  change Function.Surjective (characterLattice.precompose ((BC).map d.toralCenter.torusMap))
  apply characterLattice.precompose_surjective_of_closedSubgroup_splitTorus _ d.pinning.isSplitTorus
  exact d.toralCenter_isClosedSubgroup.baseChange (algebraBaseMap K Ω)

/-- The character group of the geometric full centre is the quotient of the
actual absolute torus character lattice by the integral root span. -/
def centerCharacterQuotientEquiv :
    (characterLattice d.pinning.toSplitPinning.torus ⧸ d.pinning.rootDatum.rootSpan ℤ) ≃ₗ[ℤ]
      characterLattice ((BC).obj d.toralCenter.group) :=
  (Submodule.quotEquivOfEq _ _ d.ker_centerCharacterRestriction.symm).trans
    (d.centerCharacterRestriction.quotKerEquivOfSurjective d.centerCharacterRestriction_surjective)

@[simp]
theorem centerCharacterQuotientEquiv_mk (χ : characterLattice d.pinning.toSplitPinning.torus) :
    d.centerCharacterQuotientEquiv (Submodule.Quotient.mk χ) = d.centerCharacterRestriction χ := rfl

/-- On representatives, the full centre character quotient intertwines the
ordinary Galois actions of the torus and the centre. -/
theorem centerCharacterQuotientEquiv_galois_mk (σ : Ω ≃ₐ[K] Ω)
    (χ : characterLattice d.pinning.toSplitPinning.torus) :
    d.centerCharacterQuotientEquiv
        (Submodule.Quotient.mk (characterLattice.galoisRepresentation K Ω d.pinning.torus σ χ)) =
      characterLattice.galoisRepresentation K Ω d.toralCenter.group σ
        (d.centerCharacterQuotientEquiv (Submodule.Quotient.mk χ)) := by
  simp only [centerCharacterQuotientEquiv_mk]
  exact (characterLattice.galoisRepresentation_precompose K Ω d.toralCenter.torusMap σ χ).symm

end TitsIndexData

end Langlands.GroupScheme
