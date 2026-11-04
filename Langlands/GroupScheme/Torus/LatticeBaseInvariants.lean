import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Mathlib.RepresentationTheory.Invariants

/-! # Canonical base change into Galois-invariant lattices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {B S : Scheme.{u}} (b : S ⟶ B) (T : CommGroupScheme B)

namespace cocharacterLattice

/-- A base-changed cocharacter evaluates the original cocharacter on the same unit. -/
theorem baseChange_points (ν : cocharacterLattice T) (U : Over S)
    (x : U ⟶ (Gm S).X) :
    baseChangePointsEquiv b T.toGrp U
        (x ≫ (CommGroupScheme.groupHom (baseChange b T ν)).hom.hom) =
      (Gm.pointsEquiv B ((Over.map b).obj U)).symm (Gm.pointsEquiv S U x) ≫
        (CommGroupScheme.groupHom ν).hom.hom := by
  change baseChangePointsEquiv b T.toGrp U
    ((x ≫ (Gm.baseChangeIso b).inv.hom.hom) ≫
      ((Over.pullback b).mapGrp.map (CommGroupScheme.groupHom ν)).hom.hom) = _
  rw [baseChangePointsEquiv_comp]
  congr 1
  apply (Gm.pointsEquiv B ((Over.map b).obj U)).injective
  rw [MulEquiv.apply_symm_apply]
  exact Gm.baseChangeUnitsEquiv_baseChangeIso_inv b U x

/-- Canonical base change is fixed by every endomorphism of the new base over the old one. -/
theorem transport_baseChange (a : S ⟶ S) (ha : a ≫ b = b) (ν : cocharacterLattice T) :
    transport b a ha T (baseChange b T ν) = baseChange b T ν := by
  apply ext_points
  intro U x
  apply (baseChangePointsEquiv b T.toGrp U).injective
  rw [groupHom_transport, transportCocharacter_points, baseChange_points,
    baseChange_points, MulEquiv.apply_symm_apply]
  rw [← Category.assoc]
  congr 1
  apply (Gm.pointsEquiv B ((Over.map b).obj U)).injective
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  change Units.map (𝟙 U.left : U.left ⟶ U.left).appTop.hom.toMonoidHom _ = _
  simp

end cocharacterLattice

end BaseChange

section FaithfulCharacterBaseChange

variable {B S : Scheme.{u}} (b : S ⟶ B) [(Over.pullback b).Faithful]

/-- Faithful pullback detects equality of actual rational characters. -/
theorem rationalCharacters.baseChange_injective (G : GroupScheme B) :
    Function.Injective (rationalCharacters.baseChange b (G := G)) := by
  intro χ ψ h
  change χ.toMul = ψ.toMul
  apply (GroupScheme.baseChange b).map_injective
  exact (cancel_mono (Gm.baseChangeIso b).hom).mp (congrArg Additive.toMul h)

/-- Faithful pullback detects equality in the actual character lattice. -/
theorem characterLattice.baseChange_injective (T : CommGroupScheme B) :
    Function.Injective (characterLattice.baseChange b T) :=
  rationalCharacters.baseChange_injective b T.toGrp

end FaithfulCharacterBaseChange

section Galois

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Canonical base change of a cocharacter is fixed by every coefficient automorphism. -/
theorem cocharacterLattice.galoisRepresentation_baseChange (σ : K ≃ₐ[k] K)
    (ν : cocharacterLattice T) :
    cocharacterLattice.galoisRepresentation k K T σ
        (cocharacterLattice.baseChange (algebraBaseMap k K) T ν) =
      cocharacterLattice.baseChange (algebraBaseMap k K) T ν :=
  cocharacterLattice.transport_baseChange (algebraBaseMap k K) T
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) ν

namespace characterLattice

/-- Canonical base change, with codomain the invariant part of the actual character lattice. -/
def baseChangeToInvariants : characterLattice T →ₗ[ℤ]
    (galoisRepresentation k K T).invariants :=
  (baseChange (algebraBaseMap k K) T).toIntLinearMap.codRestrict _
    (fun χ σ => galoisRepresentation_baseChange k K T σ χ)

@[simp] theorem coe_baseChangeToInvariants (χ : characterLattice T) :
    (baseChangeToInvariants k K T χ :
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) =
      baseChange (algebraBaseMap k K) T χ := rfl

end characterLattice

namespace cocharacterLattice

/-- Canonical base change, with codomain the invariant part of the actual cocharacter lattice. -/
def baseChangeToInvariants : cocharacterLattice T →ₗ[ℤ]
    (galoisRepresentation k K T).invariants :=
  (baseChange (algebraBaseMap k K) T).toIntLinearMap.codRestrict _
    (fun ν σ => galoisRepresentation_baseChange k K T σ ν)

@[simp] theorem coe_baseChangeToInvariants (ν : cocharacterLattice T) :
    (baseChangeToInvariants k K T ν :
      cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) =
      baseChange (algebraBaseMap k K) T ν := rfl

end cocharacterLattice

end Galois

section Fields

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Actual rational characters inject under every field extension. -/
theorem rationalCharacters.algebraBaseChange_injective
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    Function.Injective (rationalCharacters.baseChange (algebraBaseMap k K) (G := G)) := by
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  exact rationalCharacters.baseChange_injective (algebraBaseMap k K) G

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The actual character lattice injects under every field extension. -/
theorem characterLattice.algebraBaseChange_injective :
    Function.Injective (characterLattice.baseChange (algebraBaseMap k K) T) :=
  rationalCharacters.algebraBaseChange_injective k K T.toGrp

/-- The actual cocharacter lattice injects under every field extension. -/
theorem cocharacterLattice.algebraBaseChange_injective :
    Function.Injective (cocharacterLattice.baseChange (algebraBaseMap k K) T) :=
  GaloisCocharacterDescent.baseChangeCocharacter_injective k K T.toGrp

/-- Canonical character base change embeds into the Galois-invariant submodule. -/
theorem characterLattice.baseChangeToInvariants_injective :
    Function.Injective (characterLattice.baseChangeToInvariants k K T) := by
  intro χ ψ h
  exact characterLattice.algebraBaseChange_injective k K T (congrArg Subtype.val h)

/-- Canonical cocharacter base change embeds into the Galois-invariant submodule. -/
theorem cocharacterLattice.baseChangeToInvariants_injective :
    Function.Injective (cocharacterLattice.baseChangeToInvariants k K T) := by
  intro ν ν' h
  exact cocharacterLattice.algebraBaseChange_injective k K T (congrArg Subtype.val h)

end Fields

end Langlands.GroupScheme
