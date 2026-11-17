import Langlands.GroupScheme.Torus.CharacterActionNilpotentRigidity
import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.SchemeActionInvariantOpen
import Langlands.AlgebraicGeometry.AffinePointGluing
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Nilpotent rigidity of diagonalizable actions on arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {B : CommAlgCat.{u} R} {X : Over (Spec R)}
  (e : (algSpec R).obj (op B) ≅ X)

/-- Coordinates of points of an arbitrary affine scheme over the base. -/
def affinePointEquiv (C : CommAlgCat.{u} R) :
    (B ⟶ C) ≃ ((algSpec R).obj (op C) ⟶ X) where
  toFun x := (algSpec R).map x.op ≫ e.hom
  invFun x := (algSpec.fullyFaithful.preimage (x ≫ e.inv)).unop
  left_inv x := by
    apply Quiver.Hom.op_inj
    apply (algSpec R).map_injective
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp
  right_inv x := by
    change (algSpec R).map
      ((algSpec.fullyFaithful.preimage (x ≫ e.inv)).unop).op ≫ e.hom = x
    rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
    simp

theorem affinePointEquiv_comp {C D : CommAlgCat.{u} R} (x : B ⟶ C) (f : C ⟶ D) :
    affinePointEquiv e D (x ≫ f) =
      (algSpec R).map f.op ≫ affinePointEquiv e C x := by
  change (algSpec R).map (f.op ≫ x.op) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rfl

variable (a : SchemeAction (Diagonalizable.groupScheme R M).toGrp X)

/-- A categorical action on an affine scheme induces the natural coordinate action. -/
def ofSchemeAction : Action (M := M) B where
  act {C} t x := (affinePointEquiv e C).symm
    (a.act (characterPoint t) (affinePointEquiv e C x))
  one {C} x := by
    apply (affinePointEquiv e C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_one, a.act_one]
  mul {C} t s x := by
    apply (affinePointEquiv e C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_mul, a.act_mul]
  naturality {C D} f t x := by
    apply (affinePointEquiv e D).injective
    simp only [Equiv.apply_symm_apply, affinePointEquiv_comp,
      characterPoint_mapCharacter, ← a.naturality]

theorem affinePointEquiv_act {C : CommAlgCat.{u} R}
    (t : Multiplicative M →* Cˣ) (x : B ⟶ C) :
    affinePointEquiv e C ((ofSchemeAction e a).act t x) =
      a.act (characterPoint t) (affinePointEquiv e C x) :=
  Equiv.apply_symm_apply _ _

end CharacterAction

namespace SchemeAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {X : Over (Spec R)} (a : SchemeAction (Diagonalizable.groupScheme R M).toGrp X)
  (I : Ideal R) (hI : IsNilpotent I)

include hI

/-- The affine scheme case does not require a group structure on the acted-on scheme. -/
theorem act_eq_of_nilpotent_quotient_of_isAffine [IsAffine X.left]
    (h : ∀ C : CommAlgCat.{u} R,
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
      ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
        (x : (algSpec R).obj (op C) ⟶ X), a.act t x = x)
    {C : CommAlgCat.{u} R}
    (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
    (x : (algSpec R).obj (op C) ⟶ X) : a.act t x = x := by
  obtain ⟨⟨B⟩, ⟨e⟩⟩ := (essImage_algSpec (G := X)).mpr inferInstance
  have hc : ∀ C : CommAlgCat.{u} R,
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
      ∀ (t : Multiplicative M →* Cˣ) (x : B ⟶ C),
        (CharacterAction.ofSchemeAction e a).act t x = x := by
    intro C hC t x
    apply (CharacterAction.affinePointEquiv e C).injective
    rw [CharacterAction.affinePointEquiv_act]
    exact h C hC _ _
  obtain ⟨t, rfl⟩ := (Corepresented.affinePointsEquiv
    (Diagonalizable.functor R M) (Diagonalizable.grpCorepresentation R M) C).symm.surjective t
  obtain ⟨x, rfl⟩ := (CharacterAction.affinePointEquiv e C).surjective x
  rw [← CharacterAction.affinePointEquiv_act]
  rw [CharacterAction.act_eq_of_nilpotent_quotient _ I hI hc]

/-- The affine rigidity equality holds as an equality of actual action morphisms. -/
theorem hom_eq_snd_of_nilpotent_quotient_of_isAffine [IsAffine X.left]
    (h : ∀ C : CommAlgCat.{u} R,
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
      ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
        (x : (algSpec R).obj (op C) ⟶ X), a.act t x = x) :
    a.hom = snd _ _ := by
  apply Langlands.AlgebraicGeometry.AffinePoints.over_hom_ext
  intro C _ _ p
  have hp := a.act_eq_of_nilpotent_quotient_of_isAffine I hI h
    (C := CommAlgCat.of R C) (p ≫ fst _ _) (p ≫ snd _ _)
  simpa only [act, lift_comp_fst_snd] using hp

/-- Triviality on algebras annihilating a nilpotent ideal implies equality of
underlying point maps, for any scheme action. -/
theorem isInvariantOpen_of_nilpotent_quotient
    {H : GroupScheme (Spec R)} (a : SchemeAction H X)
    (h : ∀ C : CommAlgCat.{u} R,
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
      ∀ (t : (algSpec R).obj (op C) ⟶ H.X)
        (x : (algSpec R).obj (op C) ⟶ X), a.act t x = x)
    (V : X.left.Opens) : a.IsInvariantOpen V := by
  apply SetLike.ext
  intro z
  let P := H.X ⊗ X
  let K := P.left.residueField z
  let s := P.left.fromSpecResidueField z
  let : Algebra R K := (Spec.preimage (s ≫ P.hom)).hom.toAlgebra
  let C := CommAlgCat.of R K
  let p : (algSpec R).obj (op C) ⟶ P :=
    Over.homMk s (by
      change s ≫ P.hom = Spec.map (Spec.preimage (s ≫ P.hom))
      exact (Spec.map_preimage _).symm)
  have hC : ∀ r : R, r ∈ I → algebraMap R C r = 0 := by
    intro r hr
    obtain ⟨n, hn⟩ := hI
    have hrn : r ^ n = 0 := by
      have hmem := Ideal.pow_mem_pow hr n
      simpa only [hn, Ideal.zero_eq_bot, Submodule.mem_bot] using hmem
    apply isNilpotent_iff_eq_zero.mp
    refine ⟨n, ?_⟩
    rw [← map_pow, hrn, map_zero]
  have hp := h C hC (p ≫ fst _ _) (p ≫ snd _ _)
  rw [act, lift_comp_fst_snd] at hp
  have hz := congrArg (fun q : (algSpec R).obj (op C) ⟶ X =>
    q.left (IsLocalRing.closedPoint K)) hp
  change (s ≫ a.hom.left) (IsLocalRing.closedPoint K) =
    (s ≫ (snd H.X X).left) (IsLocalRing.closedPoint K) at hz
  simp only [Scheme.Hom.comp_apply, s, Scheme.fromSpecResidueField_apply] at hz
  change a.hom.left z ∈ V ↔ (snd H.X X).left z ∈ V
  rw [hz]

end SchemeAction

end Langlands.GroupScheme
