import Langlands.GroupScheme.HomogeneousCharacterLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Finite character-covariant functions on proper homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.UnitCocycleDescent

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
  (D : HomogeneousQuotient i)

/-- Pullback along the quotient respects the actual field structure maps. -/
theorem structureRingHom_projection :
    structureRingHom D.scheme.hom ≫ D.projection.left.appTop =
      structureRingHom G.X.hom := by
  unfold structureRingHom
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w D.projection]

/-- Restriction of quotient scalars gives the usual field action on functions. -/
theorem projection_field_smul (r : k) (f : Γ(G.X.left, ⊤)) :
    (show Γ(G.X.left, ⊤) from
      (structureRingHom D.scheme.hom r) •
        (show Γ(pushforwardUnit D.projection.left, ⊤) from f)) =
    (show Γ(G.X.left, ⊤) from
      r • (show ((algΓ (CommRingCat.of k)).obj G.X).unop from f)) := by
  change D.projection.left.appTop (structureRingHom D.scheme.hom r) * f =
    (structureRingHom G.X.hom r) * f
  exact congrArg (fun z : Γ(G.X.left, ⊤) => z * f)
    (congrArg (fun z : CommRingCat.of k ⟶ Γ(G.X.left, ⊤) => z r)
      (structureRingHom_projection i D))

/-- The entire space of covariant regular functions with the actual field scalars. -/
def rightCharacterCovariantSpace [Mono i.hom.hom] (χ : rationalCharacters H) :
    Submodule k ((algΓ (CommRingCat.of k)).obj G.X).unop where
  carrier := {f | IsRightCharacterCovariant i χ f}
  zero_mem' := (rightCharacterCovariantSubmodule i D χ).zero_mem
  add_mem' := (rightCharacterCovariantSubmodule i D χ).add_mem
  smul_mem' r f hf := by
    have h := (rightCharacterCovariantSubmodule i D χ).smul_mem
      (structureRingHom D.scheme.hom r) hf
    change IsRightCharacterCovariant i χ _ at h ⊢
    exact (congrArg (IsRightCharacterCovariant i χ)
      (projection_field_smul i D r f)).mp h

@[simp] theorem mem_rightCharacterCovariantSpace [Mono i.hom.hom]
    (χ : rationalCharacters H) (f : ((algΓ (CommRingCat.of k)).obj G.X).unop) :
    f ∈ rightCharacterCovariantSpace i D χ ↔ IsRightCharacterCovariant i χ f := Iff.rfl

/-- Actual line-bundle sections over the field identify with every covariant function. -/
def characterFieldSectionsEquiv [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) :
    (relativeGlobalSections D.scheme.hom).obj (characterLineBundle i D χ).obj ≃ₗ[k]
      rightCharacterCovariantSpace i D χ where
  toFun s := ⟨s.1, (isCocycleSection_top_iff i D χ s.1).mp s.2⟩
  invFun f := ⟨f.1, (isCocycleSection_top_iff i D χ f.1).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    apply Subtype.ext
    exact projection_field_smul i D r s.1

@[simp] theorem characterFieldSectionsEquiv_apply [Mono i.hom.hom]
    [IsAffineHom G.X.hom] (χ : rationalCharacters H)
    (s : (relativeGlobalSections D.scheme.hom).obj (characterLineBundle i D χ).obj) :
    (characterFieldSectionsEquiv i D χ s).1 = s.1 := rfl

/-- Properness gives finite global sections of the actual descended character bundle. -/
theorem finite_characterFieldSections [Mono i.hom.hom] [IsAffineHom G.X.hom]
    [IsProper D.scheme.hom] (χ : rationalCharacters H) :
    Module.Finite k
      ((relativeGlobalSections D.scheme.hom).obj (characterLineBundle i D χ).obj) := by
  let L := characterLineBundle i D χ
  have hf := properCoherentCohomologyFinite k D.scheme.left D.scheme.hom inferInstance
    L.obj L.property.isQuasicoherent (hasFiniteAffineSections_lineBundle L)
  let := hf.1 0
  exact Module.Finite.equiv ((relativeCohomologyZeroIso D.scheme.hom).app L.obj).toLinearEquiv

/-- The whole covariant function space is finite when the actual quotient is proper. -/
theorem finite_rightCharacterCovariantSpace [Mono i.hom.hom] [IsAffineHom G.X.hom]
    [IsProper D.scheme.hom] (χ : rationalCharacters H) :
    Module.Finite k (rightCharacterCovariantSpace i D χ) := by
  let := finite_characterFieldSections i D χ
  exact Module.Finite.equiv (characterFieldSectionsEquiv i D χ)

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
