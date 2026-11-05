import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map

/-! # Base change of actual polynomial-projective embeddings -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

universe u

namespace ProjectiveSpace

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- The polynomial-Proj morphism associated to the given extension of base rings. -/
def baseChangeMap : ProjectiveSpace B n ⟶ ProjectiveSpace R n :=
  ProjSpace.map R B n

/-- Polynomial projective space commutes with this actual affine base change. -/
theorem baseChangeMap_isPullback :
    IsPullback (baseChangeMap R B n) (projectiveSpaceToSpec B n)
      (projectiveSpaceToSpec R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  have hR : projectiveSpaceToSpec R n = ProjSpace.π R n := by congr 1
  have hB : projectiveSpaceToSpec B n = ProjSpace.π B n := by congr 1
  simpa only [baseChangeMap, hR, hB] using ProjSpace.isPullback_map R B n

variable {R B n}
  {X X' : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of R)}
  {a : X' ⟶ X} {b : X' ⟶ Spec (CommRingCat.of B)}
  (sq : IsPullback a b p (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  (i : X ⟶ ProjectiveSpace R n)
  (hi : i ≫ projectiveSpaceToSpec R n = p)

/-- Lift a specified projective-space morphism to the specified base-changed scheme. -/
def baseChangeLift : X' ⟶ ProjectiveSpace B n :=
  (baseChangeMap_isPullback R B n).lift (a ≫ i) b
    (by rw [Category.assoc, hi]; exact sq.w)

@[reassoc (attr := simp)]
theorem baseChangeLift_toSpec :
    baseChangeLift sq i hi ≫ projectiveSpaceToSpec B n = b :=
  (baseChangeMap_isPullback R B n).lift_snd _ _ _

@[reassoc (attr := simp)]
theorem baseChangeLift_map :
    baseChangeLift sq i hi ≫ baseChangeMap R B n = a ≫ i :=
  (baseChangeMap_isPullback R B n).lift_fst _ _ _

/-- The lifted morphism is the actual base change of the original morphism. -/
theorem baseChangeLift_isPullback :
    IsPullback a (baseChangeLift sq i hi) i (baseChangeMap R B n) := by
  refine IsPullback.of_bot ?_ (baseChangeLift_map sq i hi).symm
    (baseChangeMap_isPullback R B n)
  simpa only [baseChangeLift_toSpec, hi] using sq

/-- A closed immersion remains a closed immersion on the specified base change. -/
instance baseChangeLift_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (baseChangeLift sq i hi) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (baseChangeLift_isPullback sq i hi) inferInstance

end ProjectiveSpace

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {X X' : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of R)}
  {a : X' ⟶ X} {b : X' ⟶ Spec (CommRingCat.of B)}

/-- An actual finite-projective-space embedding gives one on any specified affine
base change, using the same projective dimension. -/
theorem IsHProjective.of_isPullback
    (hp : IsHProjective p)
    (sq : IsPullback a b p (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    IsHProjective b := by
  obtain ⟨n, i, hclosed, hi⟩ := hp
  have : IsClosedImmersion i := hclosed
  exact ⟨n, ProjectiveSpace.baseChangeLift sq i hi, inferInstance,
    ProjectiveSpace.baseChangeLift_toSpec sq i hi⟩

/-- A closed immersion into finite projective space over the given affine base
is proper over that same base. -/
theorem IsHProjective.isProper (hp : IsHProjective p) : IsProper p := by
  obtain ⟨n, i, hclosed, hi⟩ := hp
  have : IsClosedImmersion i := hclosed
  rw [← hi]
  infer_instance

end Langlands.AlgebraicGeometry
