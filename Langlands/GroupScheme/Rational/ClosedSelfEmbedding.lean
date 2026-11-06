import Langlands.GroupScheme.ImageGenerationNoetherian
import Langlands.GroupScheme.Rational.SplitRankTransport
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Closed self-embeddings of affine algebraic groups

A closed immersion of an affine scheme of finite type over a field into itself is an
isomorphism: on global sections it is a surjective endomorphism of a Noetherian ring,
hence injective. Consequently a homomorphism of an affine algebraic group over a field
to itself that is a closed subgroup is an isomorphism.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- A closed immersion of an affine scheme, locally of finite type over a field, into itself
is an isomorphism. -/
theorem isIso_of_isClosedImmersion_self {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [IsAffine X]
    (g : X ⟶ X) [IsClosedImmersion g] : IsIso g := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  exact GroupScheme.ImageGeneration.isIso_of_isClosedImmersion_endo g

namespace GroupScheme

variable {k : Type u} [Field k] {M : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed-subgroup endomorphism of an affine group scheme locally of finite type over a
field is an isomorphism. -/
theorem isIso_of_isClosedSubgroup_self [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    (f : M ⟶ M) (hf : IsClosedSubgroup f) : IsIso f := by
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : IsClosedImmersion f.hom.hom.left := hf
  have : IsIso f.hom.hom.left := isIso_of_isClosedImmersion_self M.X.hom _
  have : IsIso f.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp (show IsIso f.hom.hom.left from inferInstance)
  have : IsIso f.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp (show IsIso f.hom.hom from inferInstance)
  exact (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp (show IsIso f.hom from inferInstance)

/-- A closed-subgroup endomorphism of a connected reductive group over a field is an
isomorphism. -/
theorem IsConnectedReductive.isIso_of_isClosedSubgroup (hM : IsConnectedReductive M)
    (f : M ⟶ M) (hf : IsClosedSubgroup f) : IsIso f := by
  have := hM.smooth
  have := hM.isAffineHom
  exact isIso_of_isClosedSubgroup_self f hf

end GroupScheme

end Langlands
