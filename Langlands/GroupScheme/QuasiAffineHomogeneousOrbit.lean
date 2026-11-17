import Langlands.GroupScheme.RelativeQuasiAffineHomogeneousQuotient

/-! # Homogeneous quotients from quasi-affine orbit targets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.RelativeHomogeneousQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Over an affine base, a finite type scheme admitting a monomorphism into
a quasi-affine scheme is itself quasi-affine. -/
theorem quasiAffine_of_mono_to_quasiAffine
    {S : Scheme.{u}} [IsAffine S] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Y.left.IsQuasiAffine]
    (e : X ⟶ Y) [Mono e.left] : X.left.IsQuasiAffine := by
  have : LocallyOfFiniteType (e.left ≫ Y.hom) := by
    rw [Over.w e]
    infer_instance
  let : LocallyOfFiniteType e.left := locallyOfFiniteType_of_comp e.left Y.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite
    (e.left ≫ Y.left.toSpecΓ)

/-- An exact-fiber map into an actual quasi-affine scheme constructs an
actual smooth quasi-affine homogeneous quotient over an affine base. -/
theorem exists_quasiAffine_quotient_of_quasiAffine_map_kernel
    {S : Scheme.{u}} [IsAffine S] {G H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) [Y.left.IsQuasiAffine] (r : G.X ⟶ Y)
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    ∃ Q : HomogeneousQuotient i, Smooth Q.scheme.hom ∧ Q.scheme.left.IsQuasiAffine := by
  let D := quotientEmbeddingOfMapKernel i hi hH Y r hker
  let : Mono D.embedding.left := D.mono_embedding
  let : LocallyOfFiniteType D.quotient.scheme.hom := D.quotient.locallyOfFiniteType
  let : QuasiCompact D.quotient.scheme.hom := D.quotient.quasiCompact
  exact ⟨D.quotient, D.quotient.smooth_structure, quasiAffine_of_mono_to_quasiAffine D.embedding⟩

/-- Choose the quotient constructed from an exact-fiber quasi-affine orbit map. -/
def quasiAffineQuotientOfQuasiAffineMapKernel
    {S : Scheme.{u}} [IsAffine S] {G H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) [Y.left.IsQuasiAffine] (r : G.X ⟶ Y)
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    {Q : HomogeneousQuotient i // Smooth Q.scheme.hom ∧ Q.scheme.left.IsQuasiAffine} :=
  ⟨_, (exists_quasiAffine_quotient_of_quasiAffine_map_kernel i hi hH Y r hker).choose_spec⟩

end Langlands.GroupScheme.RelativeHomogeneousQuotient
