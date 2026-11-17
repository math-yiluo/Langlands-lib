import Langlands.GroupScheme.RelativeHomogeneousQuotientEmbedding
import Langlands.GroupScheme.HomogeneousQuotientSchemeAction
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart

/-! # Smooth quasi-affine relative homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeHomogeneousQuotient

variable {S : Scheme.{u}}

/-- A scheme of finite type over the base admitting a monomorphism into a
relatively affine scheme is quasi-affine above every affine base open. -/
theorem quasiAffineOver_of_mono {X Y : Over S}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsAffineHom Y.hom]
    (e : X ⟶ Y) [Mono e.left] :
    ∀ V : S.affineOpens, (X.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  have : LocallyOfFiniteType (e.left ≫ Y.hom) := by
    rw [Over.w e]
    infer_instance
  let : LocallyOfFiniteType e.left := locallyOfFiniteType_of_comp e.left Y.hom
  let : LocallyQuasiFinite e.left := inferInstance
  have hcomp : e.left ≫ Y.hom = X.hom := Over.w e
  intro V
  let U := Y.hom ⁻¹ᵁ (V : S.Opens)
  let : IsAffine U.toScheme := V.2.preimage Y.hom
  have hcompact : CompactSpace (X.hom ⁻¹ᵁ (V : S.Opens)).toScheme :=
    isCompact_iff_compactSpace.mp (X.hom.isCompact_preimage V.2.isCompact)
  have hopen : e.left ⁻¹ᵁ U = X.hom ⁻¹ᵁ (V : S.Opens) := by
    dsimp only [U]
    rw [← Scheme.Hom.comp_preimage, hcomp]
  let : CompactSpace (e.left ⁻¹ᵁ U).toScheme := by
    rw [hopen]
    exact hcompact
  have h := Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite
    (e.left ∣_ U)
  rwa [hopen] at h

/-- An exact-fiber map to a relatively affine scheme constructs a smooth
homogeneous quotient which is quasi-affine over every affine base open. -/
theorem exists_quasiAffine_quotient_of_map_kernel
    {G H : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) (r : G.X ⟶ Y) [IsAffineHom Y.hom]
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i,
      Smooth Q.scheme.hom ∧
        ∀ V : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  let D := quotientEmbeddingOfMapKernel i hi hH Y r hker
  let : Mono D.embedding.left := D.mono_embedding
  let : LocallyOfFiniteType D.quotient.scheme.hom := D.quotient.locallyOfFiniteType
  let : QuasiCompact D.quotient.scheme.hom := D.quotient.quasiCompact
  exact ⟨D.quotient, D.quotient.smooth_structure, quasiAffineOver_of_mono D.embedding⟩

/-- Choose the smooth quasi-affine homogeneous quotient supplied by an
exact-fiber map to a relatively affine scheme, together with its properties. -/
def quasiAffineQuotientOfMapKernel
    {G H : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (Y : Over S) (r : G.X ⟶ Y) [IsAffineHom Y.hom]
    (hker : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i //
      Smooth Q.scheme.hom ∧
        ∀ V : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine} :=
  ⟨_, (exists_quasiAffine_quotient_of_map_kernel i hi hH Y r hker).choose_spec⟩

end Langlands.GroupScheme.RelativeHomogeneousQuotient
