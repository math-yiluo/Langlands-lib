import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.ProjectiveQuotientEmbedding
import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction

/-! # Actual projective data for a supplied proper homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.HomogeneousQuotient

variable {k : Type u} [Field k]
  {G B : GroupScheme (Spec (CommRingCat.of k))}
  (b : B ⟶ G) {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  [Flat q.left] [QuasiCompact q.left] [Surjective q.left]
  (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)

/-- An actual matrix representation and equivariant projective closed embedding
of the supplied quotient, with its exact all-test coordinate-line stabilizer. -/
structure ProjectiveEmbeddingData where
  dimension : ℕ
  coordinate : Fin (dimension + 1)
  representation : MatrixRepresentation G (Fin (dimension + 1))
  line_stabilizer :
    ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier T ↔
        ∃ c : Γ(T.left, ⊤)ˣ,
          (representation.pointMatrix T x :
            Matrix (Fin (dimension + 1)) (Fin (dimension + 1)) Γ(T.left, ⊤)) *ᵥ
              Pi.single coordinate 1 =
            (c : Γ(T.left, ⊤)) • (Pi.single coordinate (1 : Γ(T.left, ⊤)) :
              Fin (dimension + 1) → Γ(T.left, ⊤))
  embedding : Q ⟶ ProjectiveOrbit.ambient dimension (CommRingCat.of k)
  orbit_fac : q ≫ embedding =
    ProjectiveOrbit.lineOrbitMap dimension coordinate representation
  embedding_closed : IsClosedImmersion embedding.left
  equivariant : ProjectiveOrbit.IsMatrixEquivariant
    (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib)
    representation embedding

/-- Restricting the constructed representation and action preserves their
actual matrix equivariance. -/
theorem ProjectiveEmbeddingData.restrict_equivariant
    (D : ProjectiveEmbeddingData b q hfib)
    {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) :
    ProjectiveOrbit.IsMatrixEquivariant
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict i)
      (D.representation.restrict i) D.embedding :=
  D.equivariant.restrict i

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth q.left] [IsProper Q.hom]

/-- A supplied proper smooth exact quotient of a smooth affine group has
actual projective data, with no supplied representation or subgroup smoothness. -/
def projectiveEmbeddingData (hb : IsClosedSubgroup b) :
    ProjectiveEmbeddingData b q hfib := Classical.choice (by
  have : IsClosedImmersion b.hom.hom.left := hb
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Smooth B.X.hom := smooth_subgroup_of_smooth_quotient G B b q hfib
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G B b hb
  exact ⟨{
      dimension := n
      coordinate := j
      representation := ρ
      line_stabilizer := hρ
      embedding := ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib
      orbit_fac := ProjectiveOrbit.fac_quotientOrbitMap n b j ρ hρ q hfib
      embedding_closed :=
        ProjectiveOrbit.isClosedImmersion_quotientOrbitMap n b j ρ hρ q hfib hb inferInstance
      equivariant := ProjectiveOrbit.isMatrixEquivariant_quotientOrbitMap
        n b j ρ hρ q hfib
        (Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib)
        (fun _ g h => Dynamic.flagQuotientSchemeAction_act_lift
          G (SubgroupFunctor.range b) q hfib g h) }⟩)

end Langlands.GroupScheme.HomogeneousQuotient
