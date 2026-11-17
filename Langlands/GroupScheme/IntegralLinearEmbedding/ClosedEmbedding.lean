import Langlands.GroupScheme.IntegralLinearEmbedding.FiniteSubcomodule
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Closed linear embeddings of flat affine groups over principal ideal domains -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralLinearEmbedding

open AffineLinearEmbedding

/-- A finite-rank representation of an actual group scheme that is a closed immersion. -/
structure ClosedEmbedding {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) where
  /-- The rank of the free representation module. -/
  rank : ℕ
  /-- The representation into the corresponding general linear group. -/
  representation : MatrixRepresentation G (Fin rank)
  /-- The representation is a closed immersion of group schemes. -/
  closed : IsClosedSubgroup representation

/-- A flat, finite-type algebra corepresenting a group functor over a PID gives a closed
linear embedding of the corepresented group scheme. -/
theorem exists_corepresented_closedEmbedding {R : CommRingCat.{u}} [IsDomain R]
    [IsPrincipalIdealRing R] {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    [Module.Flat R B] [Algebra.FiniteType R B] :
    Nonempty (ClosedEmbedding (Corepresented.groupScheme F e)) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := B)
  let := (bialgebra e).toCoalgebra
  obtain ⟨N, M, hcomul, hcounit, hspan⟩ :=
    exists_matrix_coefficients_of_flat (R := R) (B := B) s
  have hgen : Algebra.adjoin R
      (Set.range fun p : Fin N × Fin N => M p.1 p.2) = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Algebra.adjoin_le fun b hb => Algebra.span_le_adjoin _ _ (hspan hb)
  exact ⟨⟨N, toGLHom e M hcomul hcounit,
    isClosedSubgroup_toGLHom e M hcomul hcounit hgen⟩⟩

/-- Flatness transported to an affine coordinate algebra through an isomorphism over the
base. -/
theorem flat_of_iso {R : CommRingCat.{u}} {X : Over (Spec R)} [Flat X.hom]
    (W : (CommAlgCat.{u} R)ᵒᵖ) (ψ : (algSpec R).obj W ≅ X) :
    Module.Flat R W.unop := by
  have : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hflat : Flat ((algSpec R).obj W).hom := by
    rw [← Over.w ψ.hom]
    infer_instance
  change @Flat (Spec (CommRingCat.of W.unop)) (Spec (CommRingCat.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R W.unop))) at hflat
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hflat
  exact RingHom.flat_algebraMap_iff.mp hflat

/-- Every flat affine group of finite type over a PID has a closed linear embedding. -/
theorem exists_closedEmbedding {R : CommRingCat.{u}} [IsDomain R]
    [IsPrincipalIdealRing R] (G : GroupScheme (Spec R)) [Flat G.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    Nonempty (ClosedEmbedding G) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨W, ⟨ψ⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  have : Algebra.FiniteType R W.unop := AffineCorepresentation.finiteType_of_iso W ψ
  have : Module.Flat R W.unop := flat_of_iso W ψ
  obtain ⟨D⟩ := exists_corepresented_closedEmbedding (AffineCorepresentation.corep G ψ)
  refine ⟨⟨D.rank, AffineCorepresentation.toModel G ψ ≫ D.representation, ?_⟩⟩
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  have hψ : IsClosedImmersion ψ.inv.left := inferInstance
  exact @IsClosedImmersion.comp _ _ _ ψ.inv.left D.representation.hom.hom.left hψ D.closed

/-- A chosen closed linear embedding of a flat affine finite-type group over a PID. -/
def closedEmbedding {R : CommRingCat.{u}} [IsDomain R] [IsPrincipalIdealRing R]
    (G : GroupScheme (Spec R)) [Flat G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : ClosedEmbedding G :=
  (exists_closedEmbedding G).some

/-- The chosen representation is a closed immersion. -/
theorem closedEmbedding_isClosedSubgroup {R : CommRingCat.{u}} [IsDomain R]
    [IsPrincipalIdealRing R] (G : GroupScheme (Spec R)) [Flat G.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    IsClosedSubgroup (closedEmbedding G).representation :=
  (closedEmbedding G).closed

/-- The PID embedding theorem in the existential interface used by matrix reductions. -/
theorem exists_isClosedSubgroup_of_pid (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    (hflat : Flat G.X.hom) (haffine : IsAffineHom G.X.hom)
    (hfinite : LocallyOfFiniteType G.X.hom) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ :=
  ⟨(closedEmbedding G).rank, (closedEmbedding G).representation,
    closedEmbedding_isClosedSubgroup G⟩

/-- In particular, the same embedding exists over every DVR. -/
theorem exists_isClosedSubgroup_of_dvr (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    (hflat : Flat G.X.hom) (haffine : IsAffineHom G.X.hom)
    (hfinite : LocallyOfFiniteType G.X.hom) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ :=
  exists_isClosedSubgroup_of_pid R G hflat haffine hfinite

end Langlands.GroupScheme.IntegralLinearEmbedding
