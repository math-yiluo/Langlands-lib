import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.HopfBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.SplitOfGroupLikeSpan
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningStatement
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

namespace Langlands.GroupScheme.SplittingAssembly

/-- Group-like spanning is preserved by an equivalence of coalgebras. -/
theorem span_of_coalgEquiv
    {k : Type u} [Field k] {C : Type v} {D : Type w}
    [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup D] [Module k D] [Coalgebra k D]
    (e : C ≃ₗc[k] D)
    (h : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤ := by
  apply top_unique
  intro d _
  obtain ⟨c, rfl⟩ := e.surjective d
  have hc : c ∈ Submodule.span k {c : C | IsGroupLikeElem k c} := by
    rw [h]
    exact Submodule.mem_top
  have hm := Submodule.mem_map_of_mem (f := (e : C →ₗ[k] D)) hc
  rw [Submodule.map_span] at hm
  exact Submodule.span_mono
    (Set.image_subset_iff.2 fun _ hx => hx.map e) hm

/-- A group-scheme isomorphism of Hopf spectra transports group-like spanning. -/
theorem span_of_hopfSpecIso
    {k : Type u} [Field k] (A B : CommHopfAlgCat.{u} k)
    (e : (hopfSpec (CommRingCat.of k)).obj (op A) ≅
      (hopfSpec (CommRingCat.of k)).obj (op B))
    (h : Submodule.span k {b : B | IsGroupLikeElem k b} = ⊤) :
    Submodule.span k {a : A | IsGroupLikeElem k a} = ⊤ := by
  let i : B ≅ A := (hopfSpec.fullyFaithful.preimageIso e).unop
  exact span_of_coalgEquiv (CommHopfAlgCat.ofIso i).toCoalgEquiv h

/-- Split Hopf spectra have a group-like spanning family. -/
theorem span_of_isSplit_hopfSpec
    {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k)
    (h : IsSplitTorus ((hopfSpec (CommRingCat.of k)).obj (op A))) :
    Submodule.span k {a : A | IsGroupLikeElem k a} = ⊤ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := h
  let := Fintype.ofFinite I
  let eD := Diagonalizable.hopfSpecIso (CommRingCat.of k) (I → ℤ)
  let eS := Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))
  exact span_of_hopfSpecIso A (CommHopfAlgCat.of k (AddMonoidAlgebra k (I → ℤ)))
    (e ≪≫ eS.symm ≪≫ eD.symm) AddMonoidAlgebra.span_isGroupLikeElem

/-- Scalar extension of the actual coordinate Hopf algebra recovers the
base-changed group scheme. -/
def scalarExtensionCoordinatesIso
    {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    (T : GroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    : (hopfSpec (CommRingCat.of K)).obj
        (op (HopfCoordinates.scalarExtension k K (AffineCoordinates.hopfAlgebra T))) ≅
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  exact
    (HopfCoordinates.baseChangeSpecIso k K (AffineCoordinates.hopfAlgebra T)).symm ≪≫
      (GroupScheme.baseChange b).mapIso (AffineCoordinates.hopfSpecIso T)

/-- A splitting field gives group-like spanning of the scalar-extended actual
coordinate Hopf algebra. -/
theorem span_scalarExtension_of_isSplit
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (T : GroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)) :
    Submodule.span K
      {a : K ⊗[k] AffineCoordinates.hopfAlgebra T | IsGroupLikeElem K a} = ⊤ := by
  exact span_of_isSplit_hopfSpec
    (HopfCoordinates.scalarExtension k K (AffineCoordinates.hopfAlgebra T))
    (IsSplitTorus.of_iso (scalarExtensionCoordinatesIso T) h)

/-- The published affineness-descent proposition supplies the affine instance
needed to form a torus's actual coordinate Hopf algebra. -/
theorem isAffine_of_isTorus
    {k : Type u} [Field k]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T) :
    IsAffine T.X.left := by
  obtain ⟨K, hK, hA, h⟩ := hT
  have : IsAffineHom ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T).X.hom :=
    h.isAffineHom
  have : IsAffine ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T).X.hom
  exact Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K T.X.left T.X.hom
    ‹IsAffine ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T).X.left›

/-- Conditional assembly of separably closed splitting from pure-coalgebra
group-like spanning descent. -/
theorem isSplit_of_isSepClosed_of_prerequisites
    (hDescent : Langlands.CoalgebraDescent.SeparablyClosedGroupLikeSpanningStatement.{u,u,u})
    {k : Type u} [Field k] [IsSepClosed k]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T) :
    IsSplitTorus T := by
  have : IsAffine T.X.left := isAffine_of_isTorus T hT
  apply hT.isSplitTorus_of_groupLike_span
  obtain ⟨K, hK, hA, h⟩ := hT
  exact hDescent k (AffineCoordinates.hopfAlgebra T) K
    (span_scalarExtension_of_isSplit T h)

end Langlands.GroupScheme.SplittingAssembly
