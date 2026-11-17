import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.SplitOfGroupLikeSpan
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Descent.FiniteStageIso
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Groups of multiplicative type over a field split over a finite Galois extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace MultiplicativeTypeSplitting

/-- Internal helper predicate: `G` is isomorphic to the diagonalizable group `D_k(Λ)` of
some finitely generated abelian group `Λ` in the same universe. -/
def IsFGDiagonalizable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
    Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- The helper predicate is invariant under isomorphism. -/
theorem IsFGDiagonalizable.of_iso {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ G') (h : IsFGDiagonalizable G') : IsFGDiagonalizable G := by
  obtain ⟨Λ, hΛ, hfg, ⟨d⟩⟩ := h
  exact ⟨Λ, hΛ, hfg, ⟨e ≪≫ d⟩⟩

/-- Diagonalizability with the same character group survives every field extension. -/
theorem IsFGDiagonalizable.baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (h : IsFGDiagonalizable G) :
    IsFGDiagonalizable ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  obtain ⟨Λ, hΛ, hfg, ⟨d⟩⟩ := h
  exact ⟨Λ, hΛ, hfg,
    ⟨(GroupScheme.baseChange (algebraBaseMap k K)).mapIso d ≪≫
      Diagonalizable.baseChangeIso (algebraBaseMap k K) Λ⟩⟩

/-- Diagonalizability over an intermediate field propagates to the top of a field tower. -/
theorem IsFGDiagonalizable.fieldTower (k L K : Type u) [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (h : IsFGDiagonalizable ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) :
    IsFGDiagonalizable ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  (h.baseChange (K := K)).of_iso (baseChangeFieldTowerIso k L K G)

/-- A diagonalizable model after a field extension and group-like spanning of the actual
coordinate Hopf algebra give a diagonalizable model over the original field, with the same
character group. -/
def diagonalizableIsoOfGroupLikeSpan {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} [IsAffine T.X.left]
    {K : Type u} [Field K] [Algebra k K] {Λ : Type u} [AddCommGroup Λ]
    (e : (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (hspan : Submodule.span k
      {a : AffineCoordinates.hopfAlgebra T | IsGroupLikeElem k a} = ⊤) :
    T ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp := by
  classical
  let A := AffineCoordinates.hopfAlgebra T
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let eSpec :
      (hopfSpec (CommRingCat.of K)).obj
          (op (HopfCoordinates.scalarExtension k K A)) ≅
        (hopfSpec (CommRingCat.of K)).obj
          (op (Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)) :=
    (HopfCoordinates.baseChangeSpecIso k K A).symm ≪≫
      (GroupScheme.baseChange b).mapIso (AffineCoordinates.hopfSpecIso T) ≪≫ e ≪≫
      (Diagonalizable.hopfSpecIso (CommRingCat.of K) Λ).symm
  let eA : (K ⊗[k] A) ≃ₐc[K] AddMonoidAlgebra K Λ :=
    CommHopfAlgCat.ofIso (hopfSpec.fullyFaithful.preimageIso eSpec).unop.symm
  let eM : GroupLike k A ≃* Multiplicative Λ :=
    (Langlands.GroupLike.baseChangeMulEquivOfSpan (K := K) hspan).trans
      ((Langlands.GroupLike.mulEquivOfBialgEquiv eA).trans
        ((Langlands.GroupLike.mulEquivOfBialgEquiv
          (AddMonoidAlgebra.toMultiplicativeBialgEquiv K K Λ)).trans
            (Langlands.MonoidAlgebra.monomialGroupLikeEquiv K
              (Multiplicative Λ)).symm))
  let eL : Additive (GroupLike k A) ≃+ Λ := eM.toAdditiveLeft
  let eRec : A ≃ₐc[k] AddMonoidAlgebra k (Additive (GroupLike k A)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv k k (GroupLike k A))
  let eT := AffineCoordinates.isoOfBialgEquiv T
    (Diagonalizable.hopfAlgebra (CommRingCat.of k) (Additive (GroupLike k A))) eRec
  exact eT.symm ≪≫
    Diagonalizable.hopfSpecIso (CommRingCat.of k) (Additive (GroupLike k A)) ≪≫
      Diagonalizable.congrIso (CommRingCat.of k) eL

/-- Over a separably closed field, every group of multiplicative type is diagonalizable
with finitely generated character group. -/
theorem isFGDiagonalizable_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsMultiplicativeType T) :
    IsFGDiagonalizable T := by
  have : IsAffine T.X.left := hT.isAffine
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hT
  have hspanK : Submodule.span K
      {a : K ⊗[k] AffineCoordinates.hopfAlgebra T | IsGroupLikeElem K a} = ⊤ :=
    SplittingAssembly.span_of_hopfSpecIso
      (HopfCoordinates.scalarExtension k K (AffineCoordinates.hopfAlgebra T))
      (Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)
      (SplittingAssembly.scalarExtensionCoordinatesIso T ≪≫ e ≪≫
        (Diagonalizable.hopfSpecIso (CommRingCat.of K) Λ).symm)
      AddMonoidAlgebra.span_isGroupLikeElem
  have hspan := Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning.{u, u, u}
    k (AffineCoordinates.hopfAlgebra T) K hspanK
  exact ⟨Λ, hΛ, hfg, ⟨diagonalizableIsoOfGroupLikeSpan e hspan⟩⟩

/-- Being of multiplicative type is preserved by an algebraic extension of the ground
field. -/
theorem isMultiplicativeType_baseChange_of_isAlgebraic
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsMultiplicativeType T) :
    IsMultiplicativeType ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨d⟩⟩ := hT
  let E := AlgebraicClosure K
  let f : L →ₐ[k] E := IsAlgClosed.lift
  let : Algebra L E := f.toRingHom.toAlgebra
  let : IsScalarTower k L E :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  refine ⟨E, inferInstance, inferInstance, Λ, hΛ, hfg, ⟨?_⟩⟩
  exact (baseChangeFieldTowerIso k L E T).symm ≪≫
    baseChangeFieldTowerIso k K E T ≪≫
    (GroupScheme.baseChange (algebraBaseMap K E)).mapIso d ≪≫
    Diagonalizable.baseChangeIso (algebraBaseMap K E) Λ

/-- A group of multiplicative type over a field is diagonalizable over a finite
intermediate field of its separable closure. -/
theorem exists_finiteIntermediateField
    (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsMultiplicativeType H) :
    ∃ E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k (SeparableClosure k),
      IsFGDiagonalizable ((GroupScheme.baseChange (algebraBaseMap k E.1)).obj H) := by
  have : IsAffine H.X.left := hH.isAffine
  let Ω := SeparableClosure k
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := isFGDiagonalizable_of_isSepClosed _
    (isMultiplicativeType_baseChange_of_isAlgebraic k Ω H hH)
  let D0 := (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
  have : LocallyOfFiniteType D0.X.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom)
  let e' : (GroupScheme.baseChange (algebraBaseMap k Ω)).obj H ≅
      (GroupScheme.baseChange (algebraBaseMap k Ω)).obj D0 :=
    e ≪≫ (Diagonalizable.baseChangeIso (algebraBaseMap k Ω) Λ).symm
  let M := Descent.FiniteStage.isoModel k Ω e'
  exact ⟨M.fieldOfDefinition, Λ, hΛ, hfg,
    ⟨M.iso ≪≫ Diagonalizable.baseChangeIso (algebraBaseMap k M.fieldOfDefinition.1) Λ⟩⟩

end MultiplicativeTypeSplitting

open MultiplicativeTypeSplitting in
/-- Every group of multiplicative type over a field becomes diagonalizable, with finitely
generated character group, over a finite Galois extension. -/
theorem multiplicativeTypeFiniteGaloisSplitting :
    MultiplicativeTypeFiniteGaloisSplittingStatement.{u} := by
  intro k _ H hH
  obtain ⟨E, hE⟩ := exists_finiteIntermediateField k H hH
  have : FiniteDimensional k E.1 := E.2
  let K := IntermediateField.normalClosure k E.1 (SeparableClosure k)
  obtain ⟨Λ, hΛ, hfg, hiso⟩ := IsFGDiagonalizable.fieldTower k E.1 K H hE
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, Λ, hΛ, hfg, hiso⟩

end Langlands.GroupScheme
