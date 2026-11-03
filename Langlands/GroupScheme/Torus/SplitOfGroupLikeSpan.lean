import Langlands.Algebra.GroupLikeBaseChange
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.HopfBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.Lattice

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupLike

variable {R : Type u} [CommRing R]
  {A : Type v} [Ring A] [Bialgebra R A]
  {B : Type w} [Ring B] [Bialgebra R B]

/-- A bialgebra equivalence identifies the monoids of group-like elements. -/
def mulEquivOfBialgEquiv (e : A ≃ₐc[R] B) : GroupLike R A ≃* GroupLike R B where
  toFun g := ⟨e g.val, g.isGroupLikeElem_val.map e⟩
  invFun g := ⟨e.symm g.val, g.isGroupLikeElem_val.map e.symm⟩
  left_inv g := GroupLike.val_injective (e.symm_apply_apply g.val)
  right_inv g := GroupLike.val_injective (e.apply_symm_apply g.val)
  map_mul' g h := GroupLike.val_injective (e.map_mul g.val h.val)

end Langlands.GroupLike

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : GroupScheme (Spec (CommRingCat.of k))} [IsAffine T.X.left]

/-- A chosen splitting after field extension and group-like spanning of the original
coordinate Hopf algebra give a splitting over the original field of the same rank. -/
def AffineCoordinates.splitIsoOfGroupLikeSpan
    {K : Type u} [Field K] [Algebra k K] {I : Type u} [Finite I]
    (e : (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T ≅
        splitTorus (Spec (CommRingCat.of K)) I)
    (hspan : Submodule.span k
      {a : AffineCoordinates.hopfAlgebra T | IsGroupLikeElem k a} = ⊤) :
    T ≅ splitTorus (Spec (CommRingCat.of k)) I := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let A := AffineCoordinates.hopfAlgebra T
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let eSpec :
      (hopfSpec (CommRingCat.of K)).obj
          (op (HopfCoordinates.scalarExtension k K A)) ≅
        (hopfSpec (CommRingCat.of K)).obj
          (op (Diagonalizable.hopfAlgebra (CommRingCat.of K) (I → ℤ))) :=
    (HopfCoordinates.baseChangeSpecIso k K A).symm ≪≫
      (GroupScheme.baseChange b).mapIso (AffineCoordinates.hopfSpecIso T) ≪≫ e ≪≫
      (Diagonalizable.hopfSpecIso (CommRingCat.of K) (I → ℤ) ≪≫
        Diagonalizable.splitIso (CommRingCat.of K) (AddEquiv.refl (I → ℤ))).symm
  let eA : (K ⊗[k] A) ≃ₐc[K] AddMonoidAlgebra K (I → ℤ) :=
    CommHopfAlgCat.ofIso (hopfSpec.fullyFaithful.preimageIso eSpec).unop.symm
  let eM : GroupLike k A ≃* Multiplicative (I → ℤ) :=
    (Langlands.GroupLike.baseChangeMulEquivOfSpan (K := K) hspan).trans
      ((Langlands.GroupLike.mulEquivOfBialgEquiv eA).trans
        ((Langlands.GroupLike.mulEquivOfBialgEquiv
          (AddMonoidAlgebra.toMultiplicativeBialgEquiv K K (I → ℤ))).trans
            (Langlands.MonoidAlgebra.monomialGroupLikeEquiv K
              (Multiplicative (I → ℤ))).symm))
  let eL : Additive (GroupLike k A) ≃+ (I → ℤ) := eM.toAdditiveLeft
  let eRec : A ≃ₐc[k] AddMonoidAlgebra k (Additive (GroupLike k A)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv k k (GroupLike k A))
  let eT := AffineCoordinates.isoOfBialgEquiv T
    (Diagonalizable.hopfAlgebra (CommRingCat.of k) (Additive (GroupLike k A))) eRec
  exact eT.symm ≪≫
    Diagonalizable.hopfSpecIso (CommRingCat.of k) (Additive (GroupLike k A)) ≪≫
      Diagonalizable.splitIso (CommRingCat.of k) eL

/-- An affine torus whose coordinate Hopf algebra is spanned by group-like elements
is already split over its ground field. -/
theorem IsTorus.isSplitTorus_of_groupLike_span (hT : IsTorus T)
    (hspan : Submodule.span k
      {a : AffineCoordinates.hopfAlgebra T | IsGroupLikeElem k a} = ⊤) :
    IsSplitTorus T := by
  obtain ⟨K, hK, hA, I, hI, ⟨e⟩⟩ := hT
  exact ⟨I, hI, ⟨AffineCoordinates.splitIsoOfGroupLikeSpan e hspan⟩⟩

end Langlands.GroupScheme
