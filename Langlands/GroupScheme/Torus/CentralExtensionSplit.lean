import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.Torus.SplitOfGroupLikeSpan
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.CorepresentedComultiplication

/-! # Central extensions of split tori by split tori are split tori

Let `E` be an affine group scheme over a field `K`, `z : Z ⟶ E` a central closed subgroup and
`p : E ⟶ T` an fppf quotient map with kernel `Z`. If `Z` and `T` are split tori, then `E` is a
split torus. The proof transports the data to the coordinate Hopf algebra of `E`, where
`CentralTorusExtensionHopf` shows that the group-like elements span and form a lattice. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {B : Scheme.{u}} {H Q Q' : GroupScheme B}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing an fppf quotient map with an isomorphism of targets keeps the cover and the
kernel. -/
theorem IsFppfQuotient.comp_iso {N : SubgroupFunctor H} {q : H ⟶ Q}
    (h : IsFppfQuotient N q) (e : Q ≅ Q') : IsFppfQuotient N (q ≫ e.hom) := by
  obtain ⟨hflat, hsurj, hfp, hker⟩ := h
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget B).mapIso ((Grp.forget _).mapIso e)).hom)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (q.hom.hom.left ≫ e.hom.hom.hom.left)
    exact (MorphismProperty.cancel_right_of_respectsIso @Flat
      q.hom.hom.left e.hom.hom.hom.left).mpr hflat
  · change Surjective (q.hom.hom.left ≫ e.hom.hom.hom.left)
    exact (MorphismProperty.cancel_right_of_respectsIso @Surjective
      q.hom.hom.left e.hom.hom.hom.left).mpr hsurj
  · change LocallyOfFinitePresentation (q.hom.hom.left ≫ e.hom.hom.hom.left)
    exact (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation
      q.hom.hom.left e.hom.hom.hom.left).mpr hfp
  · rw [← hker]
    apply SubgroupFunctor.ext
    intro T
    ext x
    rw [mem_range_kernelι_iff, mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc,
      ← isoPointsEquiv_apply e T, MulEquiv.map_eq_one_iff]

end RelativeRoot

namespace CentralExtensionHopfSpec

open RelativeRoot

variable {K : Type u} [Field K]

/-- A central extension of a split torus by a split torus is a split torus, for an affine
group scheme over a field: if `z : Z ⟶ E` is a central closed subgroup, `p : E ⟶ T` is an fppf
quotient map with kernel `Z`, and `Z ≅ 𝔾_m^J`, `T ≅ 𝔾_m^I`, then `E ≅ 𝔾_m^(I ⊕ J)`. -/
theorem isSplitTorus_of_split {E Z T : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] {I J : Type u} [Finite I] [Finite J]
    (eZ0 : Z ≅ splitTorus (Spec (CommRingCat.of K)) J)
    (eT0 : T ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ T) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    IsSplitTorus E := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let R := CommRingCat.of K
  let A := AffineCoordinates.hopfAlgebra E
  let eE := AffineCoordinates.hopfSpecIso E
  let eZ : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R (J → ℤ))) ≅ Z :=
    Diagonalizable.hopfSpecIso R (J → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ)) ≪≫ eZ0.symm
  let eT : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R (I → ℤ))) ≅ T :=
    Diagonalizable.hopfSpecIso R (I → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eT0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R (J → ℤ) :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ z ≫ eE.symm.hom)).unop
  let φ : Diagonalizable.hopfAlgebra R (I → ℤ) ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eE.symm.inv ≫ p ≫ eT.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eZ.hom ≫ z ≫ eE.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eE.symm.inv ≫ p ≫ eT.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hz' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hz.comp_iso eE.symm)
  have hc' : IsCentral ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact (hc.comp_iso eE.symm).comp eZ.hom
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eE.symm).comp_iso eT.symm
  have h := isCentralExtension φ π hz' hc' hq'
  have hspan := CentralTorusExtensionHopf.span_isGroupLikeElem h
  let eRec : A ≃ₐc[K] AddMonoidAlgebra K (Additive (GroupLike K A)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K A))
  let e1 := AffineCoordinates.isoOfBialgEquiv E
    (Diagonalizable.hopfAlgebra R (Additive (GroupLike K A))) eRec
  exact ⟨I ⊕ J, inferInstance, ⟨e1.symm ≪≫
    Diagonalizable.hopfSpecIso R (Additive (GroupLike K A)) ≪≫
      Diagonalizable.splitIso R (CentralTorusExtensionHopf.groupLikeEquiv h)⟩⟩

end CentralExtensionHopfSpec

end Langlands.GroupScheme
