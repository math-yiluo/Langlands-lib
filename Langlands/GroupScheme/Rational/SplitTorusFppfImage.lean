import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual fppf images of split tori in affine group schemes -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {D D' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every homomorphism between split tori over a field is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_splitTori (hD : IsSplitTorus D.toGrp)
    (hD' : IsSplitTorus D'.toGrp) (p : D ⟶ D') :
    LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left := by
  have := hD.smooth
  have := hD'.smooth
  have : IsLocallyNoetherian D'.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian D'.X.hom
  have : LocallyOfFiniteType
      ((CommGroupScheme.groupHom p).hom.hom.left ≫ D'.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (CommGroupScheme.groupHom p).hom.hom.left := by
    exact locallyOfFiniteType_of_comp (CommGroupScheme.groupHom p).hom.hom.left D'.X.hom
  infer_instance

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- A closed split-torus image equipped with the actual fppf projection onto it. -/
structure SplitTorusFppfImage (φ : D.toGrp ⟶ H) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  projection : D ⟶ torus
  inclusion : torus.toGrp ⟶ H
  isSplitSubtorus : IsSplitSubtorus inclusion
  flat : Flat (CommGroupScheme.groupHom projection).hom.hom.left
  surjective : Surjective (CommGroupScheme.groupHom projection).hom.hom.left
  locallyOfFinitePresentation :
    LocallyOfFinitePresentation (CommGroupScheme.groupHom projection).hom.hom.left
  factorization : CommGroupScheme.groupHom projection ≫ inclusion = φ

open SplitTorusImage Corepresented Diagonalizable in
/-- Every homomorphism from a split torus to an affine field group has a closed split-torus
image reached by an actual fppf map. -/
theorem IsSplitTorus.nonempty_fppfImage (hD : IsSplitTorus D.toGrp) (φ : D.toGrp ⟶ H) :
    Nonempty (SplitTorusFppfImage φ) := by
  classical
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  let := hI
  let : Fintype I := Fintype.ofFinite I
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let G₀ := Corepresented.groupScheme (functor (CommRingCat.of k) (I → ℤ))
    (grpCorepresentation (CommRingCat.of k) (I → ℤ))
  let cH := AffineCoordinates.corepresentation H
  let Hc := Corepresented.groupScheme (AffineCoordinates.functor H) cH
  let eT : G₀ ≅ splitTorus (Spec (CommRingCat.of k)) I :=
    splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))
  let eH : Hc ≅ H := AffineCoordinates.groupSchemeIso H
  let φ₀ : G₀ ⟶ Hc := ((eT.hom ≫ eD.inv) ≫ φ) ≫ eH.symm.hom
  let β := pointsTrans (grpCorepresentation (CommRingCat.of k) (I → ℤ)) cH φ₀
  obtain ⟨n, v⟩ := Submodule.basisOfPid (Pi.basisFun ℤ I) (lattice cH β)
  let b : lattice cH β ≃+ (ULift.{u} (Fin n) → ℤ) :=
    (v.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift)).toAddEquiv
  let E : CommGroupScheme (Spec (CommRingCat.of k)) :=
    groupScheme (CommRingCat.of k) (lattice cH β)
  let p : G₀ ⟶ E.toGrp :=
    restrictMap (CommRingCat.of k) (lattice cH β).subtype.toAddMonoidHom
  let q : E.toGrp ⟶ Hc :=
    groupSchemeMap (grpCorepresentation (CommRingCat.of k) (lattice cH β)) cH (imageTrans cH β)
  have hcomp : p ≫ q = φ₀ := by
    change groupSchemeMap _ _ _ ≫ groupSchemeMap _ _ _ = φ₀
    rw [groupSchemeMap_comp, restrict_imageTrans, groupSchemeMap_pointsTrans]
  let π : D ⟶ E := Additive.ofMul (eD.hom ≫ eT.inv ≫ p)
  let j : E.toGrp ⟶ H := q ≫ eH.hom
  have hE : IsSplitTorus E.toGrp := isSplitTorus (CommRingCat.of k) b
  have hp := flat_and_surjective_restrictMap (CommRingCat.of k)
    (lattice cH β).subtype.toAddMonoidHom Subtype.val_injective
  have : Flat p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2
  have : IsIso eD.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eD)).hom)
  have : IsIso eT.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eT)).inv)
  refine ⟨{
    torus := E
    projection := π
    inclusion := j
    isSplitSubtorus := ⟨hE, ?_⟩
    flat := ?_
    surjective := ?_
    locallyOfFinitePresentation := locallyOfFinitePresentation_of_splitTori
      ⟨I, hI, ⟨eD⟩⟩ hE π
    factorization := ?_ }⟩
  · have := isClosedImmersion_imageTrans cH β
    have : IsIso eH.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eH)).hom)
    change IsClosedImmersion (q.hom.hom.left ≫ eH.hom.hom.hom.left)
    infer_instance
  · change Flat (eD.hom.hom.hom.left ≫ eT.inv.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  · change Surjective (eD.hom.hom.hom.left ≫ eT.inv.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  · change (eD.hom ≫ eT.inv ≫ p) ≫ q ≫ eH.hom = φ
    rw [Category.assoc, Category.assoc, ← Category.assoc p, hcomp]
    simp only [φ₀, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.comp_id]

/-- A chosen closed split image of a split-torus homomorphism, with its actual fppf
projection and factorization. -/
def IsSplitTorus.fppfImage (hD : IsSplitTorus D.toGrp) (φ : D.toGrp ⟶ H) :
    SplitTorusFppfImage φ :=
  Classical.choice (hD.nonempty_fppfImage φ)

end Langlands.GroupScheme
