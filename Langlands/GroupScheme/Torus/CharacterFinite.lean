import Langlands.GroupScheme.Torus.CharacterFaithfullyFlat
import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite morphisms from finite cokernels of character pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Diagonalizable

variable (R : CommRingCat.{u}) {Λ Λ' : Type u}
    [AddCommGroup Λ] [AddCommGroup Λ'] (g : Λ' →+ Λ)

/-- An injective character map with finite cokernel induces a finite morphism. -/
theorem isFinite_restrictMap (hg : Function.Injective g) [Finite (Λ ⧸ g.range)] :
    IsFinite (restrictMap R g).hom.hom.left := by
  rw [restrictMap_left]
  exact (IsFinite.SpecMap_iff _).mpr (finite_mapDomainRingHom (R := R) hg)

end Diagonalizable

variable {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The integral cokernel of pullback on the full actual character groups. -/
abbrev characterLattice.pullbackCokernel (f : T.toGrp ⟶ Q.toGrp) : Type u :=
  characterLattice T ⧸ (characterLattice.comapHom f).range

/-- Surjective pullback of full actual characters makes a homomorphism of split
tori a closed immersion. -/
theorem IsSplitTorus.isClosedImmersion_of_surjective_characterPullback
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T.toGrp ⟶ Q.toGrp)
    (hf : Function.Surjective (characterLattice.comapHom f)) :
    IsClosedImmersion f.hom.hom.left := by
  let eT := Diagonalizable.splitTorusDiagonalizableIso T hT
  let eQ := Diagonalizable.splitTorusDiagonalizableIso Q hQ
  let r := Diagonalizable.restrictMap (CommRingCat.of k) (characterLattice.comapHom f)
  have : IsClosedImmersion r.hom.hom.left :=
    Diagonalizable.isClosedImmersion_restrictMap (CommRingCat.of k) _ hf
  have : IsIso eT.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eT.hom
  have : IsIso eQ.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eQ.inv
  have hfac : f = eT.hom ≫ r ≫ eQ.inv := by
    apply (cancel_mono eQ.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Diagonalizable.splitTorusDiagonalizableIso_naturality hT hQ f
  rw [hfac]
  change IsClosedImmersion
    (eT.hom.hom.hom.left ≫ r.hom.hom.left ≫ eQ.inv.hom.hom.left)
  infer_instance

/-- A homomorphism of split tori with injective character pullback and finite
cokernel is finite. -/
theorem IsSplitTorus.isFinite_of_injective_characterPullback
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T.toGrp ⟶ Q.toGrp)
    (hf : Function.Injective (characterLattice.comapHom f))
    [Finite (characterLattice.pullbackCokernel f)] :
    IsFinite f.hom.hom.left := by
  let eT := Diagonalizable.splitTorusDiagonalizableIso T hT
  let eQ := Diagonalizable.splitTorusDiagonalizableIso Q hQ
  let r := Diagonalizable.restrictMap (CommRingCat.of k) (characterLattice.comapHom f)
  have : IsFinite r.hom.hom.left :=
    Diagonalizable.isFinite_restrictMap (CommRingCat.of k) _ hf
  have : IsIso eT.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eT.hom
  have : IsIso eQ.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eQ.inv
  have hfac : f = eT.hom ≫ r ≫ eQ.inv := by
    apply (cancel_mono eQ.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Diagonalizable.splitTorusDiagonalizableIso_naturality hT hQ f
  rw [hfac]
  change IsFinite (eT.hom.hom.hom.left ≫ r.hom.hom.left ≫ eQ.inv.hom.hom.left)
  infer_instance

end Langlands.GroupScheme
