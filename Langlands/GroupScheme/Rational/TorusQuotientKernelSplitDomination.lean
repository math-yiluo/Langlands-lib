import Langlands.GroupScheme.Rational.TorusKernelDomination
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableTorusDomination
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Split-torus domination of full torus-quotient kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Diagonalizable

variable {k : Type u} [Field k]
    (T Q : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The actual character lattice of a split torus is finitely generated. -/
theorem splitTorusCharacterLattice_fg (hT : IsSplitTorus T.toGrp) :
    AddGroup.FG (characterLattice T) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let b := (splitTorus.characterLatticeEquiv k I).symm.trans c
  exact AddGroup.fg_of_surjective (f := b.toAddMonoidHom) b.surjective

/-- A split torus is the diagonalizable group of its actual character lattice. -/
def splitTorusDiagonalizableIso (hT : IsSplitTorus T.toGrp) :
    T.toGrp ≅ (groupScheme (CommRingCat.of k) (characterLattice T)).toGrp :=
  isoOfPointModels
    (fun U : Over (Spec (CommRingCat.of k)) =>
      Multiplicative (characterLattice T) →* (Γ(U.left, ⊤))ˣ)
    (fun a => MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom))
    (characterLattice.pointCharactersEquiv T hT)
    (characterPointsEquiv (CommRingCat.of k) (characterLattice T))
    (by
      intro U U' a x
      apply MonoidHom.ext
      intro b
      exact characterLattice.pointCharacters_naturality T a x b.toAdd)
    (characterPointsEquiv_natural (CommRingCat.of k) (characterLattice T))

/-- The product of a split torus and the full kernel of a split-torus map is
an actual finitely generated diagonalizable group, without saturation. -/
def splitTorusKernelProductIso (f : T.toGrp ⟶ Q.toGrp)
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) :
    T.toGrp ⊗ kernel f ≅
      (groupScheme (CommRingCat.of k) (characterLattice T × homKernelLattice f)).toGrp :=
  ((splitTorusDiagonalizableIso T hT) ⊗ᵢ (homKernelDiagonalizableIso f hT hQ)) ≪≫
    (productIso (CommRingCat.of k) (characterLattice T) (homKernelLattice f)).symm

end Diagonalizable

namespace TorusKernelDomination

variable {k : Type u} [Field k]
    {D Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- The full quotient-kernel difference map, with an actual diagonalizable source. -/
def diagonalizableParametrization
    (hD : IsSplitTorus D.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (q : H ⟶ Q.toGrp) (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    (Diagonalizable.groupScheme (CommRingCat.of k)
      (characterLattice D × Diagonalizable.homKernelLattice
        (quotientHom hD.isTorus hQ.isTorus q p hp))).X ⟶ (kernel q).X :=
  (Diagonalizable.splitTorusKernelProductIso D Q
    (quotientHom hD.isTorus hQ.isTorus q p hp) hD hQ).inv.hom.hom ≫
    parametrization hD.isTorus hQ.isTorus q p hp

/-- Changing the source by the diagonalizable product isomorphism preserves dominance. -/
theorem diagonalizableParametrization_isDominant
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hD : IsSplitTorus D.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (q : H ⟶ Q.toGrp) [IsDominant q.hom.hom.left]
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsDominant p.left) :
    IsDominant (diagonalizableParametrization hD hQ q p hp).left := by
  have := parametrization_isDominant hD.isTorus hQ.isTorus q p hp hd
  have : IsIso (Diagonalizable.splitTorusKernelProductIso D Q
      (quotientHom hD.isTorus hQ.isTorus q p hp) hD hQ).inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso
      (Diagonalizable.splitTorusKernelProductIso D Q
        (quotientHom hD.isTorus hQ.isTorus q p hp) hD hQ).inv
  change IsDominant (_ ≫ (parametrization hD.isTorus hQ.isTorus q p hp).left)
  infer_instance

/-- A smooth connected full kernel of a dominant torus quotient inherits pointed
split-torus domination after a finite separable extension. -/
theorem exists_finiteSeparable_kernel_hasPointedSplitTorusDomination
    {D Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hD : IsSplitTorus D) (hQ : IsTorus Q)
    (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    [Smooth (kernel q).X.hom] [ConnectedSpace (kernel q).X.left]
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X])
    (hd : IsDominant p.left) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Module.Finite k L) (_ : Algebra.IsSeparable k L),
      HasPointedSplitTorusDomination ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (kernel q)) := by
  let DC : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { D with comm := hD.isCommMonObj }
  let QC : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { Q with comm := hQ.isCommMonObj }
  have hQs : IsSplitTorus Q := isSplitTorus_quotient hD hQ q p hp hd
  let f : DC.toGrp ⟶ QC.toGrp := quotientHom hD.isTorus hQs.isTorus q p hp
  let Λ := characterLattice DC × Diagonalizable.homKernelLattice f
  have : AddGroup.FG (characterLattice DC) :=
    Diagonalizable.splitTorusCharacterLattice_fg DC hD
  have : AddGroup.FG (Diagonalizable.homKernelLattice f) :=
    Diagonalizable.homKernelLattice_fg f hD
  have : AddGroup.FG Λ := inferInstance
  have : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ
  have : IsAffineHom Q.X.hom := inferInstance
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : GeometricallyIntegral (kernel q).X.hom :=
    smoothConnectedAffineGeometry.1 k (kernel q) inferInstance inferInstance inferInstance
  let r : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X ⟶ (kernel q).X :=
    diagonalizableParametrization (D := DC) (Q := QC) hD hQs q p hp
  have : IsDominant r.left :=
    diagonalizableParametrization_isDominant (D := DC) (Q := QC) hD hQs q p hp hd
  exact Diagonalizable.exists_finiteSeparable_hasPointedSplitTorusDomination
    k Λ (kernel q) r

end TorusKernelDomination

end Langlands.GroupScheme
