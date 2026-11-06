import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Full root-data comparison over arbitrary fields -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitRootDatum

variable {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (hT : IsSplitTorus T.toGrp)
    {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))

/-- Actual lattice pullback gives a full equivalence with the transported
root datum. The coweight map is the inverse of cocharacter pullback. -/
def baseChangeEquiv : RootPairing.Equiv P (baseChange b T hT P) where
  weightMap := (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv
  coweightMap := (cocharacterLattice.baseChangeEquiv b T hT).symm.toIntLinearEquiv
  indexEquiv := Equiv.refl J
  weight_coweight_transpose := by
    ext ν' χ
    obtain ⟨ν, rfl⟩ := (cocharacterLattice.baseChangeEquiv b T hT).surjective ν'
    change (baseChange b T hT P).toLinearMap
      (characterLattice.baseChange b T χ) (cocharacterLattice.baseChange b T ν) =
        P.toLinearMap χ
          ((cocharacterLattice.baseChangeEquiv b T hT).symm
            (cocharacterLattice.baseChangeEquiv b T hT ν))
    rw [baseChange_pairing, AddEquiv.symm_apply_apply]
  root_weightMap := by
    funext α
    rfl
  coroot_coweightMap := by
    funext α
    exact (cocharacterLattice.baseChangeEquiv b T hT).symm_apply_apply (P.coroot α)
  bijective_weightMap := (characterLattice.baseChangeEquiv b T hT).bijective
  bijective_coweightMap := (cocharacterLattice.baseChangeEquiv b T hT).symm.bijective

@[simp] theorem baseChangeEquiv_weightMap (χ : characterLattice T) :
    (baseChangeEquiv b T hT P).weightMap χ = characterLattice.baseChange b T χ := rfl

@[simp] theorem baseChangeEquiv_coweightMap (ν : cocharacterLattice T) :
    (baseChangeEquiv b T hT P).coweightMap (cocharacterLattice.baseChange b T ν) = ν :=
  (cocharacterLattice.baseChangeEquiv b T hT).symm_apply_apply ν

end SplitRootDatum

/-- An actual group isomorphism over any field determines equivalent full
root data on any two supplied split maximal tori. -/
theorem nonempty_rootDatumEquiv_of_iso
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}
    (hi : IsMaximalTorus i) (hj : IsMaximalTorus j)
    {J J' : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    (f : G ≅ H)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q) :
    Nonempty (RootPairing.Equiv P Q) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hH.isAffineHom
  let := hH.smooth
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  have hGK := connectedReductiveFieldExtensionStatement k K G hG
  have hHK := connectedReductiveFieldExtensionStatement k K H hH
  have hiK := (maximalTorusBaseChange k K G T i hi.1 hi.2.1).mp hi
  have hjK := (maximalTorusBaseChange k K H T' j hj.1 hj.2.1).mp hj
  have hPK := splitRootDatumFieldExtension k K G hG T hT i hi J P hP
  have hQK := splitRootDatumFieldExtension k K H hH T' hT' j hj J' Q hQ
  obtain ⟨e⟩ := nonempty_rootDatumEquiv_of_iso_of_isAlgClosed hGK hHK
    (hT.baseChange b) (hT'.baseChange b) hiK hjK
    ((GroupScheme.baseChange b).mapIso f) hPK hQK
  exact ⟨(SplitRootDatum.baseChangeEquiv b T' hT' Q).symm.comp
    (e.comp (SplitRootDatum.baseChangeEquiv b T hT P))⟩

end Langlands.GroupScheme
