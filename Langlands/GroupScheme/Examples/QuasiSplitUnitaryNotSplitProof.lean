import Langlands.GroupScheme.Examples.QuasiSplitUnitaryNotSplitStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Reductive.GeneralLinearMaximal
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # The quasi-split unitary group `U(1,1)` has no split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitUnitary

private def toGrpIso {S : Scheme.{u}} {T T' : CommGroupScheme S} (t : T ≅ T') :
    T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom t.hom
  inv := CommGroupScheme.groupHom t.inv
  hom_inv_id := congrArg Additive.toMul t.hom_inv_id
  inv_hom_id := congrArg Additive.toMul t.inv_hom_id

/-- A nontrivial quadratic conjugation gives a unitary group with no split maximal torus. -/
theorem notSplit : NotSplitStatement.{u} := by
  classical
  intro F E _ _ _ _ κ _ b c hc ⟨T, i, hsplit, hmax⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := hsplit
  have hcard : Nat.card I ≤ 1 :=
    (rankStatement F E κ b c hc).2.1 I (e.inv ≫ i) (hmax.2.1.iso_comp e.symm)
  have hG := isConnectedReductive F E κ b c hc
  have := hG.smooth
  have := hG.isAffineHom
  have hmaxE := (maximalTorusBaseChange F E (groupScheme b c) T i hmax.1 hmax.2.1).mp hmax
  have hmaxE' := hmaxE.comp_iso (splittingIso b c hc)
  let K := AlgebraicClosure E
  have : Smooth (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)).X.hom :=
    GeneralLinear.smoothStatement (Fin 2) (CommRingCat.of E)
  have hmaxK := (maximalTorusBaseChange E K
    (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)) _ _ hmaxE'.1 hmaxE'.2.1).mp hmaxE'
  have hmaxK' := hmaxK.comp_iso
    (GeneralLinear.baseChangeIso (Fin 2) (Spec.map (CommRingCat.ofHom (algebraMap E K))))
  have : Smooth (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of K)).X.hom :=
    GeneralLinear.smoothStatement (Fin 2) (CommRingCat.of K)
  have : ConnectedSpace (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of K)).X.left :=
    connectedSpace_generalLinear K (Fin 2)
  obtain ⟨g, φ, -⟩ := maximalTorusConjugacy K
    (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of K)) _ _ _ _ hmaxK'
    (GeneralLinear.isMaximalTorus_diagonalTorus (n := Fin 2) K)
  let bE : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F E))
  let bK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of E) :=
    Spec.map (CommRingCat.ofHom (algebraMap E K))
  let eK : splitTorus (Spec (CommRingCat.of K)) I ≅
      splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2)) :=
    (splitTorus.baseChangeIso bK I).symm ≪≫
      (GroupScheme.baseChange bK).mapIso
        (((GroupScheme.baseChange bE).mapIso e ≪≫ splitTorus.baseChangeIso bE I).symm) ≪≫
      toGrpIso φ
  have h2 := splitTorus.card_eq_card_of_iso I (ULift.{u} (Fin 2)) eK
  have h3 : Nat.card (ULift.{u} (Fin 2)) = 2 := by simp
  omega

end Langlands.GroupScheme.QuasiSplitUnitary
