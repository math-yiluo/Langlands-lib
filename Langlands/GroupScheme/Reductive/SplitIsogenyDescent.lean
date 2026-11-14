import Langlands.GroupScheme.Reductive.SplitIsogenyGraphBaseChange
import Langlands.GroupScheme.Reductive.SplitIsogenyRootDatumBaseChange
import Langlands.GroupScheme.Reductive.SplitIsogenyFirstProjection
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # First-projection descent for the actual local-isogeny graph -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization.SimpleIsogenyGraph

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    (D : SimpleIsogenyGraph i i' t)
    {J J' : Type u} [Finite J] [Finite J']
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [P.IsReduced] [P'.IsReduced]
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (hT' : IsSplitTorus T'.toGrp) {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)
    (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i)
    (hH : IsConnectedReductive D.envelope.group)

set_option maxHeartbeats 800000 in
include hP hP' hT' hw hG hmax hH in
/-- The first actual projection is invertible over the original arbitrary field. -/
theorem first_isIsoOfReductive : IsIso D.envelope.first := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let C := CommGroupScheme.baseChange b
  have hGK : IsConnectedReductive (B.obj G) := hG.baseChange_toAlgebraicClosure
  have hHK : IsConnectedReductive (D.baseChange K).envelope.group :=
    hH.baseChange_toAlgebraicClosure
  have hmaxK : IsMaximalTorus (T := C.obj T) (B.map i) :=
    (maximalTorusBaseChange k K G T i hmax.1 hmax.2.1).mp hmax
  let : Module.Finite ℤ (characterLattice (C.obj T)) :=
    SplitRootDatum.characterFiniteBaseChange b T D.split
  let : Module.Finite ℤ (cocharacterLattice (C.obj T)) :=
    SplitRootDatum.cocharacterFiniteBaseChange b T D.split
  let : Module.Finite ℤ (characterLattice (C.obj T')) :=
    SplitRootDatum.characterFiniteBaseChange b T' hT'
  let : Module.Finite ℤ (cocharacterLattice (C.obj T')) :=
    SplitRootDatum.cocharacterFiniteBaseChange b T' hT'
  let PK := SplitRootDatum.baseChange b T D.split P
  let PK' := SplitRootDatum.baseChange b T' hT' P'
  have hPK : IsRootDatumOf (T := C.obj T) (B.map i) PK :=
    hP.baseChange (K := K) G T D.split i
  have hPK' : IsRootDatumOf (T := C.obj T') (B.map i') PK' :=
    hP'.baseChange (K := K) G' T' hT' i'
  let fK := rootDatumIsogenyBaseChange b D.split hT' f
  have hwK : ∀ χ : characterLattice (C.obj T'), C.map t ≫ χ = fK.weightMap χ :=
    rootDatumIsogenyBaseChange_torus b D.split hT' f t hw
  let e := (D.baseChange K).firstProjectionIsoOfReductive PK PK' hPK hPK'
    (IsSplitTorus.baseChange b hT') fK hwK hGK hmaxK hHK
  let : IsIso (D.baseChange K).envelope.first := by
    change IsIso e.hom
    infer_instance
  exact D.isIso_first_of_baseChange K

/-- The descended isomorphism retains the original graph and first projection. -/
def firstProjectionIsoOfReductiveField : D.envelope.group ≅ G := by
  let : IsIso D.envelope.first :=
    D.first_isIsoOfReductive P P' hP hP' hT' f hw hG hmax hH
  exact asIso D.envelope.first

@[simp]
theorem firstProjectionIsoOfReductiveField_hom :
    (D.firstProjectionIsoOfReductiveField P P' hP hP' hT' f hw hG hmax hH).hom =
      D.envelope.first := rfl

end Langlands.GroupScheme.RootDatumIsogenyRealization.SimpleIsogenyGraph
