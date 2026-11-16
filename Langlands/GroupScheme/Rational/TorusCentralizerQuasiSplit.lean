import Langlands.GroupScheme.Rational.TorusCentralizerRegularCocharacter
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # A geometric Borel from a supplied torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.GroupScheme

namespace TorusCentralizerTorusData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (C : TorusCentralizerTorusData a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The ground-field dynamic parabolic of the separating cocharacter of the
supplied centralizer torus. -/
def borelScheme (hA : IsSplitTorus A.toGrp) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  Dynamic.Affine.parabolicScheme
    (CommGroupScheme.groupHom (C.regularCocharacter hA) ≫ C.inclusion)

/-- The actual inclusion of the chosen ground-field dynamic parabolic. -/
def borelHom (hA : IsSplitTorus A.toGrp) : C.borelScheme hA ⟶ G :=
  Dynamic.Affine.parabolicHom
    (CommGroupScheme.groupHom (C.regularCocharacter hA) ≫ C.inclusion)

/-- The chosen inclusion represents the whole dynamic parabolic on every test
scheme. -/
theorem borelHom_isRepresentedBy (hA : IsSplitTorus A.toGrp) :
    (Dynamic.parabolic
      (CommGroupScheme.groupHom (C.regularCocharacter hA) ≫ C.inclusion)).IsRepresentedBy
      (C.borelHom hA) :=
  Dynamic.Affine.isRepresentedBy_parabolicHom _

/-- The chosen original-field parabolic becomes a Borel over the algebraic
closure, and is therefore an actual geometric Borel. -/
theorem borelHom_isGeometricBorel (hG : IsConnectedReductive G)
    (hA : IsSplitTorus A.toGrp) : IsGeometricBorelSubgroup (C.borelHom hA) := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let T := (CommGroupScheme.baseChange b).obj C.torus
  let ν := cocharacterLattice.baseChange b C.torus (C.regularCocharacter hA)
  have hGK : IsConnectedReductive (F.obj G) :=
    connectedReductiveFieldExtensionStatement k (AlgebraicClosure k) G hG
  have := hGK.isAffineHom
  have hT : IsSplitTorus T.toGrp :=
    IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
      C.isTorus.baseChange
  have hi : IsMaximalTorus (T := T) (F.map C.inclusion) :=
    C.isMaximalTorus_baseChange (AlgebraicClosure k)
  have hν : IsRegularCocharacter (T := T) (F.map C.inclusion) ν :=
    C.regularCocharacter_baseChange_isRegular (AlgebraicClosure k) hA hT
  have heq : Dynamic.baseChangeCocharacter b
        (CommGroupScheme.groupHom (C.regularCocharacter hA) ≫ C.inclusion) =
      CommGroupScheme.groupHom ν ≫ F.map C.inclusion := by
    rw [Dynamic.baseChangeCocharacter_comp,
      ← cocharacterLattice.groupHom_baseChange_dynamic]
  have hrep := (C.borelHom_isRepresentedBy hA).baseChange b
  rw [← Dynamic.parabolic_baseChange, heq] at hrep
  have hclosed : IsClosedSubgroup (C.borelHom hA) :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom _
  apply isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure _ hclosed
  exact (regularCocharacterBorel (AlgebraicClosure k) (F.obj G) hGK T
    (F.map C.inclusion) hT hi).1 ν hν
    (F.obj (C.borelScheme hA)) (F.map (C.borelHom hA))
    (hclosed.baseChange b) hrep

include C in
/-- A connected reductive group is quasi-split if the whole centralizer of a
split torus is represented by a torus. -/
theorem isQuasiSplit (hG : IsConnectedReductive G) (hA : IsSplitTorus A.toGrp) :
    IsQuasiSplit G :=
  ⟨hG, C.borelScheme hA, C.borelHom hA, C.borelHom_isGeometricBorel hG hA⟩

end TorusCentralizerTorusData

/-- A torus representing the whole centralizer of a split torus makes the
ambient connected reductive group quasi-split. Closedness of the supplied
representative follows from dynamic centralizer representability. -/
theorem IsSplitTorus.isQuasiSplit_of_torusCentralizer
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) (hG : IsConnectedReductive G) (a : A.toGrp ⟶ G)
    {Z : GroupScheme (Spec (CommRingCat.of k))} (j : Z ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j) (hZ : IsTorus Z) :
    IsQuasiSplit G := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hclosed : IsClosedSubgroup j := by
    apply Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer
      (CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫ a)
    rwa [centralizingCocharacter_spec hA a]
  let C : TorusCentralizerTorusData a :=
    { torus := { toGrp := Z, comm := hZ.isCommMonObj }
      inclusion := j
      isTorus := hZ
      isClosedSubgroup := hclosed
      represents := hj }
  exact C.isQuasiSplit hG hA

end Langlands.GroupScheme
