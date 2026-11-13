import Langlands.GroupScheme.Rational.RationalCocharacterWallSupport
import Langlands.GroupScheme.Rational.CommonCocharacterLeviIntersection
import Langlands.GroupScheme.Rational.ParabolicGallery
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # Actual parabolic models retaining a fixed embedded Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RepresentedParabolicLeviIntersection

variable {k : Type u} [Field k]
  {G L : GroupScheme (Spec (CommRingCat.of k))}

namespace Dynamic

/-- Actual rational parabolic and Levi models for a cocharacter. -/
structure RationalParabolicModel
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  P : GroupScheme (Spec (CommRingCat.of k))
  M : GroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  m : M ⟶ P
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup m
  parabolic_rep : (Dynamic.parabolic chi).IsRepresentedBy p
  centralizer_rep : (Dynamic.centralizer chi).IsRepresentedBy (m ≫ p)

/-- The published affine dynamic decomposition has rational parabolic and
Levi structure in a connected reductive group. -/
def rationalParabolicModel (hG : IsConnectedReductive G)
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    RationalParabolicModel chi := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let d := affineDecompositionModel chi
  have hpc := d.parabolic_closed
  let : IsAffineHom d.parabolic.X.hom := hpc.isAffineHom
  have hmc := d.levi_closed.comp hpc
  have hM := dynamicCentralizerReductive k G hG chi d.levi
    (d.leviHom ≫ d.parabolicHom) hmc d.levi_rep
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical d.unipotentHom :=
    (dynamicGeometricUnipotentRadical k G hG chi d.parabolic d.unipotent
      d.parabolicHom d.unipotentHom d.parabolic_rep d.unipotent_rep).leviSubgroup_of_unipotentFieldExtension
        unipotentFieldExtensionStatement
  exact
    { P := d.parabolic
      M := d.levi
      p := d.parabolicHom
      m := d.leviHom
      parabolic := isParabolicSubgroup_of_range_eq_dynamicParabolic hG d.parabolicHom
        hpc chi d.parabolic_rep.2
      levi := ⟨inferInstance, d.levi_closed, hM,
        d.unipotent, d.unipotentHom, hrad, d.multiplication_isIso⟩
      parabolic_rep := d.parabolic_rep
      centralizer_rep := d.levi_rep }

end Dynamic

/-- An actual dynamic parabolic whose Levi source and ambient inclusion
are the original specified ones. -/
structure FixedLeviParabolicModel (j : L ⟶ G)
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  P : GroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  l : L ⟶ P
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup l
  comp : l ≫ p = j
  parabolic_rep : (Dynamic.parabolic chi).IsRepresentedBy p

/-- Reparametrize the canonical dynamic Levi by an actual representative
of the same centralizer. -/
def fixedLeviParabolicModel (hG : IsConnectedReductive G)
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {j : L ⟶ G} (hj : (Dynamic.centralizer chi).IsRepresentedBy j) :
    FixedLeviParabolicModel j chi := by
  let d := Dynamic.rationalParabolicModel hG chi
  let e : L ≅ d.M := hj.isoOfIsRepresentedBy d.centralizer_rep
  exact
    { P := d.P
      p := d.p
      l := e.hom ≫ d.m
      parabolic := d.parabolic
      levi := d.levi.iso_comp e
      comp := by simpa only [Category.assoc] using
        hj.isoOfIsRepresentedBy_hom_comp d.centralizer_rep
      parabolic_rep := d.parabolic_rep }

namespace RationalCocharacter

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Every regular rational direction has an actual parabolic with the
original specified representative of the whole torus centralizer as Levi. -/
def regularParabolicModel (hG : IsConnectedReductive G)
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G)
    {j : L ⟶ G} (hj : (torusCentralizer i).IsRepresentedBy j)
    {x : Space A} (hx : LinearAlgebra.FiniteHyperplaneSegment.Regular (rootForms i) x) :
    FixedLeviParabolicModel j
      (CommGroupScheme.groupHom (integralRealization hA x).cocharacter ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  apply fixedLeviParabolicModel hG _
  change (centralizer hA i x).IsRepresentedBy j
  rwa [centralizer_eq_torusCentralizer_of_regular hA i hx]

/-- The chosen actual rational parabolic retains the original embedded Levi
on every test scheme. -/
theorem isRationalParabolicWithLevi_of_regular (hG : IsConnectedReductive G)
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G)
    {j : L ⟶ G} (hj : (torusCentralizer i).IsRepresentedBy j)
    {x : Space A} (hx : LinearAlgebra.FiniteHyperplaneSegment.Regular (rootForms i) x) :
    IsRationalParabolicWithLevi j (parabolic hA i x) := by
  let d := regularParabolicModel hG hA i hj hx
  exact ⟨d.P, d.p, d.l, d.parabolic, d.levi, d.comp, d.parabolic_rep.2⟩

end RationalCocharacter

end Langlands.GroupScheme
