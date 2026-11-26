import Langlands.AbelianScheme.MultiplicationSpecialization
import Langlands.Geometry.EtaleDerivedAdjunction
import Langlands.Geometry.EtaleDerivedInverseImageCoherence
import Langlands.Geometry.EtaleInverseImageConstant
import Mathlib.Data.ZMod.Basic

/-!
# Multiplication on relative étale cohomology of an abelian scheme

The degree-dependent scalar action used in the multiplication-by-two
projectors of Harris–Taylor III.2, p. 98, at finite prime-power
coefficients. It follows from the geometric exterior-algebra calculation
and proper base change.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry
open EtaleDerivedSections EtaleDerivedDirectImage EtaleDerivedInverseImage

universe u wS wX wY

set_option autoImplicit false

namespace Langlands.Cohomology.AbelianRelativeEtale

private abbrev constantModule {R : Type u} [CommRing R] (X : Scheme.{u}) (M : ModuleCat.{u} R) :
    ModuleSheaf X R :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M

section Pullback

variable {S X Y : Scheme.{u}} (R : Type u) [CommRing R]
  [HasDerivedCategory.{wS} (ModuleSheaf S R)]
  [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
  {f : X ⟶ S} {g : Y ⟶ S} (a : Y ⟶ X) (over : a ≫ f = g)

/-- Relative pullback on the derived direct images of a constant coefficient
module. Apply the derived unit for `a` and compare the composite direct
image with the direct image of `g`. -/
def relativeConstantDerivedPullback (M : ModuleCat.{u} R) :
    (derivedDirectImage f R).obj (constantModule X M) ⟶
      (derivedDirectImage g R).obj (constantModule Y M) :=
  let aAdj := EtaleDerivedAdjunction.adjunction a R
  let fAdj := EtaleDerivedAdjunction.adjunction f R
  let gAdj := EtaleDerivedAdjunction.adjunction g R
  let compPullback : plusFunctor f R ⋙ plusFunctor a R ≅ plusFunctor g R :=
    plusFunctorComp R f a ≪≫ eqToIso (congrArg (fun h => plusFunctor h R) over)
  let compPushforward := (fAdj.comp aAdj).rightAdjointUniq (gAdj.ofNatIsoLeft compPullback.symm)
  let L := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).obj (constantModule X M)
  let constantPullback :=
    (plusSingleIso a R 0).hom.app (constantModule X M) ≫
      (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y R) 0).map
        ((EtaleInverseImage.inverseImageConstantIso a R).hom.app M)
  (rightDerivedFunctor f R).map (aAdj.unit.app L) ≫
    compPushforward.hom.app ((plusFunctor a R).obj L) ≫
    (rightDerivedFunctor g R).map constantPullback

/-- Relative pullback in degree `q`, on the actual higher direct images
of the constant coefficient module. -/
def relativeConstantCohomologyPullback (M : ModuleCat.{u} R) (q : ℕ) :
    (higherDirectImage f R q).obj (constantModule X M) ⟶
      (higherDirectImage g R q).obj (constantModule Y M) :=
  (homologyNatIso f R q).inv.app (constantModule X M) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleSheaf S R) q).map
      (relativeConstantDerivedPullback R a over M) ≫
    (homologyNatIso g R q).hom.app (constantModule Y M)

end Pullback

/-- Multiplication by an integer `m` acts by `m^q` on the `q`th higher
direct image of an abelian scheme with constant `ℤ/p^rℤ` coefficients,
where the prime `p` is invertible on the base. -/
def RelativeAbelianMultiplicationCohomologyStatement {S : Scheme}
    (A : Langlands.AbelianScheme S) (p r q : ℕ) (m : ℤ) [Fact p.Prime]
    [HasDerivedCategory.{wS} (ModuleSheaf S (ZMod (p ^ r)))]
    [HasDerivedCategory.{wX} (ModuleSheaf A.X.left (ZMod (p ^ r)))] : Prop :=
  IsUnit (p : Γ(S, ⊤)) →
    let a := Langlands.AbelianScheme.groupHom (Langlands.AbelianScheme.multiplication A m)
    relativeConstantCohomologyPullback (f := A.X.hom) (g := A.X.hom)
      (ZMod (p ^ r)) a.hom.hom.left a.hom.hom.w
      (ModuleCat.of (ZMod (p ^ r)) (ZMod (p ^ r))) q = m ^ q • 𝟙 _

end Langlands.Cohomology.AbelianRelativeEtale
