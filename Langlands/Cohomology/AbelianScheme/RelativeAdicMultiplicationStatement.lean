import Langlands.AbelianScheme.MultiplicationSpecialization
import Langlands.Geometry.EtaleDerivedAdjunction
import Langlands.Geometry.EtaleDerivedInverseImageCoherence
import Langlands.Geometry.EtaleInverseImageConstant
import Langlands.Geometry.EtaleAdicSystem
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Multiplication on the relative adic cohomology system

The finite-stage scalar calculation from Milne, *Abelian Varieties*,
§15, expressed on the quotient diagram of a single p-adic coefficient ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry EtaleDerivedSections EtaleDerivedDirectImage EtaleDerivedInverseImage

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

universe u wS wX wY

namespace Langlands.Cohomology.AbelianRelativeEtale

section NaturalPullback

variable {S X Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {f : X ⟶ S} {g : Y ⟶ S} (a : Y ⟶ X) (over : a ≫ f = g)
variable [HasDerivedCategory.{wS} (ModuleSheaf S R)]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]

/-- The pullback on relative derived direct images is natural in the
constant coefficient module. -/
def relativeConstantDerivedPullbackNat :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙ derivedDirectImage f R ⟶
      constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⋙ derivedDirectImage g R :=
  let cx := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let cy := constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)
  let sx := DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0
  let sy := DerivedCategory.Plus.singleFunctor (ModuleSheaf Y R) 0
  let aAdj := EtaleDerivedAdjunction.adjunction a R
  let fAdj := EtaleDerivedAdjunction.adjunction f R
  let gAdj := EtaleDerivedAdjunction.adjunction g R
  let compPullback : plusFunctor f R ⋙ plusFunctor a R ≅ plusFunctor g R :=
    plusFunctorComp R f a ≪≫ eqToIso (congrArg (fun h => plusFunctor h R) over)
  let compPushforward := (fAdj.comp aAdj).rightAdjointUniq (gAdj.ofNatIsoLeft compPullback.symm)
  let pull : cx ⋙ sx ⋙ plusFunctor a R ⟶ cy ⋙ sy :=
    Functor.whiskerLeft cx (plusSingleIso a R 0).hom ≫
      Functor.whiskerRight (EtaleInverseImage.inverseImageConstantIso a R).hom sy
  Functor.whiskerLeft (cx ⋙ sx) (Functor.whiskerRight aAdj.unit (rightDerivedFunctor f R)) ≫
    Functor.whiskerLeft (cx ⋙ sx ⋙ plusFunctor a R) compPushforward.hom ≫
    Functor.whiskerRight pull (rightDerivedFunctor g R)

/-- The finite-degree pullback on the actual higher direct images is
natural in the constant coefficient module. -/
def relativeConstantCohomologyPullbackNat (q : ℕ) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙ higherDirectImage f R q ⟶
      constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⋙ higherDirectImage g R q :=
  Functor.whiskerLeft _ (homologyNatIso f R q).inv ≫
    Functor.whiskerRight (relativeConstantDerivedPullbackNat R a over)
      (DerivedCategory.Plus.homologyFunctor (ModuleSheaf S R) q) ≫
    Functor.whiskerLeft _ (homologyNatIso g R q).hom

end NaturalPullback

section AdicDiagram

variable (p : ℕ) [Fact p.Prime]
variable {S X Y : Scheme.{0}}

local notation "R" => ℤ_[p]

/-- The actual `R^q f_*` sheaves for the constant prime-power coefficient
system. The arrows come from coefficient reduction over `ℤ_p`. -/
def relativeAdicCohomologySystem (f : X ⟶ S) (q : ℕ) :
    ℕᵒᵖ ⥤ ModuleSheaf S R :=
  EtaleAdicSystem.ellPowerConstantSystem X p (ModuleCat.of R R) ⋙ higherDirectImage f R q

variable [HasDerivedCategory.{wS} (ModuleSheaf S ℤ_[p])]
variable [HasDerivedCategory.{wX} (ModuleSheaf X ℤ_[p])]
variable [HasDerivedCategory.{wY} (ModuleSheaf Y ℤ_[p])]

/-- Pullback over `S` at every finite coefficient stage, with the naturality
squares for the reductions. -/
def relativeAdicCohomologyPullback {f : X ⟶ S} {g : Y ⟶ S}
    (a : Y ⟶ X) (over : a ≫ f = g) (q : ℕ) :
    relativeAdicCohomologySystem p f q ⟶ relativeAdicCohomologySystem p g q :=
  Functor.whiskerLeft _ (relativeConstantCohomologyPullbackNat R a over q)

/-- For `p` invertible on the base, multiplication by `m` on an abelian
scheme acts as `m^q` on the entire prime-power relative cohomology diagram. -/
def RelativeAdicMultiplicationCohomologyStatement (A : Langlands.AbelianScheme S)
    [HasDerivedCategory.{wX} (ModuleSheaf A.X.left ℤ_[p])] (m : ℤ) (q : ℕ) : Prop :=
  IsUnit (p : Γ(S, ⊤)) →
    let a := Langlands.AbelianScheme.groupHom (Langlands.AbelianScheme.multiplication A m)
    relativeAdicCohomologyPullback.{wS, wX, wX} p a.hom.hom.left a.hom.hom.w q = m ^ q • 𝟙 _

end AdicDiagram

end Langlands.Cohomology.AbelianRelativeEtale
