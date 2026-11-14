import Langlands.Geometry.FormalGroup.DeligneAdmissibility
import Langlands.Geometry.FormalGroup.DelignePreDatumBaseChange
import Langlands.Geometry.FormalGroup.DeligneInverseImageCoherence
import Langlands.Geometry.FormalGroup.DeligneZeroLocusBaseChange

/-! # Base change of constancy on the actual Pi-zero loci -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {S S' : Scheme.{u}}
  {d : ℕ} [NeZero d] {π : O} {F : Type u} [Field F] [Algebra O F]
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- The actual zero-locus map for the four pulled preliminary data. -/
def piZeroPullbackMap (i : ZMod d) :
    (D.pullback f).piZeroSpace i ⟶ D.piZeroSpace i :=
  D.tangent.piZeroPullbackMap f i

/-- The zero-locus map commutes with the actual inclusions into the bases. -/
theorem piZeroPullbackMap_inclusion (i : ZMod d) :
    D.piZeroPullbackMap f i ≫ D.piZeroInclusion i =
      (D.pullback f).piZeroInclusion i ≫ f.base := by
  ext x
  rfl

/-- Restriction of the pulled lattice component is inverse image of its original
restriction along the actual map of zero loci. -/
def componentOnPiZeroLocusPullbackIso (i : ZMod d) :
    (D.pullback f).componentOnPiZeroLocus i ≅
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) (D.piZeroPullbackMap f i)).obj
        (D.componentOnPiZeroLocus i) :=
  (inverseImageCompIso O f.base ((D.pullback f).piZeroInclusion i)).app
      (D.eta.lattice.component i) ≪≫
    eqToIso (congrArg
      (fun g : (D.pullback f).piZeroSpace i ⟶ (S : TopCat) =>
        (TopCat.Sheaf.pullback (ModuleCat.{u} O) g).obj (D.eta.lattice.component i))
      (D.piZeroPullbackMap_inclusion f i).symm) ≪≫
    ((inverseImageCompIso O (D.piZeroInclusion i) (D.piZeroPullbackMap f i)).app
      (D.eta.lattice.component i)).symm

/-- Condition (a) is preserved by actual base change of the four data. -/
theorem ConstantOnPiZeroLoci.pullback (h : D.ConstantOnPiZeroLoci) :
    (D.pullback f).ConstantOnPiZeroLoci := by
  intro i
  obtain ⟨e⟩ := h i
  exact ⟨D.componentOnPiZeroLocusPullbackIso f i ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) (D.piZeroPullbackMap f i)).mapIso e ≪≫
    (inverseImageConstantIso (O := O) (D.piZeroPullbackMap f i)).app
      (ModuleCat.of O (Fin d → O))⟩

end SheafPreDatum

end Langlands.DeligneFormalSpace
