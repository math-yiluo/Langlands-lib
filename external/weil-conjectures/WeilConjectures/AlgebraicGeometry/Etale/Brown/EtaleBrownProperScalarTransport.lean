/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProperScalarMateIso
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProperScalarSquare

/-! # Proper scalar mate in normalized realizations

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The proper scalar projection and its local transport square.
Source: Zheng, Lemma 5.16; Stacks 0F0G, 0GL6 and 07A4.
(blueprint: lem-pur-etale-brown-proper-scalar-transport).

Proof: form the geometric right mate of the recorded derivedTensor. Its transport
through the normalized image and scalar comparisons is scalarMate: apply the scalar
Hom bijection, replace scalar comparisons by their restriction mates, and use the
unit-compatible direct-image squares on cochains. The ordinary restriction square
is the identity on sections in both encodings, so localization and the uniqueness
of the right-derived unit give the same restricted square. The scalar unit equation
then identifies the transposes. This proves the displayed local square. The proper
finite-coefficient projection theorem makes scalarMate invertible on every derived
input. All other factors in the square are isomorphisms, and RW.derived m reflects
isomorphisms; hence the recorded mate is invertible. Take its inverse isomorphism
as projection. This proof applies to nonflat quotients and the zero ring; no bound
on the input, no regularity, and no separatedness of the target is used. -/
theorem etaleBrownProperScalarTransport
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g]
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) [Finite (strictEtaleBrownRing O t n)] :
    ∃ p : (PV.scalar h).derived ⋙ (B.level m).direct ≅
        (B.level n).direct ⋙ (PW.scalar h).derived,
      p.inv = (mateEquiv (B.level n).adjunction (B.level m).adjunction
        (.mk _ _ _ _ (B.derivedTensor h).hom)) ∧
      ∀ P : DerivedCategory (strictEtaleLevel V O t n),
        (RW.derived m).map (p.inv.app P) ≫
          (rg m).right.hom.app ((PV.scalar h).derived.obj P) ≫
          (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
            g).rightDerivedFunctor.map ((RV.scalar h).hom.app P) =
        (RW.scalar h).hom.app ((B.level n).direct.obj P) ≫
          (Etale.scalarExtension (strictEtaleBrownRingMap O t h) W).map
            ((rg n).right.hom.app P) ≫
          (Etale.scalarMate (strictEtaleBrownRingMap O t h) g).app
            ((RV.derived n).obj P) := by
  let q := (mateEquiv (B.level n).adjunction (B.level m).adjunction
    (.mk _ _ _ _ (B.derivedTensor h).hom))
  letI : IsIso q := etaleBrownProperScalarMate_isIso O t g A PW PV B RV RW rg h
  let p : (PV.scalar h).derived ⋙ (B.level m).direct ≅
      (B.level n).direct ⋙ (PW.scalar h).derived := (asIso q).symm
  refine ⟨p, ?_, ?_⟩
  · exact rfl
  · apply etaleBrownProperScalarSquare O t g A PW PV B RV RW rg h p
    rfl

end AlgebraicGeometry
