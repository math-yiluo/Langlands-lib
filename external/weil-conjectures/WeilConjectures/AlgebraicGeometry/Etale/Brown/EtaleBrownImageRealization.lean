/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealizationOrdinary
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealizationDerived
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealizationInverse

/-! # Normalized realization of a geometric image

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
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- A normalized image comparison for the supplied geometric derived adjunction.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4.
(blueprint: lem-pur-etale-brown-image-realization).

Proof: the ordinary direct-image comparison is the identity on sections, followed
by A.rightUnderlying. Naturality of the structural constant-ring map makes this
map linear; the inverse has the identical sections. Exact equivalences preserve
K-injectivity, so the supplied universal right-derived functor and the published
right-derived lowerStar are right-derived functors of this same ordinary square.
Their unique unit-compatible comparison is an isomorphism and gives exactly the
displayed cochain-unit equation. Take its inverse mate to define inverse. The
realization functors are equivalences, so this mate is invertible. Its normalization
is the mate inverse law. The ordinary transpose of B and the published geometric
transpose identify this with localization of inverse image. No properness or
coefficient finiteness is used. In particular the identity map, empty schemes,
and zero coefficient ring are covered by the same universal properties. -/
theorem etaleBrownImageRealization_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW) :
    Nonempty (StrictEtaleBrownImageRealization O t g n A B RV RW) := by
  classical
  obtain ⟨ordinaryRight, hordinary⟩ :=
    etaleBrownImageRealization_ordinaryRight_exists O t g n A RV RW
  obtain ⟨right, hright⟩ :=
    etaleBrownImageRealization_right_exists O t g n A B RV RW ordinaryRight hordinary
  obtain ⟨inverse, hinverse⟩ :=
    etaleBrownImageRealization_inverse_exists O t g n A B RV RW ordinaryRight right hright
  exact ⟨⟨⟨ordinaryRight, right, inverse⟩, hordinary, hright, hinverse⟩⟩

end AlgebraicGeometry
