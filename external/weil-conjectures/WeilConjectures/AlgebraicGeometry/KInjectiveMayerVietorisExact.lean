/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise

/-! # Exactness of the concrete direct-image Mayer--Vietoris complex

Source: Stacks Project, Cohomology, Tag 08BV, proof of Lemma 20.33.2,
using Tag 01EB and Tag 01EA.
(blueprint: lem-pc-kinjective-mayer-vietoris-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- The concrete restriction/direct-image diagram is short exact for a cover and
an arbitrary complex with injective terms. K-injectivity is not needed here.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
last paragraph; Tag 01EB (lemma-mayer-vietoris), first paragraph of its proof.
(blueprint: lem-pc-kinjective-mayer-vietoris-exact).

Proof: The transported underived adjunction is the restriction/direct-image
adjunction. On sections over a test open T its unit is restriction from T to
T ∩ U. For W ⊆ U, the mate of the restricted counit is restriction from
T ∩ U to T ∩ W: transpose this sectionwise restriction along the adjunction,
where the inverse composition comparison restricts twice, the counit removes
the repeated U-restriction, and the forward comparison identifies the result
with restriction to W. Thus in degree n the two arrows are the pair of
restrictions and their difference. The two opens T ∩ U and T ∩ V cover T.
Sheaf uniqueness makes the first arrow injective. A pair killed by the
second arrow agrees on the intersection, so sheaf gluing gives a preimage
under the first arrow. For an intersection section, use
injective_restriction_surjective on T ∩ U ∩ V ⊆ T ∩ U for I.X n,
and take zero in the V component. Hence the second arrow is surjective.
The sectionwise calculation gives the kernel universal property for the
first arrow in presheaf modules. Since all three terms are sheaves and their
inclusion into presheaf modules is fully faithful, this remains a kernel
universal property for sheaves. The first arrow is monic by sectionwise
injectivity, and the second is epic by sectionwise surjectivity. Finally apply
HomologicalComplex.shortExact_of_degreewise_shortExact. Empty or repeated
opens require no separate argument: the same sheaf gluing and lifting work. -/
theorem schemeMayerVietorisComplex_shortExact
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    (schemeMayerVietorisComplex X U V I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact schemeMayerVietorisComplex_degreewise_shortExact X U V hcover I n (hI n)

end AlgebraicGeometry
