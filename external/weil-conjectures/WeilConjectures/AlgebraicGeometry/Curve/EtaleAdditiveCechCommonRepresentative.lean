/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaRepresentative
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaRepresentative

/-! # Common augmentation representatives

Source: Stacks Project, Tags 03P2 and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every global resolution cycle has a common total-complex class with a coefficient cycle.
Source: Stacks Project, Tag 03P2, the separated affine-cover comparison, and Tag 01FD,
the two augmentations of the injective Čech double complex.
(blueprint: new-w2-additive-cech-common-representative)

Proof: Restrictions to open subschemes preserve injectives, so the augmented Čech
rows of each resolution term are exact for the covering U. Hence alpha is a
quasi-isomorphism. On each finite intersection, the additive structure sheaf has
vanishing positive cohomology by affine quasi-coherent acyclicity. Consequently
beta is a quasi-isomorphism by the first-quadrant double-complex comparison.
The coordinate identification by restrictFunctorΓ and the additive universe lift
identifies its source with the ordinary unit Čech complex. Alpha sends s to a
cycle tα. Surjectivity of beta on homology gives a coefficient homology class
with image [tα]. Lift this class to a coefficient cycle z, and apply beta to get
tβ. The chain-map identities give the two cycle equations, and the chosen
class gives [tα]=[tβ]. At degree zero the same argument is the augmented kernel
calculation; an empty covering covers only the empty scheme and all groups are
zero. No normalized equivalence or scalar action on sheaf cohomology is used. -/
theorem additiveCech_common_representative
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (s : (additiveCechGlobal I).cycles n) :
    ∃ (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
      (tα tβ : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tα =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) ∧
      (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) ∧
      (additiveCechTotal U I).homologyπ n tα =
        (additiveCechTotal U I).homologyπ n tβ := by
  -- Only beta comparison and the alpha chain-map property are needed in this direction.
  have _hcover := hcover
  obtain ⟨tα, hα⟩ := additiveCech_alpha_representative U I n s
  obtain ⟨z, tβ, hβ, ht⟩ :=
    additiveCech_beta_representative X U hU I n ((additiveCechTotal U I).homologyπ n tα)
  exact ⟨z, tα, tβ, hα, hβ, ht.symm⟩

end AlgebraicGeometry.Scheme.Modules
