/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates
public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized
import WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionEvaluation

/-! # Residue naturality of explicit rank-one tensor coordinates

Source: Stacks Project, Tags 0096 and 0BF2.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Raw residue restriction evaluates the normalized rank-one coordinate.
Source: Stacks Project, Tag 0096, composition of the tensor adjunction;
Tag 0BF2, degree-zero calculation.
(blueprint: lem-sc-picard-tensor-frame-restriction)

Proof: Write L_g for tensorPullback g and epsilon_g for its pinned unit
isomorphism. For i followed by g equal to g', let A_g : L_g' ≅ L_g ⋙ L_i
be exactly the conjugate comparison in picardOrdinaryModelRestriction. Its unit
compatibility is
A_g.hom.app O ≫ L_i.map epsilon_g ≫ epsilon_i = epsilon_g'.
To check this equation, apply the direct adjunction homEquiv. The mate unit
equation and naturality turn its left side into the composite of g-sharp with
g_*(i-sharp), transported by pushforwardComp and pushforwardCongr. On every
open and section this is g'-sharp by the scheme morphism composition formula.
The right side has this same adjunct by the definition of epsilon_g'.
Injectivity of homEquiv proves the compatibility, for each of t and s.

Put n = epsilon_t.inv ≫ f ≫ L_s.map q.hom ≫ epsilon_s. Naturality of A_s
with respect to q and the two compatibility equations show that normalization
of A_t.hom ≫ L_i.map f ≫ A_s.inv is
 epsilon_i.inv ≫ L_i.map n ≫ epsilon_i.
Apply the adjunction to this conjugated unit endomorphism and evaluate at one;
unit naturality gives i.appTop applied to n's value at one (the same calculation
as the tensor-unit conjugation in PicardTensorFrameCoordinates).
For i the residue lift to V, factor i as Spec of the residue quotient followed
by the stalk lift to V. Composing the stalk lift with V.toSpecΓ is Spec of the
germ map. Consequently ΓSpecIso κ(w), followed after i.appTop and V.topIso.inv,
is W.evaluation V w hwV. Substituting the normalized value n(1) proves the
displayed equality. No differential, perfectness, cycle membership or
annihilation of coefficients is used. -/
theorem picardTensorFrame_restriction
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (q : (Modules.overEquiv U).functor.obj (K.X 0) ≅ Modules.unit U.toScheme)
    (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U)
    (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU =
      picardResidueLift W w U hwU)
    (f : (Modules.tensorPullback V.ι).obj (Modules.unit W) ⟶
      (Modules.tensorPullback (W.homOfLE hVU)).obj
        ((Modules.overEquiv U).functor.obj (K.X 0))) :
    (ΓSpecIso (W.residueField w)).hom
      (Modules.picardTensorScalarCoordinate (W.fromSpecResidueField w)
        (picardResidueLift W w U hwU) q
        (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV)
          V.ι (W.fromSpecResidueField w) (W.homOfLE hVU)
          (picardResidueLift W w U hwU) (picardResidueLift_comp W w V hwV) hs f)) =
      W.evaluation V w hwV
        (V.topIso.hom (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f)) := by
  rw [picardTensorFrame_restriction_normalized]
  have he := picardResidueLift_appTop_eval W w V hwV
    (V.topIso.hom (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f))
  simpa only [Iso.hom_inv_id_apply] using he

end AlgebraicGeometry.Scheme
