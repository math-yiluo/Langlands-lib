/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorSummandLocalizedExt
import WeilConjectures.Algebra.Homology.HomTensorDifferentialSummandPure

/-!
# Three-term expansion of the iterated Hom differential

Source: Stacks Project, Tag 0A90 and the calculation in Tag 0A5Y.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- On one tensor summand the curried iterated Hom differential has three terms.
Source: Stacks Project, Tag 0A90, using the sign calculation of Tag 0A5Y
(blueprint: lem-sc-hom-tensor-iterated-differential-summand).

Proof: Restrict to K^p tensor L^q. On any localized site expand the outer Hom
projection formula in homComplex_exists: its postcomposition term applies the
inner Hom differential to f(x), and its precomposition term evaluates f(d_K x).
Expand the inner differential to obtain d_M(f(x)(y)) minus
(-1)^(p+n) f(x)(d_L y); the outer precomposition contributes
minus (-1)^n f(d_K x)(y). Use homTensorDegreewiseMap_spec to identify
all evaluations with the degreewise comparison. Mathlib's d1 summand map is
x tensor y mapped to d_K x tensor y, while its d2 summand map is
(-1)^p x tensor d_L y. The identity (-1)^(p+n)=(-1)^n*(-1)^p
therefore gives the three displayed terms. Bilinearity extends from pure
tensors in the presheaf tensor, and the sheafification adjunction gives the
identity on the sheaf tensor summand. Localized evaluation identifies the
resulting internal Hom maps. The argument applies to all integer degrees and
also when any differential or complex vanishes. It does not assemble the
summands or combine the two tensor differential terms. -/
theorem homTensorDegreewiseMap_iteratedDifferential_summand
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1)))) =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) := by
  let := SheafOfModules.monoidalCategory R
  apply homTensorSummandLocalized_ext R (K.X p) (L.X q)
  intro U s W x y
  exact homTensorDifferential_summand_pure R K L M n t p q h U s W x y

end CategoryTheory
