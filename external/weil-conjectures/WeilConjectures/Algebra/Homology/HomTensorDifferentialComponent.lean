/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferentialSummand
import WeilConjectures.Algebra.Homology.HomTensorSummandRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# Component of the iterated Hom differential after currying

Source: Stacks Project, Tag 0A90 and its referenced calculation in Tag 0A5Y.
(blueprint: lem-sc-hom-tensor-iterated-differential-component).
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

private lemma homObjMap_add_first {A A' B : Mod} (f g : A' ⟶ A) :
    SheafOfModules.homObjMap (R := R) (f + g) (𝟙 B) =
      SheafOfModules.homObjMap (R := R) f (𝟙 B) +
        SheafOfModules.homObjMap (R := R) g (𝟙 B) :=
  SheafOfModules.hom_ext
    (PresheafOfModules.homObjMap_add_left (R := R.obj) f.val g.val (𝟙 B.val))

-- Rewriting the total-complex differential elaborates the dependent coproduct indices.
set_option synthInstance.maxSize 256 in
/-- The component of the iterated Hom differential after degreewise currying.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90),
compatibility with differentials
(blueprint: lem-sc-hom-tensor-iterated-differential-component).

Proof: Fix the total source degree t. Expand the outer Hom differential and
then the inner Hom differential using the projection formula in
`homComplex_exists`. On the summand K^p tensor L^q with p+q=t, the currying
condition identifies the resulting localized maps with
 d_M(f(x)(y)) - (-1)^(p+n) f(x)(d_L y) - (-1)^n f(d_K x)(y).
The total tensor differential sends x tensor y to
 d_K x tensor y + (-1)^p x tensor d_L y.
Using (-1)^(p+n)=(-1)^n*(-1)^p, these are precisely the postcomposition
term and the signed precomposition term displayed below. Extend the equality
from pure tensors by bilinearity, then by the sheafification adjunction on
each summand and the coproduct universal property in total degree t.
Finally check sections on every localized site to get equality in the
internal Hom factor. This computes only the iterated-Hom side at one product
factor; the target Hom differential and joint monicity are handled separately.
Zero complexes or zero differentials give zero on both sides; negative integer
degrees use the same negOnePow addition identity. -/
theorem homTensorDegreewiseMap_iteratedDifferential_component
    (K L M : CochainComplex Mod ℤ) (n t : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (T.X t)) (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.d t (t + 1)) (𝟙 (M.X (t + (n + 1))))) :=
  by
    let := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    apply homTensorSummandRestriction_ext R K L t
    intro p q h
    simpa only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      homObjMap_add_first, smul_add, ← sub_sub] using
      homTensorDegreewiseMap_iteratedDifferential_summand R K L M n t p q h

end CategoryTheory
