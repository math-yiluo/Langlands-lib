import Langlands.AbelianScheme.LieRational
import Langlands.AbelianScheme.LieOrderBaseChange
import Langlands.AbelianScheme.LieBaseChangeNaturalityStatement

/-! # Rational Lie pullback from canonical integral naturality -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (b : T ⟶ S)
    (naturality : LieBaseChangeNaturalityStatement S)

include naturality

/-- The selected canonical comparisons intertwine all actual integral homomorphisms. -/
theorem lieMap_baseChange_of_naturality {A B : AbelianScheme S} (f : A ⟶ B) :
    (Scheme.Modules.pullback b).map (lieMap f) ≫ (lieBaseChangeIso b B).hom =
      (lieBaseChangeIso b A).hom ≫ lieMap ((baseChange b).map f) :=
  naturality T b A B f (lieBaseChangeIso b A) (lieBaseChangeIso b B)
    ((lieBaseChange S) T b A).1 ((lieBaseChange S) T b B).1
    (lieBaseChangeIso_characterization b A) (lieBaseChangeIso_characterization b B)

/-- Integral canonical naturality extends to every actual rational homomorphism. -/
theorem lieMap0_baseChange_of_naturality {A B : AbelianScheme S} (f : Hom0 A B) :
    (Scheme.Modules.pullback b).map (lieMap0 p f) ≫ (lieBaseChangeIso b B).hom =
      (lieBaseChangeIso b A).hom ≫ lieMap0 (b ≫ p) (rationalBaseChangeHom b f) := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  let := Langlands.Scheme.Modules.rationalLinearOverBase (b ≫ p)
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [map_add, lieMap0_add, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | tmul q f =>
    rw [lieMap0_tmul, Functor.map_smul, rationalBaseChangeHom_tmul, lieMap0_tmul,
      Linear.smul_comp, Linear.comp_smul, lieMap_baseChange_of_naturality b naturality f]

/-- The actual comparison between the two rational Lie pullback functors. -/
def rationalLieBaseChangeIso :
    rationalLieFunctor p ⋙ Scheme.Modules.pullback b ≅
      rationalBaseChange b ⋙ rationalLieFunctor (b ≫ p) :=
  NatIso.ofComponents (fun A => lieBaseChangeIso b A.obj) (by
    intro A B f
    exact lieMap0_baseChange_of_naturality p b naturality f)

@[simp]
theorem rationalLieBaseChangeIso_hom_app (A : RationalCategory S) :
    (rationalLieBaseChangeIso p b naturality).hom.app A =
      (lieBaseChangeIso b A.obj).hom := rfl

@[simp]
theorem rationalLieBaseChangeIso_inv_app (A : RationalCategory S) :
    (rationalLieBaseChangeIso p b naturality).inv.app A =
      (lieBaseChangeIso b A.obj).inv := rfl

omit naturality

/-- Pull back a rational order action through the constructed rational endomorphism map. -/
def baseChangeRationalOrderAction (B : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* End0 B) : O →+* End0 ((baseChange b).obj B) :=
  (rationalBaseChangeEnd b B).toRingHom.comp α

@[simp]
theorem baseChangeRationalOrderAction_apply (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B) (a : O) :
    baseChangeRationalOrderAction b B α a = rationalBaseChangeHom b (α a) := rfl

include naturality

/-- The actual rational action intertwines the same canonical Lie comparison. -/
theorem lieRationalOrderAction_baseChange_of_naturality (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B) (a : O) :
    (Scheme.Modules.pullback b).map (lieRationalOrderAction p B α a) ≫
        (lieBaseChangeIso b B).hom =
      (lieBaseChangeIso b B).hom ≫
        lieRationalOrderAction (b ≫ p) ((baseChange b).obj B)
          (baseChangeRationalOrderAction b B α) a :=
  lieMap0_baseChange_of_naturality p b naturality (α a)

omit naturality

/-- Restriction of pulled-back algebra actions agrees with pulled-back order restriction. -/
theorem baseChangeRationalOrderAction_comp (B : AbelianScheme S)
    {O P : Type v} [Ring O] [Ring P] (α : P →+* End0 B) (j : O →+* P) :
    baseChangeRationalOrderAction b B (α.comp j) =
      (baseChangeRationalOrderAction b B α).comp j := rfl

end Langlands.AbelianScheme
