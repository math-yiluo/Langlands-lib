import Langlands.AbelianScheme.IsogenyInverse
import Langlands.AbelianScheme.IsogenySpecialization

/-! # Factorization through actual isogenies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H J : Grp (Over S)}
variable [IsCommMonObj J.X]

/-- A homomorphism killing the scheme kernel agrees on every pair of scheme points
with the same image. -/
theorem hom_comp_eq_of_comp_eq (f : G ⟶ H) (g : G ⟶ J)
    (hg : kernelι f ≫ g = 1) {Z : Scheme.{u}} (a b : Z ⟶ G.X.left)
    (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) :
    a ≫ g.hom.hom.left = b ≫ g.hom.hom.left := by
  have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
    rw [← Over.w f.hom.hom, ← Category.assoc, ← h, Category.assoc]
  let a' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk a rfl
  let b' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk b hb
  have h' : a' ≫ f.hom.hom = b' ≫ f.hom.hom := Over.OverMorphism.ext h
  have hker : (a' / b') ≫ f.hom.hom = toUnit _ ≫ η[H.X] := by
    rw [GrpObj.div_comp, h', div_self']
    rfl
  let k := (kernel_isPullback f).lift (a' / b') (toUnit _) hker
  have hk : k ≫ (kernelι f).hom.hom = a' / b' := (kernel_isPullback f).lift_fst _ _ _
  have hzero : (a' / b') ≫ g.hom.hom = 1 := by
    rw [← hk, Category.assoc]
    change k ≫ (kernelι f ≫ g).hom.hom = 1
    rw [hg]
    exact MonObj.comp_one k
  have hab : a' ≫ g.hom.hom = b' ≫ g.hom.hom := by
    rw [GrpObj.div_comp, div_eq_one] at hzero
    exact hzero
  exact congrArg (fun x => x.left) hab

namespace IsogenyFactorization

variable {f : G ⟶ H} (hf : IsIsogeny f) (g : G ⟶ J)
  (hg : kernelι f ≫ g = 1)

/-- Descent of an actual scheme map killing the scheme kernel. -/
def schemeHom : H.X.left ⟶ J.X.left :=
  haveI := hf.effectiveEpi
  EffectiveEpi.desc f.hom.hom.left g.hom.hom.left
    (fun a b h => hom_comp_eq_of_comp_eq f g hg a b h)

@[reassoc]
theorem fac_schemeHom : f.hom.hom.left ≫ schemeHom hf g hg = g.hom.hom.left :=
  haveI := hf.effectiveEpi
  EffectiveEpi.fac _ _ _

/-- The descended morphism remains over the original base. -/
def overHom : H.X ⟶ J.X :=
  Over.homMk (schemeHom hf g hg) (by
    have := hf.effectiveEpi
    apply (cancel_epi f.hom.hom.left).mp
    rw [fac_schemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_overHom : f.hom.hom ≫ overHom hf g hg = g.hom.hom :=
  Over.OverMorphism.ext (fac_schemeHom hf g hg)

instance : IsMonHom (overHom hf g hg) where
  one_hom := by
    rw [← IsMonHom.one_hom f.hom.hom, Category.assoc, fac_overHom, IsMonHom.one_hom]
  mul_hom := by
    have := hf.epi_tensorHom
    apply (cancel_epi (f.hom.hom ⊗ₘ f.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, fac_overHom, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, fac_overHom]

/-- The unique descended actual group-scheme homomorphism. -/
def lift : H ⟶ J := Grp.homMk (overHom hf g hg)

@[reassoc]
theorem fac : f ≫ lift hf g hg = g :=
  Grp.hom_ext _ _ (fac_overHom hf g hg)

omit [IsCommMonObj J.X] in
include hf in
theorem hom_ext (a b : H ⟶ J) (h : f ≫ a = f ≫ b) : a = b := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have := hf.effectiveEpi
  apply (cancel_epi f.hom.hom.left).mp
  exact congrArg (fun k => k.hom.hom.left) h

theorem lift_unique (a : H ⟶ J) (ha : f ≫ a = g) : a = lift hf g hg :=
  hom_ext hf a _ (ha.trans (fac hf g hg).symm)

end IsogenyFactorization
end Langlands.GroupScheme
