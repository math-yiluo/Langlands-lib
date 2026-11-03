import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Homomorphism descent through an fpqc group-scheme quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FpqcHomDescent

variable {S : Scheme.{u}} {H Q G : GroupScheme S}
variable (q : H ⟶ Q) (f : H ⟶ G) (hk : kernelι q ≫ f = 0)

include hk

/-- A homomorphism killing the full scheme kernel agrees on equal quotient images. -/
theorem comp_eq_of_quotient_eq {T : Over S} (h h' : T ⟶ H.X)
    (he : h ≫ q.hom.hom = h' ≫ q.hom.hom) :
    h ≫ f.hom.hom = h' ≫ f.hom.hom := by
  have hd : (h / h') ≫ q.hom.hom = toUnit T ≫ η[Q.X] := by
    rw [GrpObj.div_comp, he, div_self']
    rfl
  let k := (kernel_isPullback q).lift (h / h') (toUnit T) hd
  have hki : k ≫ (kernelι q).hom.hom = h / h' :=
    (kernel_isPullback q).lift_fst _ _ _
  have hf : k ≫ (kernelι q).hom.hom ≫ f.hom.hom = 1 := by
    rw [← Grp.comp_hom_hom, hk]
    change k ≫ (toUnit (kernel q).X ≫ η[G.X]) = toUnit T ≫ η[G.X]
    rw [← Category.assoc, comp_toUnit]
  rw [← Category.assoc, hki, GrpObj.div_comp, div_eq_one] at hf
  exact hf

/-- The same equal-image criterion on arbitrary underlying schemes. -/
theorem scheme_comp_eq_of_quotient_eq {Z : Scheme.{u}}
    (h h' : Z ⟶ H.X.left)
    (he : h ≫ q.hom.hom.left = h' ≫ q.hom.hom.left) :
    h ≫ f.hom.hom.left = h' ≫ f.hom.hom.left := by
  have hs : h' ≫ H.X.hom = h ≫ H.X.hom := by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← he, Category.assoc]
  let h₀ : Over.mk (h ≫ H.X.hom) ⟶ H.X := Over.homMk h rfl
  let h₁ : Over.mk (h ≫ H.X.hom) ⟶ H.X := Over.homMk h' hs
  exact congrArg (fun x => x.left)
    (comp_eq_of_quotient_eq q f hk h₀ h₁ (Over.OverMorphism.ext he))

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
  [Surjective q.hom.hom.left]

/-- Descend the underlying scheme morphism. -/
def schemeHom : Q.X.left ⟶ G.X.left :=
  EffectiveEpi.desc q.hom.hom.left f.hom.hom.left
    (fun h h' he => scheme_comp_eq_of_quotient_eq q f hk h h' he)

@[reassoc]
theorem fac_schemeHom : q.hom.hom.left ≫ schemeHom q f hk = f.hom.hom.left :=
  EffectiveEpi.fac _ _ _

/-- The descended morphism is over the original base. -/
def overHom : Q.X ⟶ G.X :=
  Over.homMk (schemeHom q f hk) (by
    apply (cancel_epi q.hom.hom.left).mp
    rw [fac_schemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_overHom : q.hom.hom ≫ overHom q f hk = f.hom.hom :=
  Over.OverMorphism.ext (fac_schemeHom q f hk)

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

omit hk in
set_option backward.isDefEq.respectTransparency false in
/-- The product of the fpqc quotient with itself is an epimorphism over the base. -/
theorem epi_tensorHom : Epi (q.hom.hom ⊗ₘ q.hom.hom) := by
  have hp : fpqcProperty (q.hom.hom ⊗ₘ q.hom.hom).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w q.hom.hom).symm (Over.w q.hom.hom).symm
  let : QuasiCompact (q.hom.hom ⊗ₘ q.hom.hom).left := hp.1
  let : Flat (q.hom.hom ⊗ₘ q.hom.hom).left := hp.2.1
  let : Surjective (q.hom.hom ⊗ₘ q.hom.hom).left := hp.2.2
  exact Over.epi_of_epi_left _

instance : IsMonHom (overHom q f hk) where
  one_hom := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, fac_overHom, IsMonHom.one_hom]
  mul_hom := by
    have := epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, fac_overHom, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, fac_overHom]

/-- The actual homomorphism descended through the specified fpqc quotient. -/
def hom : Q ⟶ G := Grp.homMk (overHom q f hk)

@[reassoc]
theorem fac : q ≫ hom q f hk = f :=
  Grp.hom_ext _ _ (fac_overHom q f hk)

/-- Uniqueness among actual group-scheme homomorphisms. -/
theorem unique (d : Q ⟶ G) (hd : q ≫ d = f) : d = hom q f hk := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact congrArg (fun x => x.hom.hom.left) (hd.trans (fac q f hk).symm)

end Langlands.GroupScheme.FpqcHomDescent
