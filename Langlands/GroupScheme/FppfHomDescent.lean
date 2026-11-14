import Langlands.GroupScheme.HomDescent

/-! # Homomorphism descent through an fppf group-scheme quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FppfHomDescent

variable {S : Scheme.{u}} {H Q G : GroupScheme S}
variable (q : H ⟶ Q) (f : H ⟶ G) (hk : kernelι q ≫ f = 0)
variable [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]

/-- Descend the underlying scheme morphism through an fppf quotient. -/
def schemeHom : Q.X.left ⟶ G.X.left :=
  EffectiveEpi.desc q.hom.hom.left f.hom.hom.left
    (fun h h' he => FpqcHomDescent.scheme_comp_eq_of_quotient_eq q f hk h h' he)

@[reassoc]
theorem fac_schemeHom : q.hom.hom.left ≫ schemeHom q f hk = f.hom.hom.left :=
  EffectiveEpi.fac _ _ _

/-- The descended scheme morphism is over the original base. -/
def overHom : Q.X ⟶ G.X :=
  Over.homMk (schemeHom q f hk) (by
    apply (cancel_epi q.hom.hom.left).mp
    rw [fac_schemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_overHom : q.hom.hom ≫ overHom q f hk = f.hom.hom :=
  Over.OverMorphism.ext (fac_schemeHom q f hk)

private abbrev fppfProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ (@Surjective ⊓ @LocallyOfFinitePresentation)

omit hk in
set_option backward.isDefEq.respectTransparency false in
/-- The product of an fppf quotient with itself is an epimorphism over the base. -/
theorem epi_tensorHom : Epi (q.hom.hom ⊗ₘ q.hom.hom) := by
  have hp : fppfProperty (q.hom.hom ⊗ₘ q.hom.hom).left :=
    MorphismProperty.pullbackMap (P := fppfProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w q.hom.hom).symm (Over.w q.hom.hom).symm
  let : Flat (q.hom.hom ⊗ₘ q.hom.hom).left := hp.1
  let : Surjective (q.hom.hom ⊗ₘ q.hom.hom).left := hp.2.1
  let : LocallyOfFinitePresentation (q.hom.hom ⊗ₘ q.hom.hom).left := hp.2.2
  exact Over.epi_of_epi_left _

/-- The descended morphism respects the unit and multiplication. -/
instance : IsMonHom (overHom q f hk) where
  one_hom := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, fac_overHom, IsMonHom.one_hom]
  mul_hom := by
    have := epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, fac_overHom, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, fac_overHom]

/-- The actual homomorphism descended through the specified fppf quotient. -/
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

include hk in
/-- A homomorphism killing the scheme kernel factors uniquely through any
flat surjective quotient locally of finite presentation. -/
theorem existsUnique_hom : ∃! d : Q ⟶ G, q ≫ d = f :=
  ⟨hom q f hk, fac q f hk, fun d hd => unique q f hk d hd⟩

end Langlands.GroupScheme.FppfHomDescent
