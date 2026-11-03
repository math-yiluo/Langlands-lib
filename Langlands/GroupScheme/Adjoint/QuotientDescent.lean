import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.HomDescent

/-! # Descent of morphisms through a full-centre quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CenterQuotientDescent

variable {S : Scheme.{u}} {G A : GroupScheme S}
variable (q : G ⟶ A) (hker : SubgroupFunctor.range (kernelι q) = center G)

include hker

/-- A point killed by the quotient belongs to the full centre. -/
theorem mem_center_of_comp_eq_one {T : Over S} (x : T ⟶ G.X)
    (hx : x ≫ q.hom.hom = 1) : x ∈ (center G).carrier T := by
  rw [← hker]
  exact ⟨(kernelPointsEquiv q T).symm ⟨x, hx⟩,
    congrArg Subtype.val ((kernelPointsEquiv q T).apply_symm_apply ⟨x, hx⟩)⟩

variable {Y : Over S} (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f)

include hf

/-- Centre invariance makes a scheme map constant on equal quotient images. -/
theorem comp_eq_of_quotient_eq {T : Over S} (x y : T ⟶ G.X)
    (hxy : x ≫ q.hom.hom = y ≫ q.hom.hom) : x ≫ f = y ≫ f := by
  have hzq : (x⁻¹ * y) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
  have hz := mem_center_of_comp_eq_one q hker (x⁻¹ * y) hzq
  have he := hf T x (x⁻¹ * y) hz
  simpa only [mul_inv_cancel_left] using he.symm

/-- The equal-image relation also holds on arbitrary underlying scheme maps. -/
theorem scheme_comp_eq_of_quotient_eq {T : Scheme.{u}} (x y : T ⟶ G.X.left)
    (hxy : x ≫ q.hom.hom.left = y ≫ q.hom.hom.left) :
    x ≫ f.left = y ≫ f.left := by
  have hs : y ≫ G.X.hom = x ≫ G.X.hom := by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← hxy, Category.assoc]
  let x₀ : Over.mk (x ≫ G.X.hom) ⟶ G.X := Over.homMk x rfl
  let y₀ : Over.mk (x ≫ G.X.hom) ⟶ G.X := Over.homMk y hs
  exact congrArg (fun z => z.left)
    (comp_eq_of_quotient_eq q hker f hf x₀ y₀ (Over.OverMorphism.ext hxy))

variable [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]

/-- The descended underlying morphism exists by fppf effective epimorphy. -/
def schemeHom : A.X.left ⟶ Y.left :=
  EffectiveEpi.desc q.hom.hom.left f.left
    (fun x y hxy => scheme_comp_eq_of_quotient_eq q hker f hf x y hxy)

@[reassoc]
theorem fac_schemeHom : q.hom.hom.left ≫ schemeHom q hker f hf = f.left :=
  EffectiveEpi.fac _ _ _

/-- The descended morphism retains the actual structure map to the base. -/
def overHom : A.X ⟶ Y :=
  Over.homMk (schemeHom q hker f hf) (by
    apply (cancel_epi q.hom.hom.left).mp
    rw [fac_schemeHom_assoc, Over.w, Over.w])

theorem fac_overHom : q.hom.hom ≫ overHom q hker f hf = f :=
  Over.OverMorphism.ext (fac_schemeHom q hker f hf)

/-- Arbitrary centre-invariant scheme maps factor uniquely through the quotient. -/
theorem schemeUniversal :
    ∃! g : A.X ⟶ Y, q.hom.hom ≫ g = f := by
  refine ⟨overHom q hker f hf, fac_overHom q hker f hf, ?_⟩
  intro g hg
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact congrArg (fun z => z.left) (hg.trans (fac_overHom q hker f hf).symm)

end CenterQuotientDescent

section Field

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}

/-- For an fppf map to an adjoint group, the actual full-centre kernel already
implies both arbitrary-target universal properties of an adjoint quotient. -/
theorem isAdjointQuotient_of_fppf
    (q : G ⟶ A) (hG : IsConnectedReductive G) (hA : IsAdjoint A)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left)
    (hcenter : IsSchemeTheoreticCenter (kernelι q)) : IsAdjointQuotient q := by
  let : Flat q.hom.hom.left := hflat
  let : Surjective q.hom.hom.left := hsurj
  let : LocallyOfFinitePresentation q.hom.hom.left := hlfp
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom A.X.hom := hA.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  refine ⟨hG, hA, hflat, hsurj, hlfp, hcenter, ?_, ?_⟩
  · intro H f hf
    have hk : kernelι q ≫ f = 0 := by
      apply Grp.hom_ext
      change (kernelι q).hom.hom ≫ f.hom.hom = 1
      have h := hf (kernel q).X (kernelι q).hom.hom
        (by simpa only [Category.id_comp] using
          hcenter.isCentral (kernel q).X (𝟙 (kernel q).X))
      simpa only [Category.id_comp] using h
    exact ⟨FpqcHomDescent.hom q f hk, FpqcHomDescent.fac q f hk,
      fun g hg => FpqcHomDescent.unique q f hk g hg⟩
  · intro Y f hf
    exact CenterQuotientDescent.schemeUniversal q hcenter.2 f hf

end Field

end Langlands.GroupScheme
