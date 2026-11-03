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

/-! # Descent along fppf homomorphisms with full central kernel -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace CenterQuotientDescent

variable {S : Scheme.{u}} {G A H : GroupScheme S} {q : G ⟶ A}

/-- For a homomorphism whose actual kernel is the full centre, central points
are exactly the points sent to the identity, on every test scheme. -/
theorem mem_center_iff (hq : IsSchemeTheoreticCenter (kernelι q))
    (T : Over S) (x : T ⟶ G.X) :
    x ∈ (center G).carrier T ↔ x ≫ q.hom.hom = 1 := by
  rw [← hq.2]
  constructor
  · rintro ⟨y, rfl⟩
    exact (kernelPointsEquiv q T y).property
  · intro hx
    refine ⟨(kernelPointsEquiv q T).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((kernelPointsEquiv q T).apply_symm_apply ⟨x, hx⟩)

/-- An invariant morphism agrees on all scheme-valued pairs with the same image. -/
theorem comp_eq_of_comp_eq (hq : IsSchemeTheoreticCenter (kernelι q))
    {Y : Over S} (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f)
    {Z : Scheme.{u}} (a b : Z ⟶ G.X.left)
    (h : a ≫ q.hom.hom.left = b ≫ q.hom.hom.left) :
    a ≫ f.left = b ≫ f.left := by
  have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← h, Category.assoc]
  let a' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk a rfl
  let b' : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk b hb
  have h' : a' ≫ q.hom.hom = b' ≫ q.hom.hom := Over.OverMorphism.ext h
  have hz : a'⁻¹ * b' ∈ (center G).carrier _ := by
    apply (mem_center_iff hq _ _).2
    rw [MonObj.mul_comp, GrpObj.inv_comp, h', inv_mul_cancel]
  have hab := hf _ a' (a'⁻¹ * b') hz
  rw [mul_inv_cancel_left] at hab
  exact (congrArg (fun x => x.left) hab).symm

variable (hq : IsSchemeTheoreticCenter (kernelι q))
variable [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]

/-- The descended scheme morphism for an arbitrary invariant target over the base. -/
def schemeDesc {Y : Over S} (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f) : A.X ⟶ Y :=
  Over.homMk
    (EffectiveEpi.desc q.hom.hom.left f.left
      (fun a b h => comp_eq_of_comp_eq hq f hf a b h)) (by
        apply (cancel_epi q.hom.hom.left).mp
        rw [EffectiveEpi.fac_assoc, Over.w, Over.w])

@[reassoc]
theorem comp_schemeDesc {Y : Over S} (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f) :
    q.hom.hom ≫ schemeDesc hq f hf = f :=
  Over.OverMorphism.ext (EffectiveEpi.fac q.hom.hom.left f.left
    (fun a b h => comp_eq_of_comp_eq hq f hf a b h))

/-- The scheme factorization is unique, with no restriction on the target scheme. -/
theorem schemeDesc_unique {Y : Over S} (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f)
    (g : A.X ⟶ Y) (hg : q.hom.hom ≫ g = f) : g = schemeDesc hq f hf := by
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact (congrArg (fun x => x.left) hg).trans
    (congrArg (fun x => x.left) (comp_schemeDesc hq f hf)).symm

/-- The actual product of an fppf homomorphism with itself is an epimorphism. -/
theorem epi_tensorHom : Epi (q.hom.hom ⊗ₘ q.hom.hom) := by
  let : MorphismProperty.IsStableUnderComposition (@Surjective) :=
    ⟨fun _ _ hf hg => ⟨hg.surj.comp hf.surj⟩⟩
  have : Flat (q.hom.hom ⊗ₘ q.hom.hom).left :=
    MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance
      (Over.w q.hom.hom).symm (Over.w q.hom.hom).symm
  have : Surjective (q.hom.hom ⊗ₘ q.hom.hom).left :=
    MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance
      (Over.w q.hom.hom).symm (Over.w q.hom.hom).symm
  have : LocallyOfFinitePresentation (q.hom.hom ⊗ₘ q.hom.hom).left :=
    MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) inferInstance inferInstance
      (Over.w q.hom.hom).symm (Over.w q.hom.hom).symm
  exact Over.epi_of_epi_left _

theorem isMonHom_schemeDesc (f : G ⟶ H) (hf : KillsCenter f) :
    IsMonHom (schemeDesc hq f.hom.hom hf.isInvariantUnderCenter) where
  one_hom := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc,
      comp_schemeDesc, IsMonHom.one_hom]
  mul_hom := by
    have := epi_tensorHom (q := q)
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, comp_schemeDesc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, comp_schemeDesc]

/-- Descent as an actual group-scheme homomorphism for any target group scheme. -/
def groupDesc (f : G ⟶ H) (hf : KillsCenter f) : A ⟶ H :=
  haveI := isMonHom_schemeDesc hq f hf
  Grp.homMk (schemeDesc hq f.hom.hom hf.isInvariantUnderCenter)

@[reassoc]
theorem comp_groupDesc (f : G ⟶ H) (hf : KillsCenter f) :
    q ≫ groupDesc hq f hf = f :=
  Grp.hom_ext _ _ (comp_schemeDesc hq f.hom.hom hf.isInvariantUnderCenter)

/-- The group factorization is unique, also for noncommutative targets. -/
theorem groupDesc_unique (f : G ⟶ H) (hf : KillsCenter f)
    (g : A ⟶ H) (hg : q ≫ g = f) : g = groupDesc hq f hf := by
  apply Grp.hom_ext
  exact schemeDesc_unique hq f.hom.hom hf.isInvariantUnderCenter g.hom.hom
    (congrArg (fun x => x.hom.hom) hg)

include hq

/-- The full scheme quotient universal property, on all targets over the base. -/
theorem schemeUniversalOfCenter (Y : Over S) (f : G.X ⟶ Y) (hf : IsInvariantUnderCenter f) :
    ∃! g : A.X ⟶ Y, q.hom.hom ≫ g = f :=
  ⟨schemeDesc hq f hf, comp_schemeDesc hq f hf,
    fun g hg => schemeDesc_unique hq f hf g hg⟩

/-- The full group quotient universal property, on all group schemes over the base. -/
theorem groupUniversal (H : GroupScheme S) (f : G ⟶ H) (hf : KillsCenter f) :
    ∃! g : A ⟶ H, q ≫ g = f :=
  ⟨groupDesc hq f hf, comp_groupDesc hq f hf,
    fun g hg => groupDesc_unique hq f hf g hg⟩

end CenterQuotientDescent

/-- The two universal properties of an actual adjoint quotient follow from fppf
descent once its geometric properties and full kernel-centre equality are known. -/
theorem IsAdjointQuotient.of_fppf
    {k : Type u} [Field k] {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hG : IsConnectedReductive G) (hA : IsAdjoint A)
    (hq : IsSchemeTheoreticCenter (kernelι q)) : IsAdjointQuotient q where
  isConnectedReductive := hG
  isAdjoint := hA
  flat := inferInstance
  surjective := inferInstance
  locallyOfFinitePresentation := inferInstance
  kernelCenter := hq
  groupUniversal := CenterQuotientDescent.groupUniversal hq
  schemeUniversal := CenterQuotientDescent.schemeUniversalOfCenter hq

end Langlands.GroupScheme
