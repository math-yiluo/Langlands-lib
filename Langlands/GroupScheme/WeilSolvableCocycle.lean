import Langlands.GroupScheme.AffineCocycleFppf
import Langlands.GroupScheme.Torus.PicardTrivialFppfCocycle

/-! # Global cocycles for extensions with a WeilGm quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SplitUnipotentAffineTorsor

namespace Cocycle

section Extension

variable {S : Scheme.{u}} {K H T : GroupScheme S} {U : Over S}
  (j : K ⟶ H) (q : H ⟶ T) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

include hjq in
/-- A quotient coboundary lifts to a coboundary of the original cocycle when
there is a scheme section and all kernel cocycles on the same cover vanish. -/
theorem isTrivial_of_extension_section
    (σ : T.X ⟶ H.X) (hσ : σ ≫ q.hom.hom = 𝟙 T.X)
    (hK : ∀ ζ : Cocycle K U, ζ.IsTrivial)
    (ξ : Cocycle H U) (hξ : (ξ.map q).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f₀, hf₀⟩ := hξ
  let f₁ : U ⟶ H.X := f₀ ≫ σ
  have hval : ∀ {Z : Over S} (a b : Z ⟶ U),
      ∃ k : Z ⟶ K.X, k ≫ j.hom.hom = (ξ.twist f₁).toFun a b := by
    intro Z a b
    refine exists_comp_eq_of_comp_eq_one hjq _ ?_
    have hab : ξ.toFun a b ≫ q.hom.hom = (a ≫ f₀) * (b ≫ f₀)⁻¹ := hf₀ a b
    change ((a ≫ f₁)⁻¹ * ξ.toFun a b * (b ≫ f₁)) ≫ q.hom.hom = 1
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, f₁, hσ,
      Category.comp_id, hab]
    group
  exact IsTrivial.of_twist (IsTrivial.of_lift (hK ((ξ.twist f₁).lift j hval)))

end Extension

section WeilExtension

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {K H T : GroupScheme (Spec A)}
  (j : K ⟶ H) (q : H ⟶ T) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  [IsAffine H.X.left] [IsAffine T.X.left]
  [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]
  (hK : CocyclesVanish K) (e : T ≅ WeilGm.groupScheme A B)
  {U : Over (Spec A)} [Flat U.hom] [Surjective U.hom]
  [LocallyOfFinitePresentation U.hom]

include hjq hK e in
/-- An affine extension of a supplied finite-projective WeilGm presentation
has trivial fppf cocycles when its kernel's affine cocycles vanish and the
coefficient algebra has trivial Picard group. -/
theorem isTrivial_of_weilExtension_fppf_of_pic_trivial
    [Subsingleton (CommRing.Pic B)] (ξ : Cocycle H U) : ξ.IsTrivial := by
  obtain ⟨σ, hσ⟩ := exists_section j q hjq hK
  exact ξ.isTrivial_of_extension_section j q hjq σ hσ
    (fun ζ => hK.isTrivial_on_fppf U ζ)
    ((ξ.map q).isTrivial_of_weilPresentation_fppf_of_pic_trivial e)

/-- Choose a cochain on the original fppf cover for an acyclic-kernel
extension of a supplied Picard-trivial WeilGm presentation. -/
def weilExtensionFppfPicardCochain [Subsingleton (CommRing.Pic B)]
    (ξ : Cocycle H U) : U ⟶ H.X :=
  Classical.choose (ξ.isTrivial_of_weilExtension_fppf_of_pic_trivial j q hjq hK e)

/-- The chosen extension cochain satisfies the coboundary equation on all tests. -/
theorem weilExtensionFppfPicardCochain_spec [Subsingleton (CommRing.Pic B)]
    (ξ : Cocycle H U) {Z : Over (Spec A)} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.weilExtensionFppfPicardCochain j q hjq hK e) *
      (b ≫ ξ.weilExtensionFppfPicardCochain j q hjq hK e)⁻¹ :=
  Classical.choose_spec
    (ξ.isTrivial_of_weilExtension_fppf_of_pic_trivial j q hjq hK e) a b

include hjq hK e in
/-- The finite-algebra Picard hypothesis supplies the coefficient Picard
triviality for the global extension argument. -/
theorem isTrivial_of_weilExtension_fppf_of_finiteAlgebrasHaveTrivialPicard
    (hA : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} A)
    (ξ : Cocycle H U) : ξ.IsTrivial := by
  let : Subsingleton (CommRing.Pic B) := hA B
  exact ξ.isTrivial_of_weilExtension_fppf_of_pic_trivial j q hjq hK e

include hjq hK e in
/-- Global fppf cocycle vanishing over a semi-local ring for an affine
extension with acyclic kernel and a supplied WeilGm quotient. -/
theorem isTrivial_of_weilExtension_fppf_of_semilocal
    [Finite (MaximalSpectrum A)] (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_finiteAlgebrasHaveTrivialPicard j q hjq hK e
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal A)

end WeilExtension

section VectorSeries

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {K H T : GroupScheme (Spec A)}
  (j : K ⟶ H) (q : H ⟶ T) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  [IsAffine H.X.left] [IsAffine T.X.left] [IsAffineHom K.X.hom]
  [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [LocallyOfFinitePresentation q.hom.hom.left]
  {n : ℕ} (hK : HasAffineVectorSeries n K) (e : T ≅ WeilGm.groupScheme A B)
  {U : Over (Spec A)} [Flat U.hom] [Surjective U.hom]
  [LocallyOfFinitePresentation U.hom]

include hjq hK e in
/-- A finite affine vector-quotient series supplies the kernel vanishing
required in the Picard-trivial extension theorem. -/
theorem isTrivial_of_vectorSeries_weilExtension_fppf_of_pic_trivial
    [Subsingleton (CommRing.Pic B)] (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_pic_trivial j q hjq
    (HasAffineVectorSeries.cocyclesVanish n K hK inferInstance) e

include hjq hK e in
/-- The semi-local specialization for a kernel with a supplied finite affine
vector-quotient series. -/
theorem isTrivial_of_vectorSeries_weilExtension_fppf_of_semilocal
    [Finite (MaximalSpectrum A)] (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_of_weilExtension_fppf_of_semilocal j q hjq
    (HasAffineVectorSeries.cocyclesVanish n K hK inferInstance) e

end VectorSeries

end Cocycle

end Langlands.GroupScheme
