/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# The normal cone of a closed immersion

Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `I`. The *normal cone* is
`N_{Z/X} = Spec_Z (⨁_{r ≥ 0} I^r / I^{r+1})`. It is constructed as the relative spectrum over `X`
of the associated graded algebra `𝒪_X[t, I t⁻¹] / t = ⨁_{r ≥ 0} I^r / I^{r+1}`
(`AlgebraicGeometry.Scheme.IdealSheafData.normalCone`), which is an algebra over `𝒪_X / I`
(`AlgebraicGeometry.Scheme.IdealSheafData.quotientToNormalCone`, the inclusion of the degree zero
part). Hence the normal cone lies over the closed subscheme `V(I) ≅ Z`
(`AlgebraicGeometry.Scheme.Hom.normalBundleProj`), and the augmentation
`⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_X / I` defines its *zero section*
`AlgebraicGeometry.Scheme.Hom.normalConeZeroSection`, a closed immersion and a section of the
projection (`AlgebraicGeometry.Scheme.Hom.normalConeZeroSection_normalBundleProj`). For a regular
immersion of pure codimension `c` the normal cone is a vector bundle of rank `c`
(`AlgebraicGeometry.Scheme.Hom.isVectorBundle_normalBundleProj` in
`WeilConjectures.AlgebraicGeometry.NormalBundleRegular`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.AffineZariskiSite

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

lemma algebraMap_mem_tIdeal (U : X.AffineZariskiSiteᵒᵖ) {a : Γ(X, U.unop.1)}
    (ha : a ∈ I.siteIdeal U.unop) :
    algebraMap _ (I.siteIdeal U.unop).extendedReesAlgebra a ∈ I.tIdeal U := by
  refine Ideal.mem_span_singleton'.2
    ⟨⟨LaurentPolynomial.C a * LaurentPolynomial.T (-1),
      Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra ha⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, Ideal.coe_extendedReesAlgebraT,
    Ideal.coe_algebraMap_extendedReesAlgebra, mul_assoc, ← LaurentPolynomial.T_add]
  simp

/-- The inclusion `𝒪_X / I ⟶ ⨁_{r ≥ 0} I^r / I^{r+1}` of the degree zero part: an element of `I`
is `(x t⁻¹) · t`, which vanishes modulo `t`. -/
@[simps]
noncomputable def quotientToNormalCone : I.quotientAlgebra ⟶ I.normalConePresheaf where
  app U := CommRingCat.ofHom (Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (I.tIdeal U)).comp (I.toReesPresheaf.app U).hom)
    fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.2 (I.algebraMap_mem_tIdeal U ha))
  naturality U V i := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change Ideal.Quotient.mk _
        ((I.toReesPresheaf.app V).hom ((X.affineStructurePresheaf.map i).hom x)) =
      Ideal.Quotient.mk _ ((I.reesPresheaf.map i).hom ((I.toReesPresheaf.app U).hom x))
    exact congrArg _ (I.toReesPresheaf.naturality_apply i x)

lemma toQuotientAlgebra_comp_quotientToNormalCone :
    I.toQuotientAlgebra ≫ I.quotientToNormalCone =
      I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal := by
  ext U x
  rfl

lemma quotientToNormalCone_comp_normalConeToQuotient :
    I.quotientToNormalCone ≫ I.normalConeToQuotient = 𝟙 _ := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)))
  exact congr($(I.toNormalConePresheaf_comp_normalConeToQuotient).app U x)

/-- The projection `N_I X ⟶ V(I)` of the normal cone to the closed subscheme. -/
noncomputable def normalConeToQuotientSpec : I.normalCone ⟶ I.quotientSpec :=
  relativeGluingMap I.coequifibered_toQuotientAlgebra I.coequifibered_toNormalConePresheaf
    I.quotientToNormalCone

lemma normalConeToQuotientSpec_toBase :
    I.normalConeToQuotientSpec ≫ (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase =
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase :=
  relativeGluingMap_toBase _ _ _ I.toQuotientAlgebra_comp_quotientToNormalCone

end Scheme.IdealSheafData

namespace Scheme.Hom

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `prose-09-11`: Normal bundle and zero section

The projection `π : N_{Z/X} ⟶ Z` of the normal cone `N_{Z/X} = Spec_Z (⨁_{r ≥ 0} I^r / I^{r+1})`
(`AlgebraicGeometry.Scheme.IdealSheafData.normalCone` of the ideal sheaf `I` of `i`) of a closed
immersion `i : Z ⟶ X`: the projection to `V(I) ≅ Z`, given by the inclusion of the degree zero part
`𝒪_X / I ⟶ ⨁_{r ≥ 0} I^r / I^{r+1}`. -/
noncomputable def normalBundleProj : i.ker.normalCone ⟶ Z :=
  i.ker.normalConeToQuotientSpec ≫ inv i.toQuotientSpec

/-- The normal cone lies over `X` through `i`. -/
@[reassoc (attr := simp)]
lemma normalBundleProj_comp :
    i.normalBundleProj ≫ i =
      (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase := by
  have : inv i.toQuotientSpec ≫ i =
      (relativeGluingData i.ker.coequifibered_toQuotientAlgebra).toBase := by
    rw [IsIso.inv_comp_eq, toQuotientSpec_toBase]
  rw [normalBundleProj, Category.assoc, this, IdealSheafData.normalConeToQuotientSpec_toBase]

/-- Blueprint `prose-09-11`: Normal bundle and zero section

The zero section `z : Z ⟶ N_{Z/X}` (`AlgebraicGeometry.Scheme.Hom.normalConeZeroSection`, given by
the augmentation `⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_X / I`) is a section of the projection of the normal
cone. -/
@[reassoc (attr := simp)]
lemma normalConeZeroSection_normalBundleProj :
    i.normalConeZeroSection ≫ i.normalBundleProj = 𝟙 Z := by
  rw [normalConeZeroSection, normalBundleProj, IdealSheafData.normalConeToQuotientSpec,
    Category.assoc, ← Category.assoc (relativeGluingMap _ _ _), ← relativeGluingMap_comp,
    IdealSheafData.quotientToNormalCone_comp_normalConeToQuotient, relativeGluingMap_id,
    Category.id_comp, IsIso.hom_inv_id]

end Scheme.Hom

end AlgebraicGeometry
