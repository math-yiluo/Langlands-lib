/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import WeilConjectures.Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra

/-!
# The deformation space of a closed subscheme

For a quasi-coherent ideal `I` of a scheme `X`, the *deformation space* is the relative spectrum

`D_I X = Spec_X (⨁_{n ∈ ℤ} I^{-n} tⁿ)`

of the extended Rees algebra `𝒪_X[t, I t⁻¹]` (with `I^m = 𝒪_X` for `m ≤ 0`). It lies over the
relative affine line `Spec_X 𝒪_X[t]`. Inverting `t` gives `𝒪_X[t, t⁻¹]`, so over the punctured
line the deformation space is trivial, and setting `t = 0` gives the *normal cone*

`N_I X = Spec_X (𝒪_X[t, I t⁻¹] / t) = Spec_X (⨁_{r ≥ 0} I^r / I^{r+1})`.

This is the deformation to the normal cone `Bl_{V(I) × 0} (X × 𝔸¹) ∖ (strict transform of X × 0)`
of `V(I) ⊆ X`, in its Rees-algebra form.

All the schemes here are relative spectra of quasi-coherent `𝒪_X`-algebras, given on the affine
opens of `X` (`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`), and the relations
between them come from pushout squares of algebras through
`AlgebraicGeometry.Scheme.AffineZariskiSite.isPullback_relativeGluingMap`.

## Main definitions

- `AlgebraicGeometry.Scheme.polynomialSpec`: the relative affine line `Spec_X 𝒪_X[t]`.
- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`: the deformation space `D_I X`,
  with its morphism `deformationSpaceToPolynomialSpec` to the relative affine line.
- `AlgebraicGeometry.Scheme.IdealSheafData.normalCone`: the normal cone `N_I X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial LaurentPolynomial

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite

variable (X : Scheme.{u})

/-- The structure sheaf of `X` on its affine opens. -/
abbrev affineStructurePresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (toOpensFunctor X).op ⋙ X.presheaf

/-! ### Quotients of quasi-coherent algebras -/

section Quotient

variable {X} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : X.affineStructurePresheaf ⟶ F} (H : α.Coequifibered)
  (𝔞 : ∀ U, Ideal (F.obj U))
  (h𝔞 : ∀ ⦃U V⦄ (i : U ⟶ V), (𝔞 U).map (F.map i).hom = 𝔞 V)

include h𝔞 in
lemma le_comap_quotientPresheaf ⦃U V⦄ (i : U ⟶ V) : 𝔞 U ≤ (𝔞 V).comap (F.map i).hom := by
  rw [← Ideal.map_le_iff_le_comap, h𝔞]

/-- The quotient of a presheaf of rings `F` by a compatible family of ideals `𝔞`. -/
@[simps]
noncomputable def quotientPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (F.obj U ⧸ 𝔞 U)
  map {U V} i := CommRingCat.ofHom
    (Ideal.quotientMap (𝔞 V) (F.map i).hom (le_comap_quotientPresheaf 𝔞 h𝔞 i))
  map_id U := by
    ext x
    simp
  map_comp i j := by
    ext x
    simp

/-- The quotient map `F ⟶ F / 𝔞`. -/
@[simps]
noncomputable def toQuotientPresheaf : F ⟶ quotientPresheaf 𝔞 h𝔞 where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (𝔞 U))
  naturality U V i := by
    ext x
    exact (Ideal.quotientMap_mk (f := (F.map i).hom) (H := le_comap_quotientPresheaf 𝔞 h𝔞 i)
      (x := x)).symm

include h𝔞 in
lemma coequifibered_toQuotientPresheaf : (toQuotientPresheaf 𝔞 h𝔞).Coequifibered := by
  intro U V i
  have e : 𝔞 V = (𝔞 U).map (F.map i).hom := (h𝔞 i).symm
  refine (CommRingCat.isPushout_quotient (F.map i) (𝔞 U)).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Ideal.quotEquivOfEq e.symm).toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext x; rfl
  · ext x
    rfl

include H in
lemma coequifibered_comp_toQuotientPresheaf : (α ≫ toQuotientPresheaf 𝔞 h𝔞).Coequifibered :=
  NatTrans.Coequifibered.comp H (coequifibered_toQuotientPresheaf 𝔞 h𝔞)

end Quotient

/-! ### The relative affine line -/

/-- The quasi-coherent algebra `𝒪_X[t]`. -/
noncomputable abbrev polynomialPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  X.affineStructurePresheaf ⋙ CommRingCat.polynomialFunctor

/-- The structure map `𝒪_X ⟶ 𝒪_X[t]`. -/
noncomputable abbrev toPolynomialPresheaf : X.affineStructurePresheaf ⟶ X.polynomialPresheaf :=
  X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialC

lemma coequifibered_toPolynomialPresheaf : X.toPolynomialPresheaf.Coequifibered :=
  CommRingCat.coequifibered_polynomialC.whiskerLeft _

/-- The quasi-coherent algebra `𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev laurentPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  X.affineStructurePresheaf ⋙ CommRingCat.laurentFunctor

/-- The structure map `𝒪_X ⟶ 𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev toLaurentPresheaf : X.affineStructurePresheaf ⟶ X.laurentPresheaf :=
  X.affineStructurePresheaf.whiskerLeft CommRingCat.laurentC

lemma coequifibered_toLaurentPresheaf : X.toLaurentPresheaf.Coequifibered :=
  CommRingCat.coequifibered_laurentC.whiskerLeft _

/-- The relative affine line `𝔸¹_X = Spec_X 𝒪_X[t]`. -/
noncomputable abbrev polynomialSpec : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toPolynomialPresheaf).glued

/-- The projection `𝔸¹_X ⟶ X`. -/
noncomputable abbrev polynomialSpecProj : X.polynomialSpec ⟶ X :=
  (relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase

/-- The punctured relative affine line `𝔾_{m,X} = Spec_X 𝒪_X[t, t⁻¹]`. -/
noncomputable abbrev laurentSpec : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toLaurentPresheaf).glued

/-- The inclusion `𝔾_{m,X} ⟶ 𝔸¹_X`. -/
noncomputable def laurentSpecToPolynomialSpec : X.laurentSpec ⟶ X.polynomialSpec :=
  relativeGluingMap _ _ (X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent)

/-- The zero section of `𝔸¹_X` as a quasi-coherent algebra: `𝒪_X[t] / t`. -/
noncomputable abbrev polynomialZeroPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf (F := X.polynomialPresheaf) (fun _ ↦ Ideal.span {Polynomial.X}) fun U V i ↦ by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span {p}) (Polynomial.map_X _)

/-- The quotient map `𝒪_X[t] ⟶ 𝒪_X[t] / t`. -/
noncomputable abbrev polynomialToPolynomialZero : X.polynomialPresheaf ⟶ X.polynomialZeroPresheaf :=
  toQuotientPresheaf _ _

/-- The structure map `𝒪_X ⟶ 𝒪_X[t] / t`. -/
noncomputable abbrev toPolynomialZeroPresheaf :
    X.affineStructurePresheaf ⟶ X.polynomialZeroPresheaf :=
  X.toPolynomialPresheaf ≫ X.polynomialToPolynomialZero

lemma coequifibered_toPolynomialZeroPresheaf : X.toPolynomialZeroPresheaf.Coequifibered :=
  coequifibered_comp_toQuotientPresheaf X.coequifibered_toPolynomialPresheaf _ _

/-! ### The deformation space and the normal cone -/

namespace IdealSheafData

variable {X} (I : X.IdealSheafData)

/-- The ideal `I(U)` over an affine open `U`, indexed by the small affine Zariski site. -/
abbrev siteIdeal (U : X.AffineZariskiSite) : Ideal Γ(X, U.1) :=
  I.ideal ⟨U.1, U.2⟩

lemma map_siteIdeal ⦃U V : X.AffineZariskiSiteᵒᵖ⦄ (i : U ⟶ V) :
    (I.siteIdeal U.unop).map (X.affineStructurePresheaf.map i).hom = I.siteIdeal V.unop :=
  I.map_ideal' (U := ⟨V.unop.1, V.unop.2⟩) (V := ⟨U.unop.1, U.unop.2⟩) _

/-- The extended Rees algebra `𝒪_X[t, I t⁻¹]` as a quasi-coherent algebra. -/
@[simps]
noncomputable def reesPresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (I.siteIdeal U.unop).extendedReesAlgebra
  map {U V} i := CommRingCat.ofHom <| (I.siteIdeal U.unop).extendedReesAlgebraMap
    (X.affineStructurePresheaf.map i).hom _ (I.map_siteIdeal i).le
  map_id U := CommRingCat.hom_ext <| RingHom.ext fun x ↦ Subtype.ext <| by
    change LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map (𝟙 U)).hom x.1 = x.1
    rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id]
    exact LaurentPolynomial.mapRingHom_id _
  map_comp i j := CommRingCat.hom_ext <| RingHom.ext fun x ↦ Subtype.ext <| by
    change LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map (i ≫ j)).hom x.1 =
      LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map j).hom
        (LaurentPolynomial.mapRingHom (X.affineStructurePresheaf.map i).hom x.1)
    rw [CategoryTheory.Functor.map_comp, CommRingCat.hom_comp]
    exact (LaurentPolynomial.mapRingHom_mapRingHom _ _ _).symm

/-- The structure map `𝒪_X ⟶ 𝒪_X[t, I t⁻¹]`. -/
@[simps]
noncomputable def toReesPresheaf : X.affineStructurePresheaf ⟶ I.reesPresheaf where
  app U := by
    change CommRingCat.of Γ(X, U.unop.1) ⟶ .of (I.siteIdeal U.unop).extendedReesAlgebra
    exact CommRingCat.ofHom (algebraMap _ _)
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun x ↦
    (Ideal.extendedReesAlgebraMap_algebraMap _ _ (I.map_siteIdeal i).le x).symm)

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered_toReesPresheaf : I.toReesPresheaf.Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  have := U.2.isLocalization_basicOpen f
  exact Ideal.isLocalization_away_extendedReesAlgebraMap _ f this _
    (I.map_ideal_basicOpen ⟨U.1, U.2⟩ f)

/-- The deformation space `D_I X = Spec_X 𝒪_X[t, I t⁻¹]`. -/
noncomputable abbrev deformationSpace : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toReesPresheaf).glued

/-- The structure morphism `D_I X ⟶ X`. -/
noncomputable abbrev deformationSpaceProj : I.deformationSpace ⟶ X :=
  (relativeGluingData I.coequifibered_toReesPresheaf).toBase

/-- The inclusion `𝒪_X[t] ⟶ 𝒪_X[t, I t⁻¹]`. -/
@[simps]
noncomputable def polynomialToRees : X.polynomialPresheaf ⟶ I.reesPresheaf where
  app U := CommRingCat.ofHom (I.siteIdeal U.unop).toExtendedReesAlgebra
  naturality U V i := by
    refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    exact congr($(Ideal.extendedReesAlgebraMap_comp_toExtendedReesAlgebra _ _
      (I.map_siteIdeal i).le) p).symm

lemma toPolynomialPresheaf_comp_polynomialToRees :
    X.toPolynomialPresheaf ≫ I.polynomialToRees = I.toReesPresheaf := by
  ext U x
  exact Ideal.toExtendedReesAlgebra_C x

/-- The morphism `g̃ : D_I X ⟶ 𝔸¹_X` given by the coordinate `t`. -/
noncomputable def deformationSpaceToPolynomialSpec : I.deformationSpace ⟶ X.polynomialSpec :=
  relativeGluingMap _ _ I.polynomialToRees

/-- The deformation space `D_⊥ X` of the zero ideal is the relative affine line `𝔸¹_X`. -/
instance isIso_deformationSpaceToPolynomialSpec_bot :
    IsIso (⊥ : X.IdealSheafData).deformationSpaceToPolynomialSpec :=
  relativeGluingMap_of_forall _ (MorphismProperty.isomorphisms _) _ _
    (⊥ : X.IdealSheafData).toPolynomialPresheaf_comp_polynomialToRees fun U ↦ by
      have : IsIso ((⊥ : X.IdealSheafData).polynomialToRees.app (Opposite.op U)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          (Ideal.bijective_toExtendedReesAlgebra_of_eq_bot rfl)
      exact (inferInstance : IsIso (Spec.map
        ((⊥ : X.IdealSheafData).polynomialToRees.app (Opposite.op U))))

/-- The inclusion `𝒪_X[t, I t⁻¹] ⟶ 𝒪_X[t, t⁻¹]`. -/
@[simps]
noncomputable def reesToLaurent : I.reesPresheaf ⟶ X.laurentPresheaf where
  app U := CommRingCat.ofHom (I.siteIdeal U.unop).extendedReesAlgebra.val.toRingHom
  naturality U V i := by ext x; rfl

lemma polynomialToRees_comp_reesToLaurent :
    I.polynomialToRees ≫ I.reesToLaurent =
      X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent := by
  ext U p
  rfl

/-- The trivialisation of the deformation space over the punctured line:
`𝔾_{m,X} ⟶ D_I X`. -/
noncomputable def laurentSpecToDeformationSpace : X.laurentSpec ⟶ I.deformationSpace :=
  relativeGluingMap _ _ I.reesToLaurent

/-- The ideal `(t)` of the extended Rees algebra. -/
noncomputable abbrev tIdeal (U : X.AffineZariskiSiteᵒᵖ) : Ideal (I.reesPresheaf.obj U) :=
  Ideal.span {(I.siteIdeal U.unop).extendedReesAlgebraT}

lemma map_tIdeal ⦃U V : X.AffineZariskiSiteᵒᵖ⦄ (i : U ⟶ V) :
    (I.tIdeal U).map (I.reesPresheaf.map i).hom = I.tIdeal V := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun t ↦ Ideal.span {t})
    (Ideal.extendedReesAlgebraMap_T _ _ (I.map_siteIdeal i).le)

/-- The associated graded algebra `𝒪_X[t, I t⁻¹] / t = ⨁_{r ≥ 0} I^r / I^{r+1}`. -/
noncomputable abbrev normalConePresheaf : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf I.tIdeal I.map_tIdeal

lemma coequifibered_toNormalConePresheaf :
    (I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal).Coequifibered :=
  coequifibered_comp_toQuotientPresheaf I.coequifibered_toReesPresheaf _ _

/-- The normal cone `N_I X = Spec_X (⨁_{r ≥ 0} I^r / I^{r+1})`, the fibre of the deformation space
over the zero section `t = 0`. -/
noncomputable abbrev normalCone : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toNormalConePresheaf).glued

/-- The inclusion `N_I X ⟶ D_I X` of the normal cone as the fibre over `t = 0`. -/
noncomputable def normalConeToDeformationSpace : I.normalCone ⟶ I.deformationSpace :=
  relativeGluingMap _ _ (toQuotientPresheaf I.tIdeal I.map_tIdeal)

/-- The map `𝒪_X[t] / t ⟶ 𝒪_X[t, I t⁻¹] / t`. -/
@[simps]
noncomputable def polynomialZeroToNormalCone :
    X.polynomialZeroPresheaf ⟶ I.normalConePresheaf where
  app U := CommRingCat.ofHom (Ideal.quotientMap _ (I.polynomialToRees.app U).hom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_span]
    rw [Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr Ideal.toExtendedReesAlgebra_X)))
  naturality U V i := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change Ideal.Quotient.mk _
        ((I.polynomialToRees.app V).hom ((X.polynomialPresheaf.map i).hom x)) =
      Ideal.Quotient.mk _ ((I.reesPresheaf.map i).hom ((I.polynomialToRees.app U).hom x))
    exact congrArg _ (I.polynomialToRees.naturality_apply i x)

/-! ### The closed subscheme and its relative affine line -/

/-- The quasi-coherent algebra `𝒪_X / I`. -/
noncomputable abbrev quotientAlgebra : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  quotientPresheaf (F := X.affineStructurePresheaf) (fun U ↦ I.siteIdeal U.unop) I.map_siteIdeal

/-- The quotient map `𝒪_X ⟶ 𝒪_X / I`. -/
noncomputable abbrev toQuotientAlgebra : X.affineStructurePresheaf ⟶ I.quotientAlgebra :=
  toQuotientPresheaf _ I.map_siteIdeal

lemma coequifibered_toQuotientAlgebra : I.toQuotientAlgebra.Coequifibered :=
  coequifibered_toQuotientPresheaf _ _

/-- The closed subscheme `V(I) = Spec_X (𝒪_X / I)`, as a relative spectrum. -/
noncomputable abbrev quotientSpec : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toQuotientAlgebra).glued

/-- The quasi-coherent algebra `(𝒪_X / I)[t]`. -/
noncomputable abbrev quotientPolynomialAlgebra : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  I.quotientAlgebra ⋙ CommRingCat.polynomialFunctor

/-- The structure map `𝒪_X ⟶ (𝒪_X / I)[t]`. -/
noncomputable abbrev toQuotientPolynomialAlgebra :
    X.affineStructurePresheaf ⟶ I.quotientPolynomialAlgebra :=
  I.toQuotientAlgebra ≫ I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC

lemma coequifibered_toQuotientPolynomialAlgebra : I.toQuotientPolynomialAlgebra.Coequifibered :=
  NatTrans.Coequifibered.comp I.coequifibered_toQuotientAlgebra
    (CommRingCat.coequifibered_polynomialC.whiskerLeft _)

/-- The relative affine line `𝔸¹_{V(I)} = Spec_X (𝒪_X / I)[t]`. -/
noncomputable abbrev quotientPolynomialSpec : Scheme.{u} :=
  (relativeGluingData I.coequifibered_toQuotientPolynomialAlgebra).glued

/-- The map `𝒪_X[t, I t⁻¹] ⟶ (𝒪_X / I)[t]`, `t ↦ t`, `x t⁻¹ ↦ 0` for `x ∈ I`. -/
@[simps]
noncomputable def reesToQuotientPolynomial : I.reesPresheaf ⟶ I.quotientPolynomialAlgebra where
  app U := CommRingCat.ofHom ((I.siteIdeal U.unop).extendedReesAlgebraToPolynomial
    (Ideal.Quotient.mk _) Ideal.mk_ker.ge)
  naturality U V i := by
    refine CommRingCat.hom_ext ?_
    exact Ideal.extendedReesAlgebraToPolynomial_comp_extendedReesAlgebraMap _ _
      (I.map_siteIdeal i).le _ Ideal.mk_ker.ge _ Ideal.mk_ker.ge _
      (Ideal.quotientMap_comp_mk (le_comap_quotientPresheaf _ I.map_siteIdeal i))

/-- `t ↦ 0`: the restriction of `(𝒪_X / I)[t]` to the zero section. -/
@[simps]
noncomputable def quotientPolynomialEvalZero : I.quotientPolynomialAlgebra ⟶ I.quotientAlgebra where
  app U := CommRingCat.ofHom (Polynomial.evalRingHom 0)
  naturality U V i := by
    refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    exact Polynomial.eval_zero_map _ p

lemma toExtendedReesAlgebraT_mem_tIdeal (U : X.AffineZariskiSiteᵒᵖ) :
    (I.siteIdeal U.unop).extendedReesAlgebraT ∈ I.tIdeal U :=
  Ideal.subset_span rfl

/-- The projection `⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_X / I` to the degree-zero part. -/
noncomputable def normalConeToQuotient : I.normalConePresheaf ⟶ I.quotientAlgebra where
  app U := CommRingCat.ofHom (Ideal.Quotient.lift _
    ((Polynomial.evalRingHom 0).comp (I.reesToQuotientPolynomial.app U).hom)
    fun _ ha ↦ Ideal.span_T_le_ker_extendedReesAlgebraToPolynomial (Ideal.Quotient.mk _)
      Ideal.mk_ker.ge ha)
  naturality U V i := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change Polynomial.eval 0
        ((I.reesToQuotientPolynomial.app V).hom ((I.reesPresheaf.map i).hom x)) =
      (I.quotientAlgebra.map i).hom (Polynomial.eval 0 ((I.reesToQuotientPolynomial.app U).hom x))
    exact (congrArg (Polynomial.eval 0) (I.reesToQuotientPolynomial.naturality_apply i x)).trans
      (Polynomial.eval_zero_map _ _)

lemma toNormalConePresheaf_comp_normalConeToQuotient :
    (I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal) ≫ I.normalConeToQuotient =
      I.toQuotientAlgebra := by
  ext U x
  change Polynomial.eval 0 (Ideal.extendedReesAlgebraToPolynomial _ (Ideal.Quotient.mk _)
    Ideal.mk_ker.ge (algebraMap Γ(X, U.unop.1) (I.siteIdeal U.unop).extendedReesAlgebra x)) = _
  exact (congrArg (Polynomial.eval 0) (Ideal.extendedReesAlgebraToPolynomial_algebraMap
    (I := I.siteIdeal U.unop) _ Ideal.mk_ker.ge x)).trans Polynomial.eval_C

lemma polynomialToRees_comp_reesToQuotientPolynomial :
    I.polynomialToRees ≫ I.reesToQuotientPolynomial =
      Functor.whiskerRight I.toQuotientAlgebra CommRingCat.polynomialFunctor := by
  refine NatTrans.ext (funext fun U ↦ ?_)
  refine CommRingCat.hom_ext ?_
  exact Ideal.extendedReesAlgebraToPolynomial_comp_toExtendedReesAlgebra
    (I := I.siteIdeal U.unop) (Ideal.Quotient.mk _) Ideal.mk_ker.ge

/-! ### The fibres of the deformation space -/

lemma toPolynomialPresheaf_comp_polynomialToLaurent :
    X.toPolynomialPresheaf ≫ X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent =
      X.toLaurentPresheaf := by
  ext U x
  exact Polynomial.toLaurent_C x

lemma toReesPresheaf_comp_reesToLaurent :
    I.toReesPresheaf ≫ I.reesToLaurent = X.toLaurentPresheaf := by
  ext U x
  exact Ideal.coe_algebraMap_extendedReesAlgebra (I := I.siteIdeal U.unop) x

/-- **The punctured trivialisation.** Over the punctured line `𝔾_{m,X} ⊆ 𝔸¹_X` the deformation
space is trivial: `D_I X ×_{𝔸¹_X} 𝔾_{m,X} = 𝔾_{m,X}`, since inverting `t` in `𝒪_X[t, I t⁻¹]` gives
`𝒪_X[t, t⁻¹]`. -/
theorem isPullback_laurentSpecToDeformationSpace :
    IsPullback I.laurentSpecToDeformationSpace (𝟙 X.laurentSpec) I.deformationSpaceToPolynomialSpec
      X.laurentSpecToPolynomialSpec := by
  have := isPullback_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toReesPresheaf X.coequifibered_toLaurentPresheaf
    X.coequifibered_toLaurentPresheaf I.polynomialToRees
    (X.affineStructurePresheaf.whiskerLeft CommRingCat.polynomialToLaurent) I.reesToLaurent (𝟙 _)
    toPolynomialPresheaf_comp_polynomialToLaurent I.toReesPresheaf_comp_reesToLaurent
    fun U ↦ Ideal.isPushout_toExtendedReesAlgebra (I.siteIdeal U)
  rwa [relativeGluingMap_id] at this

lemma isPushout_polynomialToRees_toQuotientPresheaf (U : X.AffineZariskiSiteᵒᵖ) :
    IsPushout (I.polynomialToRees.app U)
      ((toQuotientPresheaf (F := X.polynomialPresheaf) (fun _ ↦ Ideal.span {Polynomial.X})
        fun U V i ↦ by
          rw [Ideal.map_span, Set.image_singleton]
          exact congrArg (fun p ↦ Ideal.span {p}) (Polynomial.map_X _)).app U)
      ((toQuotientPresheaf I.tIdeal I.map_tIdeal).app U) (I.polynomialZeroToNormalCone.app U) := by
  have e : (Ideal.span {Polynomial.X}).map (I.polynomialToRees.app U).hom = I.tIdeal U := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun t ↦ Ideal.span {t}) Ideal.toExtendedReesAlgebra_X
  refine (CommRingCat.isPushout_quotient (I.polynomialToRees.app U)
    (Ideal.span {Polynomial.X})).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Ideal.quotEquivOfEq e).toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext x; rfl
  · ext x; rfl

/-- The zero section `t = 0` of `𝔸¹_X`, as the relative spectrum of `𝒪_X[t] / t`. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.polynomialZeroSpec : Scheme.{u} :=
  (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).glued

/-- The inclusion of the zero section `Spec_X (𝒪_X[t] / t) ⟶ 𝔸¹_X`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.polynomialZeroSpecToPolynomialSpec :
    X.polynomialZeroSpec ⟶ X.polynomialSpec :=
  relativeGluingMap _ _ (toQuotientPresheaf _ _)

/-- The projection of the normal cone to the zero section of `𝔸¹_X`. -/
noncomputable def normalConeToPolynomialZeroSpec : I.normalCone ⟶ X.polynomialZeroSpec :=
  relativeGluingMap _ _ I.polynomialZeroToNormalCone

/-- **The fibre over `t = 0`.** The normal cone is the fibre of the deformation space over the
zero section of `𝔸¹_X`: `𝒪_X[t, I t⁻¹] ⊗_{𝒪_X[t]} 𝒪_X[t]/t = 𝒪_X[t, I t⁻¹] / t`. -/
theorem isPullback_normalConeToDeformationSpace :
    IsPullback I.normalConeToDeformationSpace I.normalConeToPolynomialZeroSpec
      I.deformationSpaceToPolynomialSpec X.polynomialZeroSpecToPolynomialSpec :=
  isPullback_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toReesPresheaf X.coequifibered_toPolynomialZeroPresheaf
    I.coequifibered_toNormalConePresheaf I.polynomialToRees _ _ I.polynomialZeroToNormalCone
    rfl rfl fun U ↦ I.isPushout_polynomialToRees_toQuotientPresheaf (.op U)

/-- `V(I) = Spec_X (𝒪_X / I) ⟶ X` is a closed immersion. -/
instance : IsClosedImmersion (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase :=
  toBase_of_forall _ @IsClosedImmersion fun _ ↦
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The kernel of `V(I) ⟶ X` is `I`. -/
lemma ker_quotientSpec_toBase :
    (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase.ker = I := by
  ext U x
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.app_eq_appLE]
  have h := toBase_appLE_sectionsIso_hom I.coequifibered_toQuotientAlgebra ⟨U.1, U.2⟩
  have hx : ((relativeGluingData I.coequifibered_toQuotientAlgebra).toBase.appLE U.1 _ le_rfl ≫
      (sectionsIso I.coequifibered_toQuotientAlgebra ⟨U.1, U.2⟩).hom).hom x =
      Ideal.Quotient.mk (I.ideal U) x := congr($h x)
  rw [CommRingCat.comp_apply] at hx
  rw [← (sectionsIso I.coequifibered_toQuotientAlgebra ⟨U.1, U.2⟩).commRingCatIsoToRingEquiv
    |>.map_eq_zero_iff]
  change _ = _ ↔ _
  erw [hx]
  exact Ideal.Quotient.eq_zero_iff_mem

end IdealSheafData

/-! ### The relative affine line is the affine line -/

/-- `Spec R[t] ≅ 𝔸¹_{Spec R}`: the morphism `Spec R[t] ⟶ 𝔸¹_{Spec R}` given by the coordinate `t`
is an isomorphism. -/
lemma isIso_homOfVector_specPolynomial (R : Type u) [CommRing R] :
    IsIso (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (C : R →+* R[X])))
      fun _ : ULift.{u} (Fin 1) ↦ (ΓSpecIso (.of R[X])).inv Polynomial.X) := by
  let e := (MvPolynomial.uniqueAlgEquiv R (ULift.{u} (Fin 1))).toRingEquiv.toCommRingCatIso
  have : AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (C : R →+* R[X])))
      (fun _ : ULift.{u} (Fin 1) ↦ (ΓSpecIso (.of R[X])).inv Polynomial.X) =
      Spec.map e.hom ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).inv := by
    refine AffineSpace.hom_ext ?_ fun i ↦ ?_
    · simp only [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.SpecIso_inv_over]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp [e]
    · rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.SpecIso_inv_appTop_coord]
      have := congr($(Scheme.ΓSpecIso_inv_naturality e.hom) (MvPolynomial.X i))
      refine Eq.trans ?_ (this.trans rfl)
      change _ = (ΓSpecIso (.of R[X])).inv (e.hom (MvPolynomial.X i))
      congr 1
      simp [e]
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The chart `Spec Γ(X, U)[t] ⟶ 𝔸¹_X` of the affine line over an affine open `U`, given by
the coordinate `t`. -/
noncomputable def polynomialSpecChart (U : X.AffineZariskiSite) :
    (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor.obj U ⟶
      𝔸(ULift.{u} (Fin 1); X) :=
  AffineSpace.homOfVector
    ((relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U ≫ U.1.ι)
    fun _ ↦ (ΓSpecIso (X.polynomialPresheaf.obj (.op U))).inv Polynomial.X

set_option backward.isDefEq.respectTransparency false in
lemma natTrans_app_comp_ι (U : X.AffineZariskiSite) :
    (relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U ≫ U.1.ι =
      Spec.map (X.toPolynomialPresheaf.app (.op U)) ≫ U.2.fromSpec := by
  simp [relativeGluingData, IsAffineOpen.isoSpec_inv_ι]

set_option backward.isDefEq.respectTransparency false in
lemma map_comp_polynomialSpecChart {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor.map i ≫
      X.polynomialSpecChart V = X.polynomialSpecChart U := by
  rw [polynomialSpecChart, polynomialSpecChart, AffineSpace.comp_homOfVector]
  congr 1
  · rw [natTrans_app_comp_ι, natTrans_app_comp_ι]
    change Spec.map (X.polynomialPresheaf.map i.op) ≫
      Spec.map (X.toPolynomialPresheaf.app (.op V)) ≫
      V.2.fromSpec = _
    rw [← Spec.map_comp_assoc, ← X.toPolynomialPresheaf.naturality, Spec.map_comp_assoc]
    exact congrArg (Spec.map (X.toPolynomialPresheaf.app (.op U)) ≫ ·)
      (V.2.map_fromSpec U.2 ((toOpensFunctor X).map i).op)
  · ext
    change (Spec.map (X.polynomialPresheaf.map i.op)).appTop _ = _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    exact Polynomial.map_X _

/-- The identification `Spec_X 𝒪_X[t] ⟶ 𝔸¹_X`, glued from the charts
`AlgebraicGeometry.Scheme.polynomialSpecChart`. -/
noncomputable def polynomialSpecToAffineSpace : X.polynomialSpec ⟶ 𝔸(ULift.{u} (Fin 1); X) :=
  colimit.desc _
    { pt := _
      ι := { app U := X.polynomialSpecChart U
             naturality U V i := by
              refine (X.map_comp_polynomialSpecChart i).trans ?_
              exact (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma ι_polynomialSpecToAffineSpace (U : X.AffineZariskiSite) :
    colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U ≫
      X.polynomialSpecToAffineSpace = X.polynomialSpecChart U :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma polynomialSpecToAffineSpace_over :
    X.polynomialSpecToAffineSpace ≫ 𝔸(ULift.{u} (Fin 1); X) ↘ X = X.polynomialSpecProj := by
  refine colimit.hom_ext fun U ↦ ?_
  rw [ι_polynomialSpecToAffineSpace_assoc, polynomialSpecChart, AffineSpace.homOfVector_over,
    natTrans_app_comp_ι, ι_toBase]

set_option backward.isDefEq.respectTransparency false in
instance (U : X.AffineZariskiSite) :
    IsIso (AffineSpace.homOfVector
      ((relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U)
      fun _ : ULift.{u} (Fin 1) ↦
        (ΓSpecIso (X.polynomialPresheaf.obj (.op U))).inv Polynomial.X) := by
  have : (relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U =
      Spec.map (CommRingCat.ofHom (C : Γ(X, U.1) →+* Γ(X, U.1)[X])) ≫ U.2.isoSpec.inv := rfl
  rw [this, ← AffineSpace.homOfVector_map]
  have : IsIso (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* _)))
      fun _ : ULift.{u} (Fin 1) ↦
        (ΓSpecIso (X.polynomialPresheaf.obj (.op U))).inv Polynomial.X) :=
    isIso_homOfVector_specPolynomial Γ(X, U.1)
  infer_instance

/-- The chart `Spec Γ(X, U)[t]` of `Spec_X 𝒪_X[t]` maps to the affine line over `U`. -/
noncomputable def polynomialSpecChartLift (U : X.AffineZariskiSite) :
    (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor.obj U ⟶
      pullback (𝔸(ULift.{u} (Fin 1); X) ↘ X) U.1.ι :=
  pullback.lift (X.polynomialSpecChart U)
    ((relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U)
    (by rw [polynomialSpecChart, AffineSpace.homOfVector_over])

instance (U : X.AffineZariskiSite) : IsIso (X.polynomialSpecChartLift U) := by
  have : X.polynomialSpecChartLift U = AffineSpace.homOfVector
      ((relativeGluingData X.coequifibered_toPolynomialPresheaf).natTrans.app U)
      (fun _ : ULift.{u} (Fin 1) ↦ (ΓSpecIso (X.polynomialPresheaf.obj (.op U))).inv Polynomial.X) ≫
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) U.1.ι).isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [polynomialSpecChartLift, pullback.lift_fst, Category.assoc,
        IsPullback.isoPullback_hom_fst, AffineSpace.homOfVector_map, polynomialSpecChart]
    · rw [polynomialSpecChartLift, pullback.lift_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, AffineSpace.homOfVector_over]
  rw [this]
  infer_instance

lemma isPullback_ι_polynomialSpecToAffineSpace (U : X.AffineZariskiSite) :
    IsPullback (colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U)
      (X.polynomialSpecChartLift U) X.polynomialSpecToAffineSpace
      (pullback.fst (𝔸(ULift.{u} (Fin 1); X) ↘ X) U.1.ι) := by
  refine IsPullback.of_bot ?_ (by rw [polynomialSpecChartLift, pullback.lift_fst,
    ι_polynomialSpecToAffineSpace])
    (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin 1); X) ↘ X) U.1.ι)
  rw [polynomialSpecChartLift, pullback.lift_snd, polynomialSpecToAffineSpace_over]
  exact ((relativeGluingData X.coequifibered_toPolynomialPresheaf).isPullback_natTrans_ι_toBase
    U).flip

/-- **`Spec_X 𝒪_X[t]` is the affine line over `X`.** -/
instance : IsIso X.polynomialSpecToAffineSpace := by
  refine IsZariskiLocalAtTarget.of_openCover (P := .isomorphisms _)
    ((directedCover X).pullback₁ (𝔸(ULift.{u} (Fin 1); X) ↘ X)) fun U ↦ ?_
  have h := X.isPullback_ι_polynomialSpecToAffineSpace U
  have : Cover.pullbackHom ((directedCover X).pullback₁ (𝔸(ULift.{u} (Fin 1); X) ↘ X))
      X.polynomialSpecToAffineSpace U = h.isoPullback.inv ≫ X.polynomialSpecChartLift U := by
    simp only [Cover.pullbackHom, IsPullback.isoPullback_inv_snd]
    rfl
  rw [MorphismProperty.isomorphisms.iff, this]
  infer_instance

/-! ### The zero section -/

set_option backward.isDefEq.respectTransparency false in
instance : IsIso (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).toBase := by
  refine toBase_of_forall _ (.isomorphisms _) fun U ↦ ?_
  have : IsIso (X.toPolynomialZeroPresheaf.app (.op U)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have h : Ideal.span {Polynomial.X - Polynomial.C (0 : Γ(X, U.1))} =
        Ideal.span {(Polynomial.X : Γ(X, U.1)[X])} := by simp
    let e := (Polynomial.quotientSpanXSubCAlgEquiv (0 : Γ(X, U.1))).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq h)
    exact ⟨fun a b hab ↦ e.injective hab, fun y ↦ ⟨e.symm y, e.apply_symm_apply y⟩⟩
  exact (MorphismProperty.isomorphisms.iff _).mpr inferInstance

/-- The zero section `X ⟶ Spec_X 𝒪_X[t]`. -/
noncomputable def polynomialSpecZeroSection : X ⟶ X.polynomialSpec :=
  inv (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).toBase ≫
    X.polynomialZeroSpecToPolynomialSpec

lemma polynomialZeroSpecToPolynomialSpec_comp_polynomialSpecToAffineSpace :
    X.polynomialZeroSpecToPolynomialSpec ≫ X.polynomialSpecToAffineSpace =
      (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).toBase ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) X := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp only [Category.assoc, polynomialSpecToAffineSpace_over, AffineSpace.zeroSection_over,
      Category.comp_id, polynomialZeroSpecToPolynomialSpec]
    rw [relativeGluingMap_toBase _ _ _ rfl]
  · rw [polynomialZeroSpecToPolynomialSpec, ι_relativeGluingMap_assoc,
      ι_polynomialSpecToAffineSpace, polynomialSpecChart, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_appTop_coord, Function.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.zeroSection_appTop_coord, map_zero, map_zero]
    have := congr($(Scheme.ΓSpecIso_inv_naturality (X.polynomialToPolynomialZero.app (.op U)))
      Polynomial.X)
    refine this.symm.trans ?_
    change (ΓSpecIso (X.polynomialZeroPresheaf.obj (.op U))).inv
      (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Γ(X, U.1)[X])}) Polynomial.X) = 0
    have h0 : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Γ(X, U.1)[X])}) Polynomial.X = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [h0, map_zero]

lemma polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace :
    X.polynomialSpecZeroSection ≫ X.polynomialSpecToAffineSpace =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) X := by
  rw [polynomialSpecZeroSection, Category.assoc,
    polynomialZeroSpecToPolynomialSpec_comp_polynomialSpecToAffineSpace, IsIso.inv_hom_id_assoc]

/-! ### The punctured line -/

/-- The coordinate `t` on `Spec_X 𝒪_X[t]`. -/
noncomputable def polynomialSpecCoord : Γ(X.polynomialSpec, ⊤) :=
  X.polynomialSpecToAffineSpace.appTop (AffineSpace.coord X 0)

lemma ι_appTop_polynomialSpecCoord (U : X.AffineZariskiSite) :
    (colimit.ι (relativeGluingData X.coequifibered_toPolynomialPresheaf).functor U).appTop
      X.polynomialSpecCoord = (ΓSpecIso (X.polynomialPresheaf.obj (.op U))).inv Polynomial.X := by
  rw [polynomialSpecCoord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ι_polynomialSpecToAffineSpace, polynomialSpecChart, AffineSpace.homOfVector_appTop_coord]

set_option backward.isDefEq.respectTransparency false in
instance : IsOpenImmersion X.laurentSpecToPolynomialSpec := by
  refine relativeGluingMap_of_forall _ @IsOpenImmersion _ _
    IdealSheafData.toPolynomialPresheaf_comp_polynomialToLaurent fun U ↦ ?_
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U.1)[X] Γ(X, U.1)[T;T⁻¹])))
  exact IsOpenImmersion.of_isLocalization (Polynomial.X : Γ(X, U.1)[X])

set_option backward.isDefEq.respectTransparency false in
/-- The punctured line `𝔾_{m,X} ⊆ 𝔸¹_X` is the locus where the coordinate `t` is invertible. -/
lemma opensRange_laurentSpecToPolynomialSpec :
    X.laurentSpecToPolynomialSpec.opensRange =
      X.polynomialSpec.basicOpen X.polynomialSpecCoord := by
  refine opens_ext _ fun U ↦ TopologicalSpace.Opens.ext ?_
  have h := isPullback_ι_relativeGluingMap X.coequifibered_toPolynomialPresheaf
    X.coequifibered_toLaurentPresheaf _
    IdealSheafData.toPolynomialPresheaf_comp_polynomialToLaurent U
  have e1 := Scheme.range_snd_of_isPullback h
  have e2 : Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1)[X] Γ(X, U.1)[T;T⁻¹]))) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Γ(X, U.1)[X]) : Set (PrimeSpectrum Γ(X, U.1)[X])) :=
    PrimeSpectrum.localization_away_comap_range _ _
  have e3 : ((Spec (.of Γ(X, U.1)[X])).basicOpen ((ΓSpecIso (.of Γ(X, U.1)[X])).inv Polynomial.X) :
      Set (Spec (.of Γ(X, U.1)[X]))) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Γ(X, U.1)[X]) : Set (PrimeSpectrum Γ(X, U.1)[X])) :=
    congrArg _ (basicOpen_eq_of_affine _)
  rw [Scheme.preimage_basicOpen_top, ι_appTop_polynomialSpecCoord]
  exact e1.symm.trans (e2.trans e3.symm)

/-! ### The relative spectrum of `𝒪_X` -/

lemma coequifibered_id_affineStructurePresheaf :
    NatTrans.Coequifibered (𝟙 X.affineStructurePresheaf) :=
  NatTrans.Coequifibered.of_isIso _

/-- `Spec_X 𝒪_X`, which is `X` itself. -/
noncomputable abbrev structureSpec : Scheme.{u} :=
  (relativeGluingData X.coequifibered_id_affineStructurePresheaf).glued

instance : IsIso (relativeGluingData X.coequifibered_id_affineStructurePresheaf).toBase :=
  toBase_of_forall _ (.isomorphisms _) fun _ ↦
    (MorphismProperty.isomorphisms.iff _).mpr (by rw [NatTrans.id_app, Spec.map_id]; infer_instance)

namespace IdealSheafData

variable {X} (I : X.IdealSheafData)

/-- The map `𝒪_X[t] ⟶ (𝒪_X / I)[t]`. -/
noncomputable abbrev polynomialToQuotientPolynomial :
    X.polynomialPresheaf ⟶ I.quotientPolynomialAlgebra :=
  Functor.whiskerRight I.toQuotientAlgebra CommRingCat.polynomialFunctor

/-- The relative affine line of `V(I)` is the base change of the one of `X`:
`Spec_X (𝒪_X / I)[t] = V(I) ×_X Spec_X 𝒪_X[t]`. -/
theorem isPullback_quotientPolynomialSpec :
    IsPullback
      (relativeGluingMap I.coequifibered_toQuotientAlgebra
        I.coequifibered_toQuotientPolynomialAlgebra
        (I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC))
      (relativeGluingMap X.coequifibered_toPolynomialPresheaf
        I.coequifibered_toQuotientPolynomialAlgebra I.polynomialToQuotientPolynomial)
      (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase X.polynomialSpecProj := by
  have h := isPullback_relativeGluingMap X.coequifibered_id_affineStructurePresheaf
    I.coequifibered_toQuotientAlgebra X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toQuotientPolynomialAlgebra I.toQuotientAlgebra X.toPolynomialPresheaf
    (I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC) I.polynomialToQuotientPolynomial
    (Category.id_comp _) rfl fun U ↦
      CommRingCat.coequifibered_polynomialC (I.toQuotientAlgebra.app (.op U))
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso (relativeGluingData X.coequifibered_id_affineStructurePresheaf).toBase)
    (by simp) (by simp) ?_ ?_
  · simp only [Iso.refl_hom, asIso_hom, Category.id_comp]
    exact relativeGluingMap_toBase _ _ _ (Category.id_comp _)
  · simp only [Iso.refl_hom, asIso_hom, Category.id_comp]
    exact relativeGluingMap_toBase _ _ _ (Category.id_comp _)

lemma toQuotientPresheaf_comp_normalConeToQuotient :
    toQuotientPresheaf I.tIdeal I.map_tIdeal ≫ I.normalConeToQuotient =
      I.reesToQuotientPolynomial ≫ I.quotientPolynomialEvalZero :=
  rfl

lemma polynomialC_comp_quotientPolynomialEvalZero :
    I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC ≫ I.quotientPolynomialEvalZero =
      𝟙 _ := by
  ext U x
  exact Polynomial.eval_C

/-- The map `𝒪_X[t] / t ⟶ 𝒪_X / I`, `t ↦ 0`. -/
noncomputable def polynomialZeroToQuotient : X.polynomialZeroPresheaf ⟶ I.quotientAlgebra where
  app U := CommRingCat.ofHom (Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (I.siteIdeal U.unop)).comp (Polynomial.evalRingHom 0))
    fun _ ha ↦ Polynomial.span_X_le_ker_mk_comp_evalRingHom_zero _ ha)
  naturality U V i := CommRingCat.hom_ext
    (Polynomial.quotientMap_comp_lift_evalRingHom_zero _ _ _
      (le_comap_quotientPresheaf _ I.map_siteIdeal i) (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton]
        exact le_of_eq (congrArg (fun p ↦ Ideal.span {p}) (Polynomial.map_X _)))).symm

lemma polynomialToPolynomialZero_comp_polynomialZeroToQuotient :
    X.polynomialToPolynomialZero ≫ I.polynomialZeroToQuotient =
      I.polynomialToQuotientPolynomial ≫ I.quotientPolynomialEvalZero := by
  ext U p
  change Ideal.Quotient.mk _ (Polynomial.eval 0 p) = Polynomial.eval 0 (Polynomial.map _ p)
  rw [Polynomial.eval_zero_map]
  rfl

lemma toPolynomialZeroPresheaf_comp_polynomialZeroToQuotient :
    X.toPolynomialZeroPresheaf ≫ I.polynomialZeroToQuotient = I.toQuotientAlgebra := by
  ext U x
  change Ideal.Quotient.mk _ (Polynomial.eval 0 (Polynomial.C x)) = _
  rw [Polynomial.eval_C]
  rfl

lemma toPolynomialZeroPresheaf_comp_polynomialZeroToNormalCone :
    X.toPolynomialZeroPresheaf ≫ I.polynomialZeroToNormalCone =
      I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal := by
  ext U x
  change Ideal.Quotient.mk _ ((I.siteIdeal U.unop).toExtendedReesAlgebra (Polynomial.C x)) =
    Ideal.Quotient.mk _ _
  rw [Ideal.toExtendedReesAlgebra_C]
  rfl

end IdealSheafData

end AlgebraicGeometry.Scheme
