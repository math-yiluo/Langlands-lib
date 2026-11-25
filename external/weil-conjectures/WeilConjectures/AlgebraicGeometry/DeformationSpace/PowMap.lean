/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.RingTheory.ExtendedReesAlgebraPow
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-!
# The power map of deformation spaces

Let `I, J` be ideal sheaves on a scheme `X` with `J ⊆ I^m` on every affine open. The power maps
`Γ(X, U)[t, J t⁻¹] ⟶ Γ(X, U)[t, I t⁻¹]`, `t ↦ t^m`, of extended Rees algebras
(`Ideal.extendedReesAlgebraPowMap`) induce a morphism `D_I X ⟶ D_J X` of deformation spaces over
`X`, covering the power map `t ↦ t^m` of the affine line.

## Main definitions

- `AlgebraicGeometry.AffineSpace.linePowMap`: the power map `t ↦ t^m` of `𝔸¹_S`.
- `AlgebraicGeometry.Scheme.polynomialSpecPowMap`: the power map `t ↦ t^m` of `Spec_X 𝒪_X[t]`.
- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpacePowMap`: the power map
  `D_I X ⟶ D_J X`.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.deformationSpacePowMap_toPolynomialSpec`: the power map
  of deformation spaces covers the power map of the relative affine line.
- `AlgebraicGeometry.Scheme.IdealSheafData.isFinite_deformationSpacePowMap`: it is finite if
  `J = I^m` with `m > 0` and `I` is of finite type on affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace AffineSpace

/-- The power map `t ↦ t^m` of the affine line `𝔸¹_S`. -/
noncomputable def linePowMap (S : Scheme.{u}) (m : ℕ) :
    𝔸(ULift.{u} (Fin 1); S) ⟶ 𝔸(ULift.{u} (Fin 1); S) :=
  homOfVector (𝔸(ULift.{u} (Fin 1); S) ↘ S) fun i ↦ coord S i ^ m

@[reassoc (attr := simp)]
lemma linePowMap_over (S : Scheme.{u}) (m : ℕ) :
    linePowMap S m ≫ 𝔸(ULift.{u} (Fin 1); S) ↘ S = 𝔸(ULift.{u} (Fin 1); S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma linePowMap_appTop_coord (S : Scheme.{u}) (m : ℕ) (i : ULift.{u} (Fin 1)) :
    (linePowMap S m).appTop (coord S i) = coord S i ^ m :=
  homOfVector_appTop_coord _ _ _

/-- The power map of the affine line is natural in the base. -/
@[reassoc]
lemma map_linePowMap {S T : Scheme.{u}} (f : S ⟶ T) (m : ℕ) :
    map (ULift.{u} (Fin 1)) f ≫ linePowMap T m = linePowMap S m ≫ map (ULift.{u} (Fin 1)) f := by
  refine hom_ext ?_ fun i ↦ ?_
  · simp
  · simp

end AffineSpace

namespace Scheme

open AffineZariskiSite

variable (X : Scheme.{u})

/-- The substitution `t ↦ t^m` on the quasi-coherent algebra `𝒪_X[t]`. -/
@[simps]
noncomputable def polynomialExpand (m : ℕ) : X.polynomialPresheaf ⟶ X.polynomialPresheaf where
  app U := CommRingCat.ofHom (Polynomial.expand (X.affineStructurePresheaf.obj U) m).toRingHom
  naturality U V i := by
    ext p : 2
    exact (Polynomial.map_expand).symm

lemma toPolynomialPresheaf_comp_polynomialExpand (m : ℕ) :
    X.toPolynomialPresheaf ≫ X.polynomialExpand m = X.toPolynomialPresheaf := by
  ext U x
  exact Polynomial.expand_C m x

/-- The power map `t ↦ t^m` of the relative affine line `Spec_X 𝒪_X[t]`. -/
noncomputable def polynomialSpecPowMap (m : ℕ) : X.polynomialSpec ⟶ X.polynomialSpec :=
  relativeGluingMap _ _ (X.polynomialExpand m)

@[reassoc (attr := simp)]
lemma polynomialSpecPowMap_proj (m : ℕ) :
    X.polynomialSpecPowMap m ≫ X.polynomialSpecProj = X.polynomialSpecProj :=
  relativeGluingMap_toBase _ _ _ (X.toPolynomialPresheaf_comp_polynomialExpand m)

set_option backward.isDefEq.respectTransparency false in
/-- Under `Spec_X 𝒪_X[t] ≅ 𝔸¹_X`, the power map of the relative affine line is the power map of
the affine line. -/
@[reassoc]
lemma polynomialSpecPowMap_polynomialSpecToAffineSpace (m : ℕ) :
    X.polynomialSpecPowMap m ≫ X.polynomialSpecToAffineSpace =
      X.polynomialSpecToAffineSpace ≫ AffineSpace.linePowMap X m := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp only [Category.assoc, polynomialSpecToAffineSpace_over, AffineSpace.linePowMap_over,
      polynomialSpecPowMap_proj]
  · rw [polynomialSpecPowMap, ι_relativeGluingMap_assoc, ι_polynomialSpecToAffineSpace,
      ι_polynomialSpecToAffineSpace_assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.linePowMap_appTop_coord,
      map_pow, polynomialSpecChart, AffineSpace.homOfVector_appTop_coord,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord]
    refine (congrArg (ΓSpecIso (X.polynomialPresheaf.obj (op U))).inv.hom
      (Polynomial.expand_X (R := X.presheaf.obj (op ((toOpensFunctor X).obj U))) m)).trans ?_
    exact map_pow _ _ _

namespace IdealSheafData

variable {X} {I J : X.IdealSheafData}

/-- The power map `𝒪_X[t, J t⁻¹] ⟶ 𝒪_X[t, I t⁻¹]`, `t ↦ t^m`, for `J ⊆ I^m`. -/
@[simps]
noncomputable def reesPowMap (m : ℕ) (hJ : ∀ U : X.AffineZariskiSite,
    J.siteIdeal U ≤ I.siteIdeal U ^ m) : J.reesPresheaf ⟶ I.reesPresheaf where
  app U := CommRingCat.ofHom (Ideal.extendedReesAlgebraPowMap m (hJ U.unop))
  naturality U V i := by
    ext : 1
    exact (Ideal.extendedReesAlgebraMap_comp_extendedReesAlgebraPowMap _ (I.map_siteIdeal i).le
      (J.map_siteIdeal i).le m (hJ _) (hJ _)).symm

variable {m : ℕ} (hJ : ∀ U : X.AffineZariskiSite, J.siteIdeal U ≤ I.siteIdeal U ^ m)

include hJ in
lemma toReesPresheaf_comp_reesPowMap : J.toReesPresheaf ≫ reesPowMap m hJ = I.toReesPresheaf := by
  ext U x
  exact Ideal.extendedReesAlgebraPowMap_algebraMap m (hJ U.unop) x

include hJ in
lemma polynomialToRees_comp_reesPowMap :
    J.polynomialToRees ≫ reesPowMap m hJ = X.polynomialExpand m ≫ I.polynomialToRees := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext ?_)
  exact Ideal.extendedReesAlgebraPowMap_comp_toExtendedReesAlgebra m (hJ U.unop)

variable (m) in
/-- The power map `D_I X ⟶ D_J X` of deformation spaces, for `J ⊆ I^m`. -/
noncomputable def deformationSpacePowMap : I.deformationSpace ⟶ J.deformationSpace :=
  relativeGluingMap J.coequifibered_toReesPresheaf I.coequifibered_toReesPresheaf (reesPowMap m hJ)

/-- The power map of deformation spaces lies over `X`. -/
@[reassoc (attr := simp)]
lemma deformationSpacePowMap_proj :
    deformationSpacePowMap m hJ ≫ J.deformationSpaceProj = I.deformationSpaceProj :=
  relativeGluingMap_toBase _ _ _ (toReesPresheaf_comp_reesPowMap hJ)

/-- The power map of deformation spaces covers the power map of the relative affine line. -/
@[reassoc]
lemma deformationSpacePowMap_toPolynomialSpec :
    deformationSpacePowMap m hJ ≫ J.deformationSpaceToPolynomialSpec =
      I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecPowMap m := by
  rw [deformationSpacePowMap, deformationSpaceToPolynomialSpec, deformationSpaceToPolynomialSpec,
    polynomialSpecPowMap, ← relativeGluingMap_comp, ← relativeGluingMap_comp,
    polynomialToRees_comp_reesPowMap]

/-- The power map of deformation spaces covers the power map of the affine line `𝔸¹_X`. -/
@[reassoc]
lemma deformationSpacePowMap_toAffineSpace :
    deformationSpacePowMap m hJ ≫ J.deformationSpaceToPolynomialSpec ≫
        X.polynomialSpecToAffineSpace =
      (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace) ≫
        AffineSpace.linePowMap X m := by
  rw [deformationSpacePowMap_toPolynomialSpec_assoc,
    polynomialSpecPowMap_polynomialSpecToAffineSpace, Category.assoc]

/-- **Finiteness of the power map.** If `I^m ⊆ J ⊆ I^m` with `m > 0` and `I` is finitely
generated on affine opens, the power map `D_I X ⟶ D_J X` is finite. -/
theorem isFinite_deformationSpacePowMap (hm : 0 < m)
    (hJ' : ∀ U : X.AffineZariskiSite, I.siteIdeal U ^ m ≤ J.siteIdeal U)
    (hI : ∀ U : X.AffineZariskiSite, (I.siteIdeal U).FG) :
    IsFinite (deformationSpacePowMap m hJ) :=
  relativeGluingMap_of_forall _ @IsFinite _ _ (toReesPresheaf_comp_reesPowMap hJ) fun U ↦
    (IsFinite.SpecMap_iff _).mpr
      (Ideal.finite_extendedReesAlgebraPowMap hm (hJ U) (hJ' U) (hI U))

/-! ### Ideal sheaves of global functions -/

lemma siteIdeal_ofIdealTop_span_pow (f : Γ(X, ⊤)) (m : ℕ) (U : X.AffineZariskiSite) :
    (ofIdealTop (Ideal.span {f ^ m})).siteIdeal U =
      (ofIdealTop (Ideal.span {f})).siteIdeal U ^ m := by
  rw [siteIdeal, siteIdeal, ofIdealTop_ideal, ofIdealTop_ideal, ← Ideal.map_pow,
    Ideal.span_singleton_pow]

lemma fg_siteIdeal_ofIdealTop {𝔞 : Ideal Γ(X, ⊤)} (h𝔞 : 𝔞.FG) (U : X.AffineZariskiSite) :
    ((ofIdealTop 𝔞).siteIdeal U).FG := by
  rw [siteIdeal, ofIdealTop_ideal]
  exact h𝔞.map _

/-! ### Zero sections -/

section ZeroSection

variable (I) in
lemma toReesPresheaf_comp_reesToQuotientPolynomial :
    I.toReesPresheaf ≫ I.reesToQuotientPolynomial = I.toQuotientPolynomialAlgebra := by
  ext U x
  exact Ideal.extendedReesAlgebraToPolynomial_algebraMap (I := I.siteIdeal U.unop) _
    Ideal.mk_ker.ge x

variable (I) in
/-- The zero section `Spec_X (𝒪_X / I)[t] ⟶ D_I X` of the deformation space, cut out by the
kernels of `Γ(X, U)[t, I t⁻¹] ⟶ (Γ(X, U) / I)[t]`. -/
noncomputable def quotientPolynomialSpecToDeformationSpace :
    I.quotientPolynomialSpec ⟶ I.deformationSpace :=
  relativeGluingMap I.coequifibered_toReesPresheaf I.coequifibered_toQuotientPolynomialAlgebra
    I.reesToQuotientPolynomial

variable (I) in
set_option backward.isDefEq.respectTransparency false in
/-- A point of the chart `Spec Γ(X, U)[t, I t⁻¹]` of `D_I X` lies on the zero section if and only
if it contains the kernel of `Γ(X, U)[t, I t⁻¹] ⟶ (Γ(X, U) / I)[t]`. -/
lemma ι_mem_range_quotientPolynomialSpecToDeformationSpace_iff (U : X.AffineZariskiSite)
    (p : Spec (I.reesPresheaf.obj (op U))) :
    colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U p ∈
        Set.range I.quotientPolynomialSpecToDeformationSpace ↔
      RingHom.ker (I.reesToQuotientPolynomial.app (op U)).hom ≤ p.asIdeal := by
  have e := Scheme.range_snd_of_isPullback (isPullback_ι_relativeGluingMap
    I.coequifibered_toReesPresheaf I.coequifibered_toQuotientPolynomialAlgebra
    I.reesToQuotientPolynomial I.toReesPresheaf_comp_reesToQuotientPolynomial U)
  have hs := Ideal.surjective_extendedReesAlgebraToPolynomial (I := I.siteIdeal U)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker.ge
  exact (Set.ext_iff.mp e p).symm.trans
    ((Set.ext_iff.mp (range_comap_of_surjective _ _ hs) p).trans
      (PrimeSpectrum.mem_zeroLocus _ _))

include hJ in
/-- **The power map detects the zero section.** If `J ⊆ I^m ⊆ J` on affine opens, a point of
`D_I X` whose image under the power map `D_I X ⟶ D_J X` lies on the zero section of `D_J X` lies on
the zero section of `D_I X`. -/
theorem mem_range_quotientPolynomialSpecToDeformationSpace_of_deformationSpacePowMap
    (hJ' : ∀ U : X.AffineZariskiSite, I.siteIdeal U ^ m ≤ J.siteIdeal U) {z : I.deformationSpace}
    (hz : deformationSpacePowMap m hJ z ∈ Set.range J.quotientPolynomialSpecToDeformationSpace) :
    z ∈ Set.range I.quotientPolynomialSpecToDeformationSpace := by
  obtain ⟨U, p, rfl⟩ : ∃ (U : X.AffineZariskiSite) (p : Spec (I.reesPresheaf.obj (op U))),
      colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U p = z :=
    (relativeGluingData I.coequifibered_toReesPresheaf).cover.exists_eq z
  rw [← Scheme.Hom.comp_apply, deformationSpacePowMap, ι_relativeGluingMap,
    Scheme.Hom.comp_apply] at hz
  replace hz := (ι_mem_range_quotientPolynomialSpecToDeformationSpace_iff J U _).mp hz
  exact (ι_mem_range_quotientPolynomialSpecToDeformationSpace_iff I U p).mpr
    (Ideal.ker_extendedReesAlgebraToPolynomial_le_of_le_comap m (hJ U) (hJ' U) p.asIdeal hz)

/-- For the zero ideal, the zero section `Spec_X (𝒪_X / ⊥)[t] ⟶ D_⊥ X` is an isomorphism. -/
instance isIso_quotientPolynomialSpecToDeformationSpace_bot :
    IsIso (⊥ : X.IdealSheafData).quotientPolynomialSpecToDeformationSpace :=
  relativeGluingMap_of_forall _ (MorphismProperty.isomorphisms _) _ _
    (toReesPresheaf_comp_reesToQuotientPolynomial ⊥) fun U ↦ by
      have : IsIso ((⊥ : X.IdealSheafData).reesToQuotientPolynomial.app (op U)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨Ideal.injective_extendedReesAlgebraToPolynomial_bot,
            Ideal.surjective_extendedReesAlgebraToPolynomial _ Ideal.Quotient.mk_surjective
              Ideal.mk_ker.ge⟩
      exact (inferInstance : IsIso (Spec.map
        ((⊥ : X.IdealSheafData).reesToQuotientPolynomial.app (op U))))

variable (I) in
/-- `I` maps to the zero ideal of `V(I)`, chart by chart. -/
lemma siteIdeal_map_appLE_subschemeι_le_bot ⦃U' : I.subscheme.AffineZariskiSite⦄
    ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ I.subschemeι ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map (I.subschemeι.appLE U.1 U'.1 hU).hom ≤
      (⊥ : I.subscheme.IdealSheafData).siteIdeal U' :=
  siteIdeal_map_appLE_le_of_le_map I.le_map_bot_subschemeι hU

/-- The relative affine line of `V(I) ⊆ X`, as the relative spectrum of `(𝒪_X / I)[t]` over `X`,
is the base change of the one over `V(I)`, chart by chart. -/
lemma isPushout_quotientPolynomialPullbackData_subschemeι {U' : I.subscheme.AffineZariskiSite}
    {U : X.AffineZariskiSite} (hU : U'.1 ≤ I.subschemeι ⁻¹ᵁ U.1) :
    IsPushout (I.subschemeι.appLE U.1 U'.1 hU) (I.toQuotientPolynomialAlgebra.app (op U))
      ((⊥ : I.subscheme.IdealSheafData).toQuotientPolynomialAlgebra.app (op U'))
      ((quotientPolynomialPullbackData I.subschemeι I ⊥
        I.siteIdeal_map_appLE_subschemeι_le_bot).map hU) :=
  (CommRingCat.isPushout_quotient_of_map_eq _ (I.siteIdeal U)
    ((I.siteIdeal_map_appLE_subschemeι_le_bot hU).antisymm bot_le)).flip.paste_vert
    (CommRingCat.coequifibered_polynomialC _)

/-- The relative affine line `Spec_X (𝒪_X / I)[t]` lies over `V(I)`. -/
lemma range_toBase_quotientPolynomialSpec :
    Set.range (relativeGluingData I.coequifibered_toQuotientPolynomialAlgebra).toBase ⊆
      Set.range I.subschemeι := by
  rintro _ ⟨w, rfl⟩
  have hsupp := Scheme.Hom.support_ker
    (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase
  rw [ker_quotientSpec_toBase] at hsupp
  rw [← relativeGluingMap_toBase I.coequifibered_toQuotientAlgebra
    I.coequifibered_toQuotientPolynomialAlgebra
    (I.quotientAlgebra.whiskerLeft CommRingCat.polynomialC) rfl, Scheme.Hom.comp_apply,
    range_subschemeι, hsupp]
  exact subset_closure ⟨_, rfl⟩

variable (I) in
/-- The zero section of `D_I X` is the image of the deformation space `D_⊥ V(I) = 𝔸¹_{V(I)}` of
the zero ideal of `V(I)` under the morphism induced by `V(I) ⟶ X`. -/
theorem range_deformationSpaceMap_subschemeι :
    Set.range (deformationSpaceMap I.subschemeι I ⊥ I.siteIdeal_map_appLE_subschemeι_le_bot) =
      Set.range I.quotientPolynomialSpecToDeformationSpace := by
  set D := quotientPolynomialPullbackData I.subschemeι I ⊥
    I.siteIdeal_map_appLE_subschemeι_le_bot
  have hR : D.comparison I.coequifibered_toQuotientPolynomialAlgebra
        (⊥ : I.subscheme.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra ≫
      I.quotientPolynomialSpecToDeformationSpace =
      (⊥ : I.subscheme.IdealSheafData).quotientPolynomialSpecToDeformationSpace ≫
        deformationSpaceMap I.subschemeι I ⊥ I.siteIdeal_map_appLE_subschemeι_le_bot :=
    PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
      (reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map _ _ _ _)
  have hpb := D.isPullback_comparison I.coequifibered_toQuotientPolynomialAlgebra
    (⊥ : I.subscheme.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra fun x ↦ by
      obtain ⟨⟨⟨U', U⟩, hU⟩, hx⟩ := Pairs.exists_mem I.subschemeι x
      exact ⟨U', U, hU, hx, isPushout_quotientPolynomialPullbackData_subschemeι hU⟩
  have hsurj := Scheme.range_snd_of_isPullback hpb.flip
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := Scheme.Hom.surjective
      (⊥ : I.subscheme.IdealSheafData).quotientPolynomialSpecToDeformationSpace w
    rw [← Scheme.Hom.comp_apply, ← hR, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · rintro _ ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ : w ∈ Set.range (D.comparison _ _) := by
      rw [hsurj]
      exact range_toBase_quotientPolynomialSpec ⟨w, rfl⟩
    rw [← Scheme.Hom.comp_apply, hR, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

include hJ in
/-- **The power map detects the zero section**, in terms of the closed subschemes `V(I) ⊆ X` and
`V(J) ⊆ X`: if `J ⊆ I^m ⊆ J` on affine opens, a point of `D_I X` whose image under the power map
`D_I X ⟶ D_J X` lies in the image of `D_⊥ V(J) ⟶ D_J X` lies in the image of
`D_⊥ V(I) ⟶ D_I X`. -/
theorem mem_range_deformationSpaceMap_subschemeι_of_deformationSpacePowMap
    (hJ' : ∀ U : X.AffineZariskiSite, I.siteIdeal U ^ m ≤ J.siteIdeal U) {z : I.deformationSpace}
    (hz : deformationSpacePowMap m hJ z ∈ Set.range
      (deformationSpaceMap J.subschemeι J ⊥ J.siteIdeal_map_appLE_subschemeι_le_bot)) :
    z ∈ Set.range
      (deformationSpaceMap I.subschemeι I ⊥ I.siteIdeal_map_appLE_subschemeι_le_bot) := by
  rw [range_deformationSpaceMap_subschemeι] at hz ⊢
  exact mem_range_quotientPolynomialSpecToDeformationSpace_of_deformationSpacePowMap hJ hJ' hz

include hJ in
/-- **The power map preserves the zero section.** For `m > 0` and `J ⊆ I^m` on affine opens, the
power map `D_I X ⟶ D_J X` sends the zero section of `D_I X` into that of `D_J X`. -/
theorem deformationSpacePowMap_mem_range_quotientPolynomialSpecToDeformationSpace (hm : 0 < m)
    {z : I.deformationSpace} (hz : z ∈ Set.range I.quotientPolynomialSpecToDeformationSpace) :
    deformationSpacePowMap m hJ z ∈ Set.range J.quotientPolynomialSpecToDeformationSpace := by
  obtain ⟨U, p, rfl⟩ : ∃ (U : X.AffineZariskiSite) (p : Spec (I.reesPresheaf.obj (op U))),
      colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U p = z :=
    (relativeGluingData I.coequifibered_toReesPresheaf).cover.exists_eq z
  replace hz := (ι_mem_range_quotientPolynomialSpecToDeformationSpace_iff I U p).mp hz
  rw [← Scheme.Hom.comp_apply, deformationSpacePowMap, ι_relativeGluingMap,
    Scheme.Hom.comp_apply]
  have hle : RingHom.ker (J.reesToQuotientPolynomial.app (op U)).hom ≤
      p.asIdeal.comap (Ideal.extendedReesAlgebraPowMap m (hJ U)) := fun x hx ↦
    Ideal.mem_comap.mpr (hz (Ideal.extendedReesAlgebraPowMap_mem_ker hm (hJ U) hx))
  exact (ι_mem_range_quotientPolynomialSpecToDeformationSpace_iff J U _).mpr hle

include hJ in
/-- **The power map preserves the zero section**, in terms of the closed subschemes `V(I) ⊆ X` and
`V(J) ⊆ X`: for `m > 0` and `J ⊆ I^m` on affine opens, the power map `D_I X ⟶ D_J X` sends the
image of `D_⊥ V(I) ⟶ D_I X` into the image of `D_⊥ V(J) ⟶ D_J X`. -/
theorem deformationSpacePowMap_mem_range_deformationSpaceMap_subschemeι (hm : 0 < m)
    {z : I.deformationSpace} (hz : z ∈ Set.range
      (deformationSpaceMap I.subschemeι I ⊥ I.siteIdeal_map_appLE_subschemeι_le_bot)) :
    deformationSpacePowMap m hJ z ∈ Set.range
      (deformationSpaceMap J.subschemeι J ⊥ J.siteIdeal_map_appLE_subschemeι_le_bot) := by
  rw [range_deformationSpaceMap_subschemeι] at hz ⊢
  exact deformationSpacePowMap_mem_range_quotientPolynomialSpecToDeformationSpace hJ hm hz

end ZeroSection

end IdealSheafData

end Scheme

end AlgebraicGeometry
