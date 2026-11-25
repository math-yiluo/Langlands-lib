/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.NormalBundle
public import WeilConjectures.RingTheory.ExtendedReesAlgebraGraded

/-!
# Functoriality of normal cones and their zero sections

Let `h : X' ⟶ X` be a morphism of schemes and `I`, `J` ideal sheaves on `X`, `X'` with `h^* I ⊆ J`.
The maps of associated graded algebras `gr_I 𝒪_X ⟶ h_* gr_J 𝒪_{X'}` induce a morphism of normal
cones `N_J X' ⟶ N_I X`, the special fibre of the morphism `D_J X' ⟶ D_I X` of deformation spaces.

The augmentation `gr_I 𝒪_X ⟶ 𝒪_X / I` defines the zero section `V(I) ⟶ N_I X`, a closed immersion.
Blueprint `lemma-normal-cones-contracting-ideals` (2) (Varshavsky, *Lefschetz–Verdier trace formula
and a generalization of a theorem of Fujiwara*): if moreover `(h^* I)^n ⊆ J^{n+1}` for some `n ≥ 1`,
then the morphism of normal cones lands set-theoretically in the zero section, since the irrelevant
ideal of `gr_I` is mapped to nilpotent elements of `gr_J`.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.normalConeMap`: the morphism `N_J X' ⟶ N_I X`.
- `AlgebraicGeometry.Scheme.IdealSheafData.quotientSpecMap`: the morphism `V(J) ⟶ V(I)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.normalConeZeroSection`: the zero section
  `V(I) ⟶ N_I X`.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace`: the morphism
  of normal cones is the restriction of the morphism of deformation spaces.
- `AlgebraicGeometry.Scheme.IdealSheafData.range_normalConeMap_subset_range_normalConeZeroSection`:
  blueprint `lemma-normal-cones-contracting-ideals` (2).
- `AlgebraicGeometry.Scheme.IdealSheafData.preimage_range_normalConeZeroSection`: blueprint
  `lemma-normal-cones-contracting-ideals` (1), set-theoretically: if `J = h^* I · 𝒪_{X'}`, the
  preimage of the zero section of `N_I X` is the zero section of `N_J X'`.
- Over a locally noetherian `X`, the deformation space and the normal cone are locally of finite
  type over `X` (they are affine, hence quasi-compact and separated, over `X` in general).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite Opposite

namespace IdealSheafData

/-! ### The zero section of the normal cone -/

section ZeroSection

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The zero section `V(I) ⟶ N_I X` of the normal cone, given by the augmentation
`⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_X / I` killing the irrelevant ideal. -/
noncomputable def normalConeZeroSection : I.quotientSpec ⟶ I.normalCone :=
  relativeGluingMap I.coequifibered_toNormalConePresheaf I.coequifibered_toQuotientAlgebra
    I.normalConeToQuotient

/-- The zero section lies over `X`. -/
@[reassoc (attr := simp)]
lemma normalConeZeroSection_toBase :
    I.normalConeZeroSection ≫ (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase =
      (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase :=
  relativeGluingMap_toBase _ _ _ I.toNormalConePresheaf_comp_normalConeToQuotient

/-- The zero section is a section of the projection `N_I X ⟶ V(I)`. -/
@[reassoc (attr := simp)]
lemma normalConeZeroSection_normalConeToQuotientSpec :
    I.normalConeZeroSection ≫ I.normalConeToQuotientSpec = 𝟙 _ := by
  rw [normalConeZeroSection, normalConeToQuotientSpec, ← relativeGluingMap_comp,
    quotientToNormalCone_comp_normalConeToQuotient, relativeGluingMap_id]

lemma surjective_normalConeToQuotient_app (U : X.AffineZariskiSiteᵒᵖ) :
    Function.Surjective (I.normalConeToQuotient.app U) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨((I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal).app U) x,
    (CommRingCat.comp_apply _ _ x).symm.trans
      congr($(congr($(I.toNormalConePresheaf_comp_normalConeToQuotient).app U)) x)⟩

/-- The zero section of the normal cone is a closed immersion. -/
instance : IsClosedImmersion I.normalConeZeroSection :=
  relativeGluingMap_of_forall _ @IsClosedImmersion _ _
    I.toNormalConePresheaf_comp_normalConeToQuotient fun _ ↦
      IsClosedImmersion.spec_of_surjective _ (I.surjective_normalConeToQuotient_app _)

/-- A point of the chart `Spec gr_I(U)` of the normal cone whose prime contains the irrelevant
ideal (the kernel of the augmentation `gr_I(U) ⟶ Γ(U) / I(U)`) lies on the zero section. -/
lemma ι_mem_range_normalConeZeroSection (U : X.AffineZariskiSite)
    (z : Spec (I.normalConePresheaf.obj (op U)))
    (hz : RingHom.ker (I.normalConeToQuotient.app (op U)).hom ≤ z.asIdeal) :
    colimit.ι (relativeGluingData I.coequifibered_toNormalConePresheaf).functor U z ∈
      Set.range I.normalConeZeroSection := by
  have hz' : z ∈ Set.range (Spec.map (I.normalConeToQuotient.app (op U))) := by
    change z ∈ Set.range (PrimeSpectrum.comap (I.normalConeToQuotient.app (op U)).hom)
    rw [range_comap_of_surjective _ _ (I.surjective_normalConeToQuotient_app _)]
    exact hz
  obtain ⟨w, rfl⟩ := hz'
  refine ⟨colimit.ι (relativeGluingData I.coequifibered_toQuotientAlgebra).functor U w, ?_⟩
  rw [← Scheme.Hom.comp_apply, normalConeZeroSection, ι_relativeGluingMap, Scheme.Hom.comp_apply]
  rfl

/-- The augmentation `gr_I(U) ⟶ Γ(U) / I(U)` sends the class of `x ∈ Γ(U)[t, I t⁻¹]` to the class
of its coefficient of `t⁰`. -/
lemma normalConeToQuotient_app_mk (U : X.AffineZariskiSiteᵒᵖ)
    (x : (I.siteIdeal U.unop).extendedReesAlgebra) :
    I.normalConeToQuotient.app U (Ideal.Quotient.mk (I.tIdeal U) x) =
      Ideal.Quotient.mk (I.siteIdeal U.unop) ((x : LaurentPolynomial Γ(X, U.unop.1)).coeff 0) :=
  Ideal.eval_zero_extendedReesAlgebraToPolynomial _ Ideal.mk_ker.ge x

end ZeroSection

/-! ### Finiteness -/

section FiniteType

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The inclusion of the normal cone into the deformation space lies over `X`. -/
@[reassoc (attr := simp)]
lemma normalConeToDeformationSpace_deformationSpaceProj :
    I.normalConeToDeformationSpace ≫ I.deformationSpaceProj =
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase :=
  relativeGluingMap_toBase _ _ _ rfl

/-- The normal cone is a closed subscheme of the deformation space. -/
instance : IsClosedImmersion I.normalConeToDeformationSpace :=
  relativeGluingMap_of_forall _ @IsClosedImmersion _ _ rfl fun _ ↦
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Over a locally noetherian scheme, the deformation space is locally of finite type: the
extended Rees algebra of a finitely generated ideal is a finitely generated algebra. -/
instance [IsLocallyNoetherian X] : LocallyOfFiniteType I.deformationSpaceProj :=
  toBase_of_forall _ @LocallyOfFiniteType fun U ↦ by
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    have := Ideal.finiteType_extendedReesAlgebra (IsNoetherian.noetherian (I.siteIdeal U))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr this

/-- Over a locally noetherian scheme, the normal cone is locally of finite type. -/
instance [IsLocallyNoetherian X] :
    LocallyOfFiniteType (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase := by
  rw [← normalConeToDeformationSpace_deformationSpaceProj]
  infer_instance

end FiniteType

/-! ### Functoriality -/

variable {X X' : Scheme.{u}} (h : X' ⟶ X) (I : X.IdealSheafData) (J : X'.IdealSheafData)
  (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
    (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')

lemma map_tIdeal_extendedReesPullbackData_map {U' : X'.AffineZariskiSite}
    {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    (I.tIdeal (op U)).map ((extendedReesPullbackData h I J hJ).map hU).hom = J.tIdeal (op U') := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun t ↦ Ideal.span {t}) (Ideal.extendedReesAlgebraMap_T _ _ (hJ hU))

/-- The base change data `gr_I Γ(X, U) ⟶ gr_J Γ(X', U')` of the associated graded algebras along
`h : X' ⟶ X`, for ideal sheaves with `h^* I ⊆ J`. -/
@[simps]
noncomputable def normalConePullbackData :
    PullbackData h (I.toReesPresheaf ≫ toQuotientPresheaf I.tIdeal I.map_tIdeal)
      (J.toReesPresheaf ≫ toQuotientPresheaf J.tIdeal J.map_tIdeal) where
  map {U' U} hU := CommRingCat.ofHom (Ideal.quotientMap (J.tIdeal (op U'))
    ((extendedReesPullbackData h I J hJ).map hU).hom
    (Ideal.map_le_iff_le_comap.mp (map_tIdeal_extendedReesPullbackData_map h I J hJ hU).le))
  map_naturality i' i h₁ h₂ := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    exact congrArg (Ideal.Quotient.mk _)
      congr($((extendedReesPullbackData h I J hJ).map_naturality i' i h₁ h₂) x)
  app_comp_map hU := by
    ext x
    exact congrArg (Ideal.Quotient.mk _)
      congr($((extendedReesPullbackData h I J hJ).app_comp_map hU) x)

/-- The base change data `Γ(X, U) / I ⟶ Γ(X', U') / J` along `h : X' ⟶ X`, for ideal sheaves with
`h^* I ⊆ J`. -/
@[simps]
noncomputable def quotientPullbackData :
    PullbackData h I.toQuotientAlgebra J.toQuotientAlgebra where
  map {U' U} hU := CommRingCat.ofHom
    (Ideal.quotientMap (J.siteIdeal U') (h.appLE U.1 U'.1 hU).hom
      (Ideal.map_le_iff_le_comap.mp (hJ hU)))
  map_naturality i' i h₁ h₂ := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    exact congrArg (Ideal.Quotient.mk _) congr($(h.affineStructurePresheaf_map_appLE i' i h₁ h₂) x)
  app_comp_map hU := by
    ext x
    rfl

/-- The morphism `N_J X' ⟶ N_I X` of normal cones over `h : X' ⟶ X`, for ideal sheaves with
`h^* I ⊆ J`, induced by the maps of associated graded algebras `gr_I 𝒪_X ⟶ gr_J 𝒪_{X'}`. -/
noncomputable def normalConeMap : J.normalCone ⟶ I.normalCone :=
  (normalConePullbackData h I J hJ).comparison _ _

/-- The morphism `V(J) ⟶ V(I)` of closed subschemes over `h : X' ⟶ X`, for ideal sheaves with
`h^* I ⊆ J`. -/
noncomputable def quotientSpecMap : J.quotientSpec ⟶ I.quotientSpec :=
  (quotientPullbackData h I J hJ).comparison _ _

/-- The morphism of normal cones lies over `h : X' ⟶ X`. -/
@[reassoc]
lemma normalConeMap_toBase :
    normalConeMap h I J hJ ≫ (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase =
      (relativeGluingData J.coequifibered_toNormalConePresheaf).toBase ≫ h :=
  PullbackData.comparison_toBase _ _ _

/-- The morphism `V(J) ⟶ V(I)` lies over `h : X' ⟶ X`. -/
@[reassoc]
lemma quotientSpecMap_toBase :
    quotientSpecMap h I J hJ ≫ (relativeGluingData I.coequifibered_toQuotientAlgebra).toBase =
      (relativeGluingData J.coequifibered_toQuotientAlgebra).toBase ≫ h :=
  PullbackData.comparison_toBase _ _ _

/-- The morphism of normal cones is the restriction of the morphism `D_J X' ⟶ D_I X` of
deformation spaces to the special fibres. -/
@[reassoc]
lemma normalConeMap_normalConeToDeformationSpace :
    normalConeMap h I J hJ ≫ I.normalConeToDeformationSpace =
      J.normalConeToDeformationSpace ≫ deformationSpaceMap h I J hJ :=
  PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _ fun _ ↦ rfl

/-- The morphism of normal cones is compatible with the projections `N_J X' ⟶ V(J)` and
`N_I X ⟶ V(I)`. -/
@[reassoc]
lemma normalConeMap_normalConeToQuotientSpec :
    normalConeMap h I J hJ ≫ I.normalConeToQuotientSpec =
      J.normalConeToQuotientSpec ≫ quotientSpecMap h I J hJ :=
  PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _ fun hU ↦ by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    exact congrArg (Ideal.Quotient.mk _)
      congr($((extendedReesPullbackData h I J hJ).app_comp_map hU) x)

/-- The morphism of normal cones is compatible with the zero sections. -/
@[reassoc]
lemma normalConeZeroSection_normalConeMap :
    J.normalConeZeroSection ≫ normalConeMap h I J hJ =
      quotientSpecMap h I J hJ ≫ I.normalConeZeroSection :=
  (PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _ fun {U'} {U} hU ↦ by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
    change (quotientPullbackData h I J hJ).map hU (I.normalConeToQuotient.app (op U)
        (Ideal.Quotient.mk _ x)) =
      J.normalConeToQuotient.app (op U') (Ideal.Quotient.mk _
        ((extendedReesPullbackData h I J hJ).map hU x))
    rw [normalConeToQuotient_app_mk, normalConeToQuotient_app_mk]
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ ((LaurentPolynomial.mapRingHom _ _).coeff 0)
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    rfl).symm

/-- **Blueprint `lemma-normal-cones-contracting-ideals` (2).** Let `h : X' ⟶ X` and ideal sheaves
`I`, `J` with `L = h^* I ⊆ J` and `L^n ⊆ J^{n+1}` for some `n ≥ 1` (on all pairs of affine opens
`U' ⊆ h⁻¹ U`). Then the morphism of normal cones `N_J X' ⟶ N_I X` lands set-theoretically in the
zero section `V(I) ⟶ N_I X`. -/
theorem range_normalConeMap_subset_range_normalConeZeroSection {n : ℕ} (hn : 0 < n)
    (hJn : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ^ n ≤ J.siteIdeal U' ^ (n + 1)) :
    Set.range (normalConeMap h I J hJ) ⊆ Set.range I.normalConeZeroSection := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨q, y, rfl⟩ := (pairsCover h J.coequifibered_toNormalConePresheaf).exists_eq x
  obtain ⟨⟨U', U⟩, hU⟩ := q
  change (colimit.ι (relativeGluingData J.coequifibered_toNormalConePresheaf).functor U' ≫
    normalConeMap h I J hJ) y ∈ _
  rw [normalConeMap, PullbackData.ι_comparison _ _ _ hU, Scheme.Hom.comp_apply]
  refine I.ι_mem_range_normalConeZeroSection U _ fun a ha ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha0 : (a.1 : LaurentPolynomial Γ(X, U.1)).coeff 0 ∈
      I.siteIdeal U := by
    rw [RingHom.mem_ker] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((I.normalConeToQuotient_app_mk (op U) a).symm.trans ha)
  have hpow : ((normalConePullbackData h I J hJ).map hU (Ideal.Quotient.mk _ a)) ^ n = 0 := by
    change (Ideal.Quotient.mk (J.tIdeal (op U')) ((I.siteIdeal U).extendedReesAlgebraMap
      (h.appLE U.1 U'.1 hU).hom (J.siteIdeal U') (hJ hU) a)) ^ n = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_extendedReesAlgebraMap_mem_span_extendedReesAlgebraT _ _ _ hn (hJn hU) ha0
  change (normalConePullbackData h I J hJ).map hU (Ideal.Quotient.mk _ a) ∈ y.asIdeal
  refine y.isPrime.mem_of_pow_mem n ?_
  rw [hpow]
  exact zero_mem _

/-- A point of the chart `Spec gr_I(U)` of the normal cone lying on the zero section has a prime
containing the irrelevant ideal. -/
lemma ker_le_of_ι_mem_range_normalConeZeroSection {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.AffineZariskiSite) (z : Spec (I.normalConePresheaf.obj (op U)))
    (hz : colimit.ι (relativeGluingData I.coequifibered_toNormalConePresheaf).functor U z ∈
      Set.range I.normalConeZeroSection) :
    RingHom.ker (I.normalConeToQuotient.app (op U)).hom ≤ z.asIdeal := by
  obtain ⟨w, hw⟩ := hz
  have hsq := isPullback_ι_relativeGluingMap I.coequifibered_toNormalConePresheaf
    I.coequifibered_toQuotientAlgebra I.normalConeToQuotient
    I.toNormalConePresheaf_comp_normalConeToQuotient U
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  have hz' : z ∈ Set.range (PrimeSpectrum.comap (I.normalConeToQuotient.app (op U)).hom) :=
    ⟨hsq.isoPullback.inv p, (Scheme.Hom.comp_apply _ _ _).symm.trans
      (congr($(hsq.isoPullback_inv_snd) p).trans hp)⟩
  rw [range_comap_of_surjective _ _ (I.surjective_normalConeToQuotient_app _)] at hz'
  exact hz'

/-- **Blueprint `lemma-normal-cones-contracting-ideals` (1).** If `J = h^* I · 𝒪_{X'}` (on all pairs
of affine opens `U' ⊆ h⁻¹ U`), then the preimage of the zero section of `N_I X` under the morphism
of normal cones `N_J X' ⟶ N_I X` is, set-theoretically, the zero section of `N_J X'`. -/
theorem preimage_range_normalConeZeroSection
    (hJeq : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom = J.siteIdeal U') :
    normalConeMap h I J (fun _ _ hU ↦ (hJeq hU).le) ⁻¹' Set.range I.normalConeZeroSection =
      Set.range J.normalConeZeroSection := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    obtain ⟨q, y, rfl⟩ := (pairsCover h J.coequifibered_toNormalConePresheaf).exists_eq x
    obtain ⟨⟨U', U⟩, hU⟩ := q
    change (colimit.ι (relativeGluingData J.coequifibered_toNormalConePresheaf).functor U' ≫
      normalConeMap h I J _) y ∈ Set.range I.normalConeZeroSection at hx
    rw [normalConeMap, PullbackData.ι_comparison _ _ _ hU, Scheme.Hom.comp_apply] at hx
    have hker := I.ker_le_of_ι_mem_range_normalConeZeroSection U _ hx
    refine J.ι_mem_range_normalConeZeroSection U' y fun b hb ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [RingHom.mem_ker, normalConeToQuotient_app_mk, Ideal.Quotient.eq_zero_iff_mem] at hb
    refine Ideal.mem_of_coeff_zero_mem_of_map_eq (h.appLE U.1 U'.1 hU).hom (J.siteIdeal U')
      (hJeq hU) (y.asIdeal.comap (Ideal.Quotient.mk (J.tIdeal (op U'))))
      ?_ (fun a ha ↦ ?_) hb
    · have h0 : Ideal.Quotient.mk (J.tIdeal (op U')) (J.siteIdeal U').extendedReesAlgebraT = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      exact Ideal.mem_comap.mpr (by convert y.asIdeal.zero_mem)
    · exact hker (RingHom.mem_ker.mpr ((I.normalConeToQuotient_app_mk (op U) a).trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr ha)))
  · rintro _ ⟨w, rfl⟩
    refine ⟨(quotientSpecMap h I J fun _ _ hU ↦ (hJeq hU).le) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← normalConeZeroSection_normalConeMap, Scheme.Hom.comp_apply]

end IdealSheafData

end AlgebraicGeometry.Scheme
