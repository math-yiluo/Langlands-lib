/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicField
public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.HigherDirectImage
public import WeilConjectures.SixFunctors.OpenClosed.Supported

/-!
# Acyclicity of the affine line over a discrete valuation ring

For a discrete valuation ring `A` and a finite coefficient ring `Λ` whose exponent is invertible
on `A`, the unit `K ⟶ Rπ_* π^* K` of the projection `π : 𝔸¹_A ⟶ Spec A` is an isomorphism for
every bounded below complex `K` of étale sheaves of `Λ`-modules on `Spec A`
(`AlgebraicGeometry.Etale.affineLineAcyclicAt_of_isDiscreteValuationRing`).

## The argument

More generally, let `j : U ⟶ S` be a quasi-compact open immersion and `i : Z ⟶ S` a closed
immersion with complementary ranges, such that the affine line is acyclic over `U` and over `Z`
(`AlgebraicGeometry.Etale.AffineLineAcyclicAt.of_isOpenImmersion_of_isClosedImmersion`).

* For any `g : S' ⟶ S` along which the derived base change map of `π` is an isomorphism at `M`,
  the unit of `π` is an isomorphism at `Rg_* M` as soon as the unit of the projection of `𝔸¹_{S'}`
  is an isomorphism at `M`
  (`AlgebraicGeometry.Etale.isIso_unit_app_rightDerivedFunctorPlus_obj_of_isIso_baseChange_app`,
  a formal consequence of the mate description of the base change map,
  `CategoryTheory.isIso_unit_app_obj_of_isIso_mateEquiv_app`). The base change map is an
  isomorphism along `j` by smooth base change and along `i` by finite base change.
* Every `G ∈ D⁺(S)` sits in a distinguished triangle `G ⟶ Rj_* j^* G ⟶ C ⟶ G[1]` with
  `j^* C = 0`, since `j^* Rj_* ≅ 𝟭`. The cohomology sheaves of `C` are supported on `Z`, hence
  are pushforwards `i_* F`, and `Ri_*(F[0]) ≅ (i_* F)[0]`. So the unit is an isomorphism at
  `Rj_* j^* G` and at `C`, hence at `G`.

For a discrete valuation ring `A` with fraction field `K` and residue field `k`, the generic point
`Spec K ⟶ Spec A` is an open immersion (`K` is the localization of `A` away from a uniformizer)
and the closed point `Spec k ⟶ Spec A` is a closed immersion with complementary range, and the
affine line is acyclic over the fields `K` and `k`
(`AlgebraicGeometry.Etale.affineLineAcyclicAt_of_field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

/-- The unit of an adjunction `L ⊣ R` is an isomorphism at `X` if and only if `L` is bijective
on morphisms into `X`. -/
lemma CategoryTheory.Adjunction.isIso_unit_app_iff_bijective_map {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : C) :
    IsIso (adj.unit.app X) ↔
      ∀ T : C, Function.Bijective (L.map : (T ⟶ X) → (L.obj T ⟶ L.obj X)) := by
  rw [isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun T ↦ ?_
  rw [← Equiv.comp_bijective L.map (adj.homEquiv T (L.obj X))]
  congr! 1
  ext x
  simp [Adjunction.homEquiv_unit]

/-- Let `β : R₁ ⋙ G ⟶ H ⋙ R₂` be the mate of an isomorphism `α : G ⋙ L₂ ≅ L₁ ⋙ H` with respect
to `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and let `G ⊣ G'`, `H ⊣ H'`. If `β` is an isomorphism at `d` and the
unit of `H ⊣ H'` is an isomorphism at `d`, then the unit of `G ⊣ G'` is an isomorphism at
`R₁ d`. -/
lemma CategoryTheory.isIso_unit_app_obj_of_isIso_mateEquiv_app {C D C' D' : Type*} [Category* C]
    [Category* D] [Category* C'] [Category* D'] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'}
    {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ C'} {G' : C' ⥤ C} {H : D ⥤ D'}
    {H' : D' ⥤ D} (adjG : G ⊣ G') (adjH : H ⊣ H') (α : G ⋙ L₂ ≅ L₁ ⋙ H) (d : D)
    (hβ : IsIso ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).app d))
    (hH : IsIso (adjH.unit.app d)) :
    IsIso (adjG.unit.app (R₁.obj d)) := by
  rw [adjG.isIso_unit_app_iff_bijective_map]
  intro c
  let β := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).app d
  let e : (G.obj c ⟶ G.obj (R₁.obj d)) ≃ (H.obj (L₁.obj c) ⟶ H.obj d) :=
    ((Iso.refl _).homCongr (asIso β)).trans
      ((adj₂.homEquiv _ _).symm.trans ((α.app c).homCongr (Iso.refl _)))
  have key : e ∘ G.map = H.map ∘ (adj₁.homEquiv c d).symm := by
    ext x
    have h₁ : L₂.map β ≫ adj₂.counit.app (H.obj d) =
        α.hom.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) :=
      mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom) d
    have h₂ := α.hom.naturality x
    dsimp at h₂
    have h : α.inv.app c ≫ L₂.map (G.map x) ≫ L₂.map β ≫ adj₂.counit.app (H.obj d) =
        H.map ((adj₁.homEquiv c d).symm x) := by
      rw [h₁, reassoc_of% h₂, Iso.inv_hom_id_app_assoc, Adjunction.homEquiv_counit,
        Functor.map_comp]
    simpa [e, Adjunction.homEquiv_counit] using h
  rw [← Equiv.comp_bijective _ e, key, Equiv.bijective_comp]
  exact (adjH.isIso_unit_app_iff_bijective_map d).1 hH _

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The unit at a direct image.** For a commutative square `g' ≫ f = f' ≫ g`, if the derived
base change map `g^* Rf_* M ⟶ Rf'_* g'^* M` is an isomorphism and the unit of `g'` is an
isomorphism at `M`, then the unit `Rf_* M ⟶ Rg_* g^* Rf_* M` of `g` is an isomorphism. -/
theorem isIso_unit_app_rightDerivedFunctorPlus_obj_of_isIso_baseChange_app
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hBC : IsIso ((baseChange (ModuleCat.{u + 1} Λ) sq).app M))
    (hM : IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g').unit.app M)) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).unit.app
      (R+((f)_*[ModuleCat.{u + 1} Λ]).obj M)) := by
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at hM ⊢
  rw [baseChange_app_eq_mateEquiv] at hBC
  exact isIso_unit_app_obj_of_isIso_mateEquiv_app _ _ _ _
    (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq) M hBC hM

/-- If the affine line over `Z` is acyclic, then for a finite morphism `f : Z ⟶ S` the unit of
the projection `π : 𝔸¹_S ⟶ S` is an isomorphism at every `Rf_* M`: the base change map along
`f` is an isomorphism by finite base change. -/
theorem isIso_unit_app_rightDerivedFunctorPlus_obj_of_isFinite {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFinite f] (hZ : AffineLineAcyclicAt Λ Z)
    (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app (R+((f)_*[ModuleCat.{u + 1} Λ]).obj M)) := by
  have sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) f).flip
  refine isIso_unit_app_rightDerivedFunctorPlus_obj_of_isIso_baseChange_app Λ sq.toCommSq M ?_
    (hZ M)
  have := (inferInstance : IsBaseChangeIso (ModuleCat.{u + 1} Λ) f).isIso _ _ _ sq
  rw [baseChange_eq_derivedBaseChangeMapPlus]
  infer_instance

/-- If the affine line over `U` is acyclic and the exponent of `Λ` is invertible on `S`, then for
a quasi-compact and quasi-separated `f : U ⟶ S` the unit of the projection `π : 𝔸¹_S ⟶ S` is an
isomorphism at every `Rf_* M`: the base change map along the smooth `π` is an isomorphism by
smooth base change. -/
theorem isIso_unit_app_rightDerivedFunctorPlus_obj_of_qcqs {U S : Scheme.{u}} (f : U ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [HasInvertibleExponent Λ S]
    (hU : AffineLineAcyclicAt Λ U)
    (M : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app (R+((f)_*[ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  have : Smooth (𝔸(ULift.{u} (Fin 1); S) ↘ S) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin 1))) _
  have sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) f).flip
  refine isIso_unit_app_rightDerivedFunctorPlus_obj_of_isIso_baseChange_app Λ sq.toCommSq M ?_
    (hU M)
  exact isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ _ sq M fun _ ↦
    IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu _

/-- For an open immersion `j`, the restriction `j^* G ⟶ j^* Rj_* j^* G` of the unit of
`j^* ⊣ Rj_*` is an isomorphism, the counit `j^* Rj_* ⟶ 𝟭` being one. -/
lemma isIso_upperStar_map_unit_app_of_isOpenImmersion {U S : Scheme.{u}} (j : U ⟶ S)
    [IsOpenImmersion j]
    (G : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D+((j)^*[ModuleCat.{u + 1} Λ]).map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).unit.app G)) := by
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus, IsIso.eq_inv_of_inv_hom_id
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.left_triangle_components
      G)]
  infer_instance

/-- Let `j : U ⟶ S` and `i : Z ⟶ S` be an open and a closed immersion with complementary ranges.
If the affine line over `Z` is acyclic, the unit of the projection `π : 𝔸¹_S ⟶ S` is an
isomorphism at every `C ∈ D⁺(S)` with `j^* C = 0`: the cohomology sheaves of `C` are of the form
`i_* F`, and `i_* F` placed in degree `0` is `Ri_*(F[0])`. -/
theorem isIso_unit_app_of_isZero_upperStar {U Z S : Scheme.{u}} (j : U ⟶ S) (i : Z ⟶ S)
    [IsOpenImmersion j] [IsClosedImmersion i] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hZ : AffineLineAcyclicAt Λ Z)
    (C : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : IsZero (D+((j)^*[ModuleCat.{u + 1} Λ]).obj C)) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app C) := by
  let P : ObjectProperty (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := fun F ↦
    IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj F)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ IsZero.of_iso h ((j)^*[ModuleCat.{u + 1} Λ].mapIso e.symm)⟩
  refine DerivedCategory.Plus.isIso_app_of_forall_homology _ P (fun F hF ↦ ?_)
    (fun K n _ q hq ↦ DerivedCategory.Plus.isZero_homology_of_isGE K n q hq)
    (fun K n _ q hq ↦ isZero_homologyFunctor_upperStar_lowerStar_obj Λ _ K n q hq) C
    (fun q ↦ IsZero.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).map_isZero hC)
      ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app C))
  obtain ⟨L, ⟨e⟩⟩ := mem_essImage_lowerStar_of_isZero_upperStar i hij hF
  exact (NatTrans.isIso_app_iff_of_iso _ (rightDerivedFunctorPlusLowerStarSingleIso Λ i L ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso e)).1
      (isIso_unit_app_rightDerivedFunctorPlus_obj_of_isFinite Λ i hZ _)

/-- **Acyclicity of the affine line glues along an open–closed decomposition.** Let
`j : U ⟶ S` be a quasi-compact open immersion and `i : Z ⟶ S` a closed immersion with
complementary ranges, and let the exponent of `Λ` be invertible on `S`. If the affine line is
acyclic over `U` and over `Z`, it is acyclic over `S`.

Every `G ∈ D⁺(S)` sits in a distinguished triangle `G ⟶ Rj_* j^* G ⟶ C ⟶ G[1]` with
`j^* C = 0`; the unit is an isomorphism at `Rj_* j^* G` by smooth base change
(`AlgebraicGeometry.Etale.isIso_unit_app_rightDerivedFunctorPlus_obj_of_qcqs`) and at `C` by
finite base change (`AlgebraicGeometry.Etale.isIso_unit_app_of_isZero_upperStar`). -/
theorem AffineLineAcyclicAt.of_isOpenImmersion_of_isClosedImmersion {U Z S : Scheme.{u}}
    (j : U ⟶ S) (i : Z ⟶ S) [IsOpenImmersion j] [QuasiCompact j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) [HasInvertibleExponent Λ S]
    (hU : AffineLineAcyclicAt Λ U) (hZ : AffineLineAcyclicAt Λ Z) : AffineLineAcyclicAt Λ S := by
  intro G
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).unit.app G)
  have hC : IsZero (D+((j)^*[ModuleCat.{u + 1} Λ]).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ (D+((j)^*[ModuleCat.{u + 1} Λ]).map_distinguished _ hT)).2
      (isIso_upperStar_map_unit_app_of_isOpenImmersion Λ j G)
  exact NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃ _ hT
    (isIso_unit_app_rightDerivedFunctorPlus_obj_of_qcqs Λ j hU _)
    (isIso_unit_app_of_isZero_upperStar Λ j i hij hZ C hC)

/-- For a discrete valuation ring `A`, the generic point `Spec K ⟶ Spec A` and the closed point
`Spec k ⟶ Spec A` have complementary ranges. -/
lemma range_specMap_residue_eq_compl (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))).base =
      (Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))).base)ᶜ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hr {B : Type u} [CommRing B] (f : A →+* B) (p : PrimeSpectrum A) :
      p ∈ Set.range (Spec.map (CommRingCat.ofHom f)).base ↔
        p ∈ Set.range (PrimeSpectrum.comap f) := Iff.rfl
  ext p
  rw [Set.mem_compl_iff, hr, hr, PrimeSpectrum.localization_comap_range (FractionRing A)
    (nonZeroDivisors A), IsLocalRing.ResidueField.algebraMap_eq,
    range_comap_of_surjective _ _ IsLocalRing.residue_surjective, IsLocalRing.ker_residue,
    Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  refine ⟨fun h hd ↦ ?_, fun h ↦ ?_⟩
  · exact Set.disjoint_left.1 hd (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
      (h ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit))
  · have hp : p.asIdeal ≠ ⊥ := by
      rintro hp
      refine h (Set.disjoint_left.2 fun x hx hx0 ↦ nonZeroDivisors.ne_zero hx ?_)
      simpa [hp] using hx0
    rw [IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hp)]

/-- **Acyclicity of the affine line over a discrete valuation ring**: for a discrete valuation
ring `A` and a finite coefficient ring `Λ` whose exponent is invertible on `A`, the unit
`K ⟶ Rπ_* π^* K` of `π : 𝔸¹_A ⟶ Spec A` is an isomorphism for every `K ∈ D⁺(A_ét, Λ)`. -/
theorem affineLineAcyclicAt_of_isDiscreteValuationRing [Finite Λ] (A : Type u) [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [HasInvertibleExponent Λ (Spec (.of A))] :
    AffineLineAcyclicAt Λ (Spec (.of A)) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  let i := Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have : IsLocalization.Away ϖ (FractionRing A) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors A)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun x hx ↦ ?_).2 inferInstance
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hx) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, Units.mul_left_dvd.2 dvd_rfl⟩
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization ϖ
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : HasInvertibleExponent Λ (Spec (.of (FractionRing A))) := .of_hom j
  have : HasInvertibleExponent Λ (Spec (.of (IsLocalRing.ResidueField A))) := .of_hom i
  exact AffineLineAcyclicAt.of_isOpenImmersion_of_isClosedImmersion Λ j i
    (range_specMap_residue_eq_compl A) (affineLineAcyclicAt_of_field Λ _)
    (affineLineAcyclicAt_of_field Λ _)

end Etale

end AlgebraicGeometry
