/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFreeSheafDerivedSections
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!
# Kummer computations on the affine line and `𝔾_m` over an algebraically closed field

For an algebraically closed field `k` and a finite coefficient ring `Λ` whose exponent is
invertible in `k`, we compute the étale cohomology `Hᵠ(X, Λ)` (in the derived category of étale
sheaves of `Λ`-modules) of `X = 𝔸¹_k` and of `X = 𝔾_{m,k}`, the complement of the zero section.

The comparison with the cohomology `Sheaf.H` of the underlying abelian sheaves
(`AlgebraicGeometry.Etale.nonempty_cohomology_singleFunctor_iso_sheafH`) reduces everything to
the abelian computations of `WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Étale cohomology of a sheaf of `Λ`-modules vanishes in negative degrees. -/
theorem isZero_cohomology_singleFunctor_of_neg (Z : Scheme.{u})
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q < 0) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) Z q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let Γ := Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  refine IsZero.of_iso (Γ.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 hq) ?_
  exact (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
    Γ.rightDerivedFunctorPlusCompatibility.symm) (DerivedCategory.homologyFunctor _ q)).app F

/-- On a quasi-compact quasi-separated scheme, the étale cohomology of a sheaf of `Λ`-modules is,
as an abelian group, the cohomology `Sheaf.H` of its underlying abelian sheaf. -/
theorem nonempty_cohomology_singleFunctor_iso_sheafH (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((cohomology (ModuleCat.{u + 1} Λ) Z q).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      AddCommGrpCat.of (Sheaf.H ((forget₂Sheaf Λ Z).obj F) q)) := by
  obtain ⟨e⟩ := Scheme.nonempty_freeSheafDerivedSectionsIso Z Λ q
  exact ⟨(e.app F).symm ≪≫ (shiftedHomFunctorFreeSheafIso Λ Z q).app F⟩

theorem isZero_cohomology_singleFunctor_iff (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) Z q).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) ↔
      Subsingleton (Sheaf.H ((forget₂Sheaf Λ Z).obj F) q) := by
  obtain ⟨e⟩ := nonempty_cohomology_singleFunctor_iso_sheafH Λ Z F q
  rw [ModuleCat.isZero_iff_subsingleton]
  exact e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr

/-- The constant complex `Λ_X` is the constant sheaf `Λ` placed in degree zero. -/
noncomputable def constantComplexIsoSingleFunctorConstantSheaf (X : Scheme.{u}) :
    constantComplex Λ X ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso (presheafToSheaf _ _))

/-- The underlying abelian sheaf of the constant sheaf `Λ` is the constant sheaf on the
underlying abelian group of `Λ`. -/
noncomputable def forget₂SheafConstantSheafIso (X : Scheme.{u}) :
    (forget₂Sheaf Λ X).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (ModuleCat.of Λ Λ)) :=
  (constantSheafSheafComposeForget₂Iso Λ).app _

/-- `Hᵠ(X, Λ)` vanishes as soon as `Hᵠ` of the underlying constant abelian sheaf does. -/
lemma isZero_cohomology_constantComplex_of_subsingleton (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ)
    (h : Subsingleton (Sheaf.H ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (ModuleCat.of Λ Λ))) q)) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj (constantComplex Λ X)) := by
  refine IsZero.of_iso ?_ ((cohomology (ModuleCat.{u + 1} Λ) X q).mapIso
    (constantComplexIsoSingleFunctorConstantSheaf Λ X))
  rw [isZero_cohomology_singleFunctor_iff]
  exact @Equiv.subsingleton _ _
    ((Sheaf.functorH _ q).mapIso
      (forget₂SheafConstantSheafIso Λ X)).addCommGroupIsoToAddEquiv.toEquiv h

section Field

variable {k : Type u} [Field k] [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))]

omit [Finite Λ] in
variable (k) in
lemma exists_natCast_ne_zero_nsmul_eq_zero :
    ∃ n : ℕ, (n : k) ≠ 0 ∧ ∀ a : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (ModuleCat.of Λ Λ), n • a = 0 := by
  obtain ⟨n, -, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of k))
  refine ⟨n, fun h ↦ ?_, fun a ↦ ?_⟩
  · have := hu.map (Scheme.ΓSpecIso (.of k)).hom.hom
    rw [map_natCast, h] at this
    exact not_isUnit_zero this
  · rw [nsmul_eq_mul, hΛ, zero_mul]

instance : Finite ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
    (ModuleCat.of Λ Λ)) :=
  inferInstanceAs (Finite Λ)

variable [IsAlgClosed k]

/-- **The affine line is acyclic** (blueprint `thm-pur-kummer-affine-line` (1)):
`Hᵠ(𝔸¹_k, Λ) = 0` for `q ≠ 0`, for `k` algebraically closed and `Λ` finite with invertible
exponent. -/
theorem isZero_cohomology_affineLine (q : ℤ) (hq : q ≠ 0) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))) := by
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact IsZero.of_iso (isZero_cohomology_singleFunctor_of_neg Λ _ _ hq)
      ((cohomology _ _ q).mapIso (constantComplexIsoSingleFunctorConstantSheaf Λ _))
  · obtain ⟨n, hn, hA⟩ := exists_natCast_ne_zero_nsmul_eq_zero Λ k
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
    exact isZero_cohomology_constantComplex_of_subsingleton Λ _ q
      (AffineSpace.subsingleton_sheafH_constantSheaf_line _ hn hA q (by exact_mod_cast hq))

omit [Finite Λ] in
/-- **Cohomological dimension of `𝔾_{m,k}`** (blueprint `thm-pur-kummer-affine-line` (2)):
`Hᵠ(𝔾_{m,k}, Λ) = 0` for `q ∉ {0, 1}`. -/
theorem isZero_cohomology_multiplicativeGroup {G : Scheme.{u}}
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
      (Spec (.of k))).base)ᶜ) (q : ℤ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) G q).obj (constantComplex Λ G)) := by
  have := AffineSpace.isAffine_of_range_eq_compl_zeroSection j hj
  rcases lt_or_gt_of_ne hq0 with hq | hq
  · exact IsZero.of_iso (isZero_cohomology_singleFunctor_of_neg Λ _ _ hq)
      ((cohomology _ _ q).mapIso (constantComplexIsoSingleFunctorConstantSheaf Λ _))
  · obtain ⟨n, hn, hA⟩ := exists_natCast_ne_zero_nsmul_eq_zero Λ k
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
    refine isZero_cohomology_constantComplex_of_subsingleton Λ _ q
      (AffineSpace.subsingleton_sheafH_constantSheaf_multiplicativeGroup j hj _
        (AffineSpace.pos_of_natCast_ne_zero hn) ?_ q (by omega))
    ext a
    simpa using hA a

end Field


/-- The constant sheaf functor to sheaves of `Λ`-modules on a nonempty scheme is faithful on
`Λ`: a scalar endomorphism of `Λ` whose constant sheaf is zero is zero. -/
lemma eq_zero_of_constantSheaf_map_eq_zero {X : Scheme.{u}} [Nonempty X]
    {M N : ModuleCat.{u + 1} Λ} (g : M ⟶ N)
    (h : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g = 0) : g = 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := (X.uliftPointSmallEtale x).sheafFiber_map_constantSheaf_map (A := ModuleCat.{u + 1} Λ) g
  rw [h, Functor.map_zero] at this
  have h' := congrArg (fun φ ↦ ((X.uliftPointSmallEtale x).sheafFiberConstantSheafIso M).inv ≫
    φ ≫ ((X.uliftPointSmallEtale x).sheafFiberConstantSheafIso N).hom) this
  simp only [zero_comp, comp_zero, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at h'
  exact h'.symm

variable [Finite Λ]

/-- **Global sections of the constant sheaf `Λ` on a connected scheme**: the unit
`Λ ⟶ Γ(X, Λ_X)` is bijective. It is injective since the constant sheaf functor is faithful, and
both sides have the same finite cardinality by the corresponding statement for abelian groups
(`AlgebraicGeometry.Scheme.bijective_toSheafify_app_terminal`). -/
theorem bijective_constantSheafΓAdj_unit_app (X : Scheme.{u}) [ConnectedSpace X] :
    Function.Bijective ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app
      (ModuleCat.of Λ Λ)) := by
  have : Nonempty X := ConnectedSpace.toNonempty
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let ρ := adj.unit.app (ModuleCat.of Λ Λ)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    let g : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ := (show Λ from c) • 𝟙 (ModuleCat.of Λ Λ)
    have h1 : adj.homEquiv _ _ ((constantSheaf _ _).map g) = 0 := by
      rw [Adjunction.homEquiv_unit]
      have := adj.unit.naturality g
      dsimp at this
      rw [← this]
      refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
      change ρ ((show Λ from c) • a) = 0
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hc, smul_zero]
    have h2 : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g = 0 := by
      apply (adj.homEquiv _ _).injective
      rw [h1, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have h3 := eq_zero_of_constantSheaf_map_eq_zero Λ (X := X) g h2
    simpa [g] using congrArg (fun φ : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ ↦ φ (1 : Λ)) h3
  let T := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let A := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (ModuleCat.of Λ Λ)
  let E : _ ≃ A :=
    ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))).toLinearEquiv.toEquiv.trans
    ((((sheafToPresheaf _ _).mapIso (forget₂SheafConstantSheafIso Λ X)).app
      (Opposite.op T)).addCommGroupIsoToAddEquiv.toEquiv.trans
    (Equiv.ofBijective _ (Scheme.bijective_toSheafify_app_terminal X A)).symm)
  have : Finite ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) :=
    Finite.of_equiv _ E.symm
  exact hinj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr E))

omit [Finite Λ] in
/-- The étale cohomology `Hᵠ(X, F)`, `q ∈ ℕ`, of a sheaf placed in degree zero is the `q`-th right
derived functor of the global sections. -/
noncomputable def cohomologySingleFunctorIsoRightDerived (X : Scheme.{u}) (q : ℕ) :
    DerivedCategory.singleFunctor _ 0 ⋙ cohomology (ModuleCat.{u + 1} Λ) X (q : ℤ) ≅
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        (Sheaf.Γ X.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ)) ≪≫
    (Sheaf.Γ X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

/-- **`H⁰(X, Λ) = Λ` for a connected scheme `X`.** -/
noncomputable def cohomologyZeroConstantComplexIso (X : Scheme.{u}) [ConnectedSpace X] :
    (cohomology (ModuleCat.{u + 1} Λ) X 0).obj (constantComplex Λ X) ≅ ModuleCat.of Λ Λ :=
  have := (ConcreteCategory.isIso_iff_bijective _).2 (bijective_constantSheafΓAdj_unit_app Λ X)
  (cohomology (ModuleCat.{u + 1} Λ) X 0).mapIso
      (constantComplexIsoSingleFunctorConstantSheaf Λ X) ≪≫
    (cohomologySingleFunctorIsoRightDerived Λ X 0).app _ ≪≫
    (Functor.rightDerivedZeroIsoSelf _).app _ ≪≫
    (asIso ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app
      (ModuleCat.of Λ Λ))).symm

section Field

variable {k : Type u} [Field k]

instance connectedSpace_affineLine : ConnectedSpace 𝔸(ULift.{u} (Fin 1); Spec (.of k)) := by
  have : Nonempty 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
    ⟨(AffineSpace.zeroSection _ _).base (Classical.arbitrary (Spec (.of k)))⟩
  have := isIntegral_of_isAffine_of_isDomain 𝔸(ULift.{u} (Fin 1); Spec (.of k))
  infer_instance

lemma connectedSpace_of_range_eq_compl_zeroSection {G : Scheme.{u}}
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
      (Spec (.of k))).base)ᶜ) : ConnectedSpace G := by
  have := AffineSpace.isAffine_of_range_eq_compl_zeroSection j hj
  have := AffineSpace.isDomain_of_range_eq_compl_zeroSection j hj
  obtain ⟨g, -⟩ : (AffineSpace.oneSection (ULift.{u} (Fin 1)) (Spec (.of k))).base
      (Classical.arbitrary (Spec (.of k))) ∈ Set.range j.base := by
    rw [hj]
    exact AffineSpace.oneSection_apply_notMem_range_zeroSection _ _ _
  have : Nonempty G := ⟨g⟩
  have := isIntegral_of_isAffine_of_isDomain G
  infer_instance

/-- Blueprint `thm-pur-kummer-affine-line` (1), degree zero: `H⁰(𝔸¹_k, Λ) = Λ`. -/
theorem nonempty_iso_cohomology_zero_affineLine :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) ≅ ModuleCat.of Λ Λ) :=
  ⟨cohomologyZeroConstantComplexIso Λ _⟩

/-- Blueprint `thm-pur-kummer-affine-line` (2), degree zero: `H⁰(𝔾_{m,k}, Λ) = Λ`. -/
theorem nonempty_iso_cohomology_zero_multiplicativeGroup {G : Scheme.{u}}
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
      (Spec (.of k))).base)ᶜ) :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G 0).obj (constantComplex Λ G) ≅
      ModuleCat.of Λ Λ) :=
  have := connectedSpace_of_range_eq_compl_zeroSection j hj
  ⟨cohomologyZeroConstantComplexIso Λ _⟩

end Field

end AlgebraicGeometry.Etale
