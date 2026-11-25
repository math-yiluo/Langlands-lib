/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicField
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalHigher

/-!
# Acyclicity of the affine line over strictly henselian local rings, by base change

Let `R` be a strictly henselian local ring and `Λ` a finite coefficient ring whose exponent is
invertible on `R`. Suppose given a ring `A`, a ring homomorphism `A ⟶ R` and an integer
killing `Λ` which is invertible in `A`, such that the affine line over `Spec A` is acyclic
(`AlgebraicGeometry.Etale.AffineLineAcyclicAt`). Then for every sheaf `M` of `Λ`-modules on
`Spec R`, `Hᵠ(𝔸¹_R, p_R^* M) = 0` for `q > 0`
(`AlgebraicGeometry.Etale.subsingleton_sheafH_affineLine_of_affineLineAcyclicAt`).

Such an `A` is `ℚ` or a localization `ℤ_(p)`; the first is a field
(`AlgebraicGeometry.Etale.affineLineAcyclicAt_of_field`), the second a discrete valuation ring.
Given the acyclicity of the affine line over discrete valuation rings, this proves the
strictly henselian case of the acyclicity of the affine line
(`AlgebraicGeometry.Etale.subsingleton_sheafH_affineLine_of_isStrictlyHenselianLocalRing` and
`bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_affineLineAcyclicAt`).

## The argument

Write `g : Spec R ⟶ Spec A`, `π_A : 𝔸¹_A ⟶ Spec A`, `π_R : 𝔸¹_R ⟶ Spec R` and
`h : 𝔸¹_R ⟶ 𝔸¹_A`. The Leray isomorphisms, smooth base change `π_A^* Rg_* K ≅ Rh_* π_R^* K`
and the acyclicity `Rg_* K ≅ Rπ_{A*} π_A^* Rg_* K` give
`RΓ(𝔸¹_R, π_R^* K) ≅ RΓ(𝔸¹_A, π_A^* Rg_* K) ≅ RΓ(Spec A, Rg_* K) ≅ RΓ(Spec R, K)`
(`AlgebraicGeometry.Etale.rightDerivedGlobalSectionsUpperStarIso`), and the global sections
functor of the strictly local scheme `Spec R` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Derived global sections through a base change square.** For a commutative square
`e ≫ g = h ≫ p` (with `e : Y ⟶ T`, `h : Y ⟶ X`, `g : T ⟶ S`, `p : X ⟶ S`) and a bounded below
complex `K` on `T` such that the base change map `p^* Rg_* K ⟶ Rh_* e^* K` and the unit
`Rg_* K ⟶ Rp_* p^* Rg_* K` are isomorphisms, `RΓ(Y, e^* K) ≅ RΓ(T, K)`. -/
noncomputable def rightDerivedGlobalSectionsUpperStarIso {X S T Y : Scheme.{u}}
    {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : CommSq e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((baseChange (ModuleCat.{u + 1} Λ) sq).app K)]
    [IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p).unit.app
      (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K))] :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
        (DerivedCategory.Plus.ι.obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj (DerivedCategory.Plus.ι.obj K) :=
  ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ h).app _).symm ≪≫
    (rightDerivedGlobalSections _ X).mapIso
      ((((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _).symm ≪≫
        DerivedCategory.Plus.ι.mapIso (asIso ((baseChange _ sq).app K)).symm) ≪≫
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ p).app _).symm ≪≫
    (rightDerivedGlobalSections _ S).mapIso
      ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _).symm ≪≫
        DerivedCategory.Plus.ι.mapIso
          (asIso ((derivedUpperStarLowerStarAdjunctionPlus _ p).unit.app _)).symm ≪≫
        ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ g).app _

/-- Over a strictly local scheme `T ≅ Spec R`, the derived global sections of a sheaf placed
in degree `0` have no cohomology in positive degrees: the global sections functor is exact. -/
lemma isZero_homology_rightDerivedGlobalSections_singleFunctor_of_isStrictlyHenselianLocalRing
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R] {T : Scheme.{u}}
    (e : T ≅ Spec (.of R)) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have := preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (Λ := Λ) e
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    ((Sheaf.Γ T.smallEtaleTopology _).rightDerivedFunctorIsoMapDerivedCategory.app _) ≪≫
    (((Sheaf.Γ T.smallEtaleTopology _).mapDerivedCategoryHomologyFunctorIso q).app _).symm)
  exact (Sheaf.Γ T.smallEtaleTopology _).map_isZero
    (DerivedCategory.Plus.isZero_homology_of_isLE ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
      0 q hq)

/-- **Positive-degree acyclicity of the affine line over a strictly henselian local ring, by
base change.** Let `R` be a strictly henselian local ring, `φ : A ⟶ R` a ring homomorphism such
that the affine line over `Spec A` is acyclic, and `N ≠ 0` an integer killing `Λ` which is
invertible in `A`. Then `Hᵠ(𝔸¹_R, p_R^* M) = 0` for every sheaf `M` of `Λ`-modules on `Spec R`
and `q > 0`. -/
theorem subsingleton_sheafH_affineLine_of_affineLineAcyclicAt {R A : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] [CommRing A] (φ : A →+* R) (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNA : IsUnit (N : A)) (hA : AffineLineAcyclicAt Λ (Spec (.of A)))
    (M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).flip
  have : Smooth (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A)) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin 1))) _
  have hNS : IsUnit (N : Γ(Spec (.of A), ⊤)) := by
    simpa using hNA.map (Scheme.ΓSpecIso (.of A)).inv.hom
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj M
  have := Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ _ sq K
    fun _ ↦ IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNS _
  have := hA (R+((g)_*[ModuleCat.{u + 1} Λ]).obj K)
  refine (isZero_cohomology_singleFunctor_iff_subsingleton_H Λ _ _ q).1 ?_
  exact (isZero_homology_rightDerivedGlobalSections_singleFunctor_of_isStrictlyHenselianLocalRing
    Λ (Iso.refl _) M q (by omega)).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedGlobalSections _ _).mapIso (DerivedCategory.Plus.ι.mapIso
        ((((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ]
          ).mapDerivedCategoryPlusSingleFunctor 0).app M).symm) ≪≫
        rightDerivedGlobalSectionsUpperStarIso Λ sq.toCommSq K))

/-- The exponent of `Λ` is invertible on `Spec A` as soon as some positive integer killing `Λ`
is a unit in `A`. -/
lemma hasInvertibleExponent_spec_of_isUnit {A : Type u} [CommRing A] (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNA : IsUnit (N : A)) : HasInvertibleExponent Λ (Spec (.of A)) :=
  ⟨N, Nat.pos_of_ne_zero hN₀, hN, by simpa using hNA.map (Scheme.ΓSpecIso (.of A)).inv.hom⟩

/-- **The affine line over a strictly henselian local ring has no cohomology in positive
degrees**, given the acyclicity of the affine line over discrete valuation rings. Let `R` be a
strictly henselian local ring on which the exponent of `Λ` is invertible and `M` a sheaf of
`Λ`-modules on `Spec R`. Then `Hᵠ(𝔸¹_R, p_R^* M) = 0` for `q > 0`.

Let `P ⊆ ℤ` be the preimage of the maximal ideal of `R`; the integers outside `P` are units in
`R`, so that `R` is an algebra over `A = ℤ_P`, in which the exponent `N` of `Λ` is invertible.
If `P = 0`, `A = ℚ` is a field (`AlgebraicGeometry.Etale.affineLineAcyclicAt_of_field`);
otherwise `A` is a discrete valuation ring (the hypothesis `hDVR`). Conclude by
`AlgebraicGeometry.Etale.subsingleton_sheafH_affineLine_of_affineLineAcyclicAt`. -/
theorem subsingleton_sheafH_affineLine_of_isStrictlyHenselianLocalRing [Finite Λ]
    (hDVR : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [HasInvertibleExponent Λ (Spec (.of A))], AffineLineAcyclicAt Λ (Spec (.of A)))
    {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    [HasInvertibleExponent Λ (Spec (.of R))]
    (M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  obtain ⟨N, hNpos, hN, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of R))
  have hN₀ := hNpos.ne'
  have hNR : IsUnit (N : R) := by
    simpa using hu.map (Scheme.ΓSpecIso (.of R)).hom.hom
  let P := (IsLocalRing.maximalIdeal R).comap (Int.castRingHom R)
  have hP (y : ℤ) (hy : y ∉ P) : IsUnit (Int.castRingHom R y) :=
    IsLocalRing.notMem_maximalIdeal.1 hy
  have hNP : (N : ℤ) ∉ P := IsLocalRing.notMem_maximalIdeal.2 (by simpa using hNR)
  by_cases hP0 : P = ⊥
  · let ψ : ℚ →+* R := IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom R)
      fun y ↦ hP y fun h ↦ nonZeroDivisors.coe_ne_zero y (by rwa [hP0, Ideal.mem_bot] at h)
    have hNA : IsUnit (N : ULift.{u} ℚ) := by
      simpa using (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hN₀ : (N : ℚ) ≠ 0)).map
        (ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ)
    have := hasInvertibleExponent_spec_of_isUnit Λ N hN₀ hN hNA
    exact subsingleton_sheafH_affineLine_of_affineLineAcyclicAt Λ
      (ψ.comp ULift.ringEquiv.toRingHom) N hN₀ hN hNA (affineLineAcyclicAt_of_field Λ _) M q hq
  · let ψ : Localization.AtPrime P →+* R :=
      IsLocalization.lift (M := P.primeCompl) (g := Int.castRingHom R) fun y ↦ hP y y.2
    have : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hP0 _
    have : IsDomain (ULift.{u} (Localization.AtPrime P)) :=
      MulEquiv.isDomain (Localization.AtPrime P) ULift.ringEquiv.toMulEquiv
    have : IsDiscreteValuationRing (ULift.{u} (Localization.AtPrime P)) :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
        (ULift.ringEquiv.symm : Localization.AtPrime P ≃+* ULift.{u} (Localization.AtPrime P))
    have hNA : IsUnit (N : ULift.{u} (Localization.AtPrime P)) := by
      simpa using (IsLocalization.map_units (Localization.AtPrime P)
        (⟨N, hNP⟩ : P.primeCompl)).map
        (ULift.ringEquiv.symm : Localization.AtPrime P ≃+* ULift.{u} (Localization.AtPrime P))
    have := hasInvertibleExponent_spec_of_isUnit Λ N hN₀ hN hNA
    exact subsingleton_sheafH_affineLine_of_affineLineAcyclicAt Λ
      (ψ.comp ULift.ringEquiv.toRingHom) N hN₀ hN hNA (hDVR _) M q hq

/-- **Acyclicity of the affine line over strictly henselian local rings, in the form of
invariance under local homomorphisms**, given the acyclicity of the affine line over discrete
valuation rings (`hDVR`): for a homomorphism `φ : A ⟶ B` of strictly henselian local rings
and `M` locally constant on `Spec A`, the pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` is bijective for every `q`. -/
theorem bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_affineLineAcyclicAt
    [Finite Λ]
    (hDVR : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [HasInvertibleExponent Λ (Spec (.of A))], AffineLineAcyclicAt Λ (Spec (.of A)))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B)
    [HasInvertibleExponent Λ (Spec (.of A))]
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ) :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) q) :=
  bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_subsingleton Λ
    (fun R _ _ _ _ L _ q hq ↦
      have : IsStrictlyHenselianLocalRing R := { isSepClosed_residueField := inferInstance }
      subsingleton_sheafH_affineLine_of_isStrictlyHenselianLocalRing Λ hDVR L q hq) φ M q

end Etale

end AlgebraicGeometry
