/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Algebra.Homology.ModuleCat.Subcomplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Dualizable complexes of modules are perfect

Let `R` be a commutative ring. A perfect complex of `D(R)` is dualizable for the derived tensor
product (`DerivedCategory.IsPerfect.isDualizable`). This file proves the converse over a
Noetherian ring: a dualizable object of `D(R)` is perfect
(`DerivedCategory.isPerfect_of_isDualizable`). Together, perfectness and dualizability agree
(`DerivedCategory.isPerfect_iff_isDualizable`).

## Strategy

Let `C` be dualizable, with right dual `D`, and represent `C` by a complex `L`.

1. Maps `C ⟶ Z` correspond to maps `𝟙 ⟶ Z ⊗ D`. Represent `D` by a K-flat complex `F` of flat
   modules. A map `𝟙 ⟶ Q(L) ⊗ D = Q(L ⊗ F)` is given by a cocycle `x` of degree `0` of the
   complex `L ⊗ F`, as `𝟙 = R[0]` is K-projective. The element `x` comes from a subcomplex
   `L' ⊗ F` with `L'` a subcomplex of `L` with finitely generated terms, vanishing outside a
   finite interval, and it is a cocycle there since `L' ⊗ F ⟶ L ⊗ F` is injective. Applied to
   the identity of `C`, this shows that `C` is a retract of `Q(L')`
   (`DerivedCategory.exists_retract_of_exactPairing`).
2. Over a Noetherian ring, `C` is then bounded with finitely generated cohomology. So is its dual
   `D`, which is again dualizable. If `C` vanishes above `b` and `D` vanishes above `b'`, then
   `C` has Tor amplitude in `[-b', b]`: maps `Y ⟶ C ⊗ᴸ M` correspond to maps `D ⊗ᴸ Y ⟶ M`.
3. A bounded complex with finitely generated cohomology and finite Tor amplitude is perfect
   (`DerivedCategory.isPerfect_of_finiteTorAmplitude`).

## Main statements

- `DerivedCategory.exists_retract_of_exactPairing`: a dualizable object of `D(R)` is a retract
  of a bounded complex with finitely generated terms.
- `DerivedCategory.isPerfect_of_isDualizable`, `DerivedCategory.isPerfect_iff_isDualizable`
  (`sk-def-perfect`): over a Noetherian ring, the perfect objects of `D(R)` are exactly the
  dualizable ones.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- If `K` and its right dual `L` vanish above `b` and `b'` respectively, then `K` has Tor
amplitude in `[-b', b]`: maps `Y ⟶ K ⊗ᴸ F[0]` correspond to maps `L ⊗ᴸ Y ⟶ F[0]`, which
vanish for `Y` above `-b' - 1`. -/
lemma torAmplitudeIn_of_exactPairing_of_isLE {K L : DerivedCategory C} [ExactPairing K L]
    (b b' : ℤ) [K.IsLE b] [L.IsLE b'] : torAmplitudeIn C (-b') b K := by
  intro F
  refine ⟨(TStructure.t.isGE_iff_orthogonal (-b' - 1) (-b') (by omega) _).2 fun Y f hY ↦ ?_,
    ?_⟩
  · have : Y.IsLE (-b' - 1) := hY
    have := isLE_tensor L Y b' (-b' - 1)
    obtain ⟨g, rfl⟩ := (tensorLeftHomEquiv Y K L ((singleFunctor C 0).obj F)).surjective f
    rw [TStructure.t.zero g (b' + (-b' - 1)) 0 (by omega)]
    simp [tensorLeftHomEquiv]
  · have := isLE_tensor K ((singleFunctor C 0).obj F) b 0
    rwa [add_zero] at this

end General

section ModuleCat

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

variable (R) in
/-- The complex `R[0]`, whose image in `D(R)` is the monoidal unit. -/
noncomputable abbrev unitComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} R))

instance : (unitComplex R).IsKProjective := by
  have (n : ℤ) : Projective ((unitComplex R).X n) := by
    by_cases h : n = 0
    · subst h
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).projective
  exact CochainComplex.isKProjective_of_projective _ 0

/-- The monoidal unit of `D(R)` is the image of `R[0]`. -/
noncomputable def unitIsoQObjUnitComplex :
    𝟙_ (DerivedCategory (ModuleCat.{u} R)) ≅ Q.obj (unitComplex R) :=
  (singleFunctorObjUnitIso _).symm ≪≫ (singleFunctorIsoCompQ _ 0).app _

/-- **A dualizable object is a retract of a finite complex.** Let `C` be an object of `D(R)`
with a right dual `D`, represented by a complex `L`. Then the isomorphism `C ≅ Q(L)` factors
through `Q(L')` for a subcomplex `L'` of `L` with finitely generated terms, vanishing outside a
finite interval.

The coevaluation `𝟙 ⟶ C ⊗ D ≅ Q(L ⊗ F)`, where `F` is a K-flat complex of flat modules
representing `D`, is given by a cocycle of `L ⊗ F` of degree `0`, as `𝟙 = R[0]` is
K-projective. This cocycle comes from `L' ⊗ F` for a finite subcomplex `L'` of `L`, so the
coevaluation factors through `Q(L') ⊗ D`, and the zigzag identity factors `C ≅ Q(L)` through
`Q(L')`. -/
theorem exists_retract_of_exactPairing (C D : DerivedCategory (ModuleCat.{u} R))
    [ExactPairing C D] (L : CochainComplex (ModuleCat.{u} R) ℤ) (e : C ≅ Q.obj L) :
    ∃ (N : L.SubcomplexFamily) (_ : N.IsFinite) (w : C ⟶ Q.obj (CochainComplex.subcomplex N)),
      w ≫ Q.map (CochainComplex.subcomplexι N) = e.hom := by
  obtain ⟨F, π, _, hFflat, hF⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage D)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let eD : Q.obj F ≅ D := asIso (Q.map π) ≪≫ Q.objObjPreimageIso D
  let T (L' : CochainComplex (ModuleCat.{u} R) ℤ) : Q.obj L' ⊗ D ≅ Q.obj (L' ⊗ F) :=
    whiskerLeftIso (Q.obj L') eD.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L' F hF
  have hT {L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ} (f : L₁ ⟶ L₂) :
      Q.map f ▷ D ≫ (T L₂).hom = (T L₁).hom ≫ Q.map (f ▷ F) := by
    simp only [T, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc, ← whisker_exchange_assoc,
      qObjTensorQObjIsoOfKFlatRight_hom_naturality]
  let eU := unitIsoQObjUnitComplex (R := R)
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq (unitComplex R) (L ⊗ F)
    (eU.inv ≫ η_ C D ≫ e.hom ▷ D ≫ (T L).hom)
  let s : (unitComplex R).X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv (1 : R)
  obtain ⟨N, hN, x', hx'⟩ := CochainComplex.exists_mem_range_tensor F 0 (φ.f 0 s)
  let ι := CochainComplex.subcomplexι N
  have hd : (CochainComplex.subcomplex N ⊗ F).d 0 1 x' = 0 := by
    apply CochainComplex.injective_subcomplexι_whiskerRight_f N F hFflat 1
    rw [map_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.Hom.comm, ModuleCat.comp_apply,
      hx', ← ModuleCat.comp_apply, φ.comm]
    simp
  let φ' : unitComplex R ⟶ CochainComplex.subcomplex N ⊗ F :=
    HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x'))
      (by
        rintro k (rfl : 0 + 1 = k)
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (CochainComplex.subcomplex N ⊗ F).d 0 1 (LinearMap.toSpanSingleton R _ x' 1) = 0
        rw [LinearMap.toSpanSingleton_apply, one_smul]
        exact hd)
  have hφ' : φ' ≫ ι ▷ F = φ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv,
      HomologicalComplex.comp_f]
    have hf0 : φ'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x') :=
      HomologicalComplex.mkHomFromSingle_f _ _
    rw [hf0, Category.assoc, Iso.inv_hom_id_assoc]
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul]
    exact hx'
  have hu : (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map ι ▷ D = η_ C D ≫ e.hom ▷ D := by
    rw [← cancel_mono (T L).hom, Category.assoc, Category.assoc, Category.assoc, hT ι,
      Iso.inv_hom_id_assoc, ← Q.map_comp, hφ', hφ, Iso.hom_inv_id_assoc,
      Category.assoc]
  have key : (tensorRightHomEquiv _ C D _).symm (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map ι =
      (λ_ C).hom ≫ e.hom := by
    rw [← tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y' := D), ← hu,
      Equiv.eq_symm_apply, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  exact ⟨N, hN, _, by rw [Category.assoc, key, Iso.inv_hom_id_assoc]⟩

/-- Over a Noetherian ring, an object of `D(R)` with a right dual is bounded and has finitely
generated cohomology: it is a retract of a bounded complex of finitely generated modules. -/
theorem exists_homologyConcentratedIn_and_finite_of_exactPairing [IsNoetherianRing R]
    (C D : DerivedCategory (ModuleCat.{u} R)) [ExactPairing C D] :
    (∃ a b : ℤ, homologyConcentratedIn a b C) ∧
      ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C) := by
  obtain ⟨N, hN, w, hw⟩ :=
    exists_retract_of_exactPairing C D (Q.objPreimage C) (Q.objObjPreimageIso C).symm
  obtain ⟨a, b, hab⟩ := hN.2
  let L' := CochainComplex.subcomplex N
  let r := Q.map (CochainComplex.subcomplexι N) ≫ (Q.objObjPreimageIso C).hom
  have hwr : w ≫ r = 𝟙 C := by simp [r, reassoc_of% hw]
  have : L'.IsStrictlyGE a := CochainComplex.isStrictlyGE_subcomplex fun n hn ↦ hab n (Or.inl hn)
  have : L'.IsStrictlyLE b := CochainComplex.isStrictlyLE_subcomplex fun n hn ↦ hab n (Or.inr hn)
  let H (i : ℤ) := homologyFunctor (ModuleCat.{u} R) i
  let eH (i : ℤ) : (H i).obj (Q.obj L') ≅ L'.homology i := (homologyFunctorFactors _ i).app L'
  have hret (i : ℤ) : (H i).map w ≫ (H i).map r = 𝟙 _ := by
    rw [← Functor.map_comp, hwr, CategoryTheory.Functor.map_id]
  have (i : ℤ) : Mono ((H i).map w) := (IsSplitMono.mk' ⟨_, hret i⟩).mono
  have (i : ℤ) : Epi ((H i).map r) := (IsSplitEpi.mk' ⟨_, hret i⟩).epi
  refine ⟨⟨a, b, ?_, ?_⟩, fun i ↦ ?_⟩
  · change C.IsGE a
    rw [isGE_iff]
    intro i hi
    exact IsZero.of_mono ((H i).map w) ((L'.exactAt_of_isGE a i hi).isZero_homology.of_iso (eH i))
  · change C.IsLE b
    rw [isLE_iff]
    intro i hi
    exact IsZero.of_mono ((H i).map w) ((L'.exactAt_of_isLE b i hi).isZero_homology.of_iso (eH i))
  · have := hN.finite i
    have : Module.Finite R (L'.cycles i) :=
      Module.Finite.of_injective (L'.iCycles i).hom
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
    have : Module.Finite R (L'.homology i) :=
      Module.Finite.of_surjective (L'.homologyπ i).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    have : Module.Finite R ((H i).obj (Q.obj L')) := Module.Finite.equiv (eH i).toLinearEquiv.symm
    exact Module.Finite.of_surjective ((H i).map r).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Blueprint `sk-def-perfect`: a dualizable point complex is perfect.

Over a Noetherian ring `R`, an object `C` of `D(R)` which is dualizable for the derived tensor
product is quasi-isomorphic to a bounded complex of finitely generated projective modules. `C`
and its dual are retracts of bounded complexes of finitely generated modules
(`DerivedCategory.exists_retract_of_exactPairing`), so they are bounded with finitely generated
cohomology, and `C` has finite Tor amplitude
(`DerivedCategory.torAmplitudeIn_of_exactPairing_of_isLE`); such a complex is perfect
(`DerivedCategory.isPerfect_of_finiteTorAmplitude`). -/
theorem isPerfect_of_isDualizable [IsNoetherianRing R] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : IsDualizable C) : C.IsPerfect := by
  obtain ⟨_⟩ := hC
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let := BraidedCategory.exactPairing_swap C Cᘁ
  obtain ⟨⟨a, b, hC₁, hC₂⟩, hfin⟩ := exists_homologyConcentratedIn_and_finite_of_exactPairing C Cᘁ
  obtain ⟨⟨-, b', -, hD₂⟩, -⟩ := exists_homologyConcentratedIn_and_finite_of_exactPairing Cᘁ C
  have : C.IsLE b := hC₂
  have : (Cᘁ).IsLE b' := hD₂
  exact isPerfect_of_finiteTorAmplitude
    ((exists_homologyConcentratedIn_iff_bounded C).1 ⟨a, b, hC₁, hC₂⟩) hfin
    ⟨-b', b, torAmplitudeIn_of_exactPairing_of_isLE (L := Cᘁ) b b'⟩

/-- Blueprint `sk-def-perfect`: perfect point complexes are the dualizable objects.

Over a Noetherian ring `R`, an object of `D(R)` is quasi-isomorphic to a bounded complex of
finitely generated projective modules if and only if it is dualizable for the derived tensor
product. -/
theorem isPerfect_iff_isDualizable [IsNoetherianRing R] (C : DerivedCategory (ModuleCat.{u} R)) :
    C.IsPerfect ↔ IsDualizable C :=
  ⟨IsPerfect.isDualizable, isPerfect_of_isDualizable⟩

end ModuleCat

end DerivedCategory
