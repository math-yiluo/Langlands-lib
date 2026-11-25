/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleSliceOrigin
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSiteBoundedConstantModels
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink

/-! # Bounded constant models from finite etale-local cohomology

Source: Stacks Project, Tags 09AL and 094G
(blueprint: lem-weil-pbc-finite-coefficient-etale-bounded-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Conjugate every differential by a small-carrier linear equivalence. -/
private theorem small_finite_complex (R : Type t) [CommRing R]
    (M : CochainComplex (ModuleCat.{t + 1} (ULift.{t + 1} R)) ℤ)
    (a b : ℤ) (hz : ∀ i : ℤ, i < a ∨ b < i → IsZero (M.X i))
    (ht : ∀ i : ℤ, Module.Finite (ULift.{t + 1} R) (M.X i)) :
    ∃ P : CochainComplex (ModuleCat.{t} R) ℤ,
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Finite R (P.X i)) ∧ Nonempty
        (((ModuleCat.uliftFunctor.{t + 1, t} R ⋙
          ModuleCat.restrictScalars.{t + 1}
            (ULift.ringEquiv : ULift.{t + 1} R ≃+* R).toRingHom
          ).mapHomologicalComplex (.up ℤ)).obj P ≅ M) := by
  classical
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).toRingHom
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).symm.toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).symm.toRingHom
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  let F := ModuleCat.restrictScalars.{t + 1, t, t + 1}
    (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).symm.toRingHom
  let N := (F.mapHomologicalComplex (.up ℤ)).obj M
  let e (i : ℤ) : LinearEquiv
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).toRingHom
      (σ' := (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).symm.toRingHom)
      (M.X i) (N.X i) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun (r : ULift.{t + 1, t} R) x ↦ rfl }
  have hN (i : ℤ) : Module.Finite R (N.X i) := by
    have := ht i
    exact Module.Finite.of_surjective (e i).toLinearMap (e i).surjective
  let small (i : ℤ) : Small.{t} (N.X i) := by
    have := hN i
    exact Module.Finite.small R (N.X i)
  let V (i : ℤ) := ModuleCat.of R (Shrink.{t} (N.X i))
  let f (i : ℤ) : V i ≃ₗ[R] N.X i := Shrink.linearEquiv R (N.X i)
  let P : CochainComplex (ModuleCat.{t} R) ℤ :=
    { X := V
      d := fun i j ↦ ModuleCat.ofHom
        ((f j).symm.toLinearMap.comp ((N.d i j).hom.comp (f i).toLinearMap))
      shape := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (f j).symm (N.d i j (f i x)) = 0
        rw [N.shape i j hij]
        exact (f j).symm.map_zero
      d_comp_d' := by
        intro i j k _ _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (f k).symm (N.d j k (f j ((f j).symm (N.d i j (f i x))))) = 0
        rw [LinearEquiv.apply_symm_apply]
        have h := ConcreteCategory.congr_hom (N.d_comp_d i j k) (f i x)
        change N.d j k (N.d i j (f i x)) = 0 at h
        rw [h, map_zero] }
  let G := ModuleCat.uliftFunctor.{t + 1, t} R ⋙
    ModuleCat.restrictScalars.{t + 1, t + 1, t}
      (ULift.ringEquiv : ULift.{t + 1, t} R ≃+* R).toRingHom
  let fLift (i : ℤ) : G.obj (P.X i) ≃ₗ[ULift.{t + 1, t} R] M.X i :=
    { toFun := fun x ↦ f i x.down
      invFun := fun x ↦ ULift.up ((f i).symm x)
      left_inv := fun x ↦ by
        apply ULift.ext
        exact (f i).symm_apply_apply x.down
      right_inv := fun x ↦ (f i).apply_symm_apply x
      map_add' := fun x y ↦ (f i).map_add x.down y.down
      map_smul' := fun r x ↦ (f i).map_smul r.down x.down }
  let ep : (G.mapHomologicalComplex (.up ℤ)).obj P ≅ M :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ (fLift i).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change N.d i j (f i x.down) = f j ((f j).symm (N.d i j (f i x.down)))
      exact ((f j).apply_symm_apply _).symm)
  refine ⟨P, ?_, ?_, ?_, ⟨ep⟩⟩
  · apply (P.isStrictlyGE_iff a).2
    intro i hi
    have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp (hz i (Or.inl hi))
    have : Subsingleton (N.X i) := this
    exact ModuleCat.isZero_iff_subsingleton.mpr (f i).toEquiv.subsingleton
  · apply (P.isStrictlyLE_iff b).2
    intro i hi
    have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp (hz i (Or.inr hi))
    have : Subsingleton (N.X i) := this
    exact ModuleCat.isZero_iff_subsingleton.mpr (f i).toEquiv.subsingleton
  · intro i
    have := hN i
    exact Module.Finite.equiv (f i).symm

/-- Finite etale-local cohomology and fixed cohomological bounds give bounded
constant finite-module complexes on a further etale cover. This assertion is for an
arbitrary derived object over a coefficient sheaf identified with a finite constant
ring; it contains no adic filtration or perfect-residue hypothesis.

Source: Stacks Project, proetale.tex, lemma-compare-constructible-derived (09AL),
and sites-cohomology.tex, lemma-locally-constant (094G).
(blueprint: lem-weil-pbc-finite-coefficient-etale-bounded-models).

Proof: use the coefficient isomorphism to restrict scalars to the constant ring.
On the slice at V, the supplied etale-local finite module descriptions make every
cohomology sheaf constructible with one stratum. Exact localization commutes with
cohomology, so its cohomology vanishes outside [a,b]. Identify the localized
pro-etale site with that of V. The finite-ring bounded constructible comparison
(09AL) descends the derived object to the etale site and preserves these bounds.
Exact fully faithful comparison identifies its etale cohomology with the given
finite local systems. Apply bounded constant-model descent (094G), preserving
[a,b]. Its construction descends the differentials as well as the terms.
Each finite module over the finite ring has a finite underlying set, so transport
its complex, including all differentials, to the coefficient universe t. Apply
the exact constant realization and the coefficient isomorphism to the resulting
etale model. Compatibility with exact slice restriction gives the displayed
isomorphism. Compose the covers and close under further restriction to obtain a
covering sieve. Only nonempty charts are requested; empty charts require no model
in this statement. The zero coefficient ring gives the zero complex. -/
theorem finiteCoefficient_etale_bounded_models
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ)
    (K : DerivedCategory (SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hvan : let R₀ := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R);
      ∀ q : ℤ, q < a ∨ b < q → IsZero
        ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
          ((DerivedCategory.homologyFunctor _ q).obj K)))
    (hloc : let R₀ := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R);
      ∀ (q : ℤ) (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X φ).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                  koszulConstantFunctor X B).obj N)))) :
    ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
      ∀ (W : X.Etale) (g : W ⟶ V), T g → Nonempty W.left →
        ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Finite B (P.X i)) ∧ Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
                ((toProEt X).obj W) K ≅
              ringedSiteDerivedRestrictionOfUniverses
                ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
                ((toProEt X).obj W) ((completedAdicDerivedChange X φ).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)))) := by
  classical
  obtain ⟨L, hLvan, hLloc, htransfer⟩ := finiteCoefficient_etale_slice_origin
    X B R φ hφ K V a b hab hvan hloc
  obtain ⟨𝒰, h𝒰⟩ := AlgebraicGeometry.Etale.etale_site_bounded_constant_models
    V.left (ULift.{t + 1} B) L a b hab hLvan hLloc
  have hmodels (i : 𝒰.I₀) :
      ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ q : ℤ, Module.Finite B (P.X q)) ∧ Nonempty
          ((AlgebraicGeometry.Etale.upperStar
              (ModuleCat.{t + 1} (ULift.{t + 1} B)) (𝒰.f i)).mapDerivedCategory.obj L ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapHomologicalComplex (.up ℤ)).obj
                (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
                  ).mapHomologicalComplex (.up ℤ)).obj P))) := by
    obtain ⟨E, hEfinite, hEzero, ⟨eE⟩⟩ := h𝒰 i
    obtain ⟨P, hPa, hPb, hfinite, ⟨eP⟩⟩ := small_finite_complex B E a b hEzero
      (fun q ↦ by have := hEfinite q; exact Module.Finite.of_finite)
    refine ⟨P, hPa, hPb, hfinite, ⟨eE ≪≫ ?_⟩⟩
    exact DerivedCategory.Q.mapIso
      (((constantSheaf (𝒰.X i).smallEtaleTopology
        (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapHomologicalComplex (.up ℤ)).mapIso eP.symm)
  let U (i : 𝒰.I₀) : X.Etale := Scheme.Etale.mk (𝒰.f i ≫ V.hom)
  let f (i : 𝒰.I₀) : U i ⟶ V := MorphismProperty.Over.homMk (𝒰.f i) rfl
  refine ⟨Sieve.ofArrows U f, ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨i, y, hy⟩
  · intro W g hg _
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff U f g).mp hg
    obtain ⟨P, hPa, hPb, hfinite, ⟨eP⟩⟩ := hmodels i
    refine ⟨P, hPa, hPb, hfinite, htransfer W (h ≫ f i) P ⟨?_⟩⟩
    let C := ModuleCat.{t + 1} (ULift.{t + 1} B)
    let E := ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
      ).mapHomologicalComplex (.up ℤ)).obj P
    let F := AlgebraicGeometry.Etale.upperStar C h.left
    exact (Functor.mapDerivedCategoryNatIso
        (AlgebraicGeometry.Etale.upperStarComp C h.left (𝒰.f i))).app L ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app L ≪≫
      F.mapDerivedCategory.mapIso eP ≪≫ F.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso
          (AlgebraicGeometry.Scheme.upperStarConstantSheafIso C h.left) (.up ℤ)).app E)

end AlgebraicGeometry.Scheme
