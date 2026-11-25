/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality

/-! # Localized evaluation and chain-map composition

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-localized-evaluation).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private lemma uncurry_chain_natural (X : Scheme.{u})
    (P P' L L' M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    schemeTensorHomUncurry X P' L' M'
        (a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
          (X := (op L, (schemeHomKInjectiveResolution X).obj M))
          (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
          (b.op, (schemeHomKInjectiveResolution X).map c)) =
      HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (.up ℤ) ≫
        schemeTensorHomUncurry X P L M φ ≫ (schemeHomKInjectiveResolution X).map c := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : q + p = n := by change p + q = n at h; omega
  simp only [HomologicalComplex.comp_f]
  rw [schemeTensorHomUncurry_component X P' L' M' _ p q n h h']
  conv_rhs =>
    rw [HomologicalComplex.ι_mapBifunctorMap_assoc a b (curriedTensor _) (.up ℤ)]
  have hc := congrArg (fun f ↦ f ≫ ((schemeHomKInjectiveResolution X).map c).f n)
    (schemeTensorHomUncurry_component X P L M φ p q n h h')
  simp only [Category.assoc] at hc
  conv_rhs => rw [hc]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  conv_rhs => rw [← tensorHom_def_assoc]
  exact schemeTensorHomUncurryComponent_natural X P P' L L' M M' a b c φ p q n h'

/-- The localized evaluation composite is natural for actual Hom-complex inputs.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-localized-evaluation).

Proof: Put ψ = a followed by φ followed by Hom(b,I(c)). Restrict U(ψ) and
Tot(a tensor b) followed by U(φ) followed by I(c) to the summand P'^p tensor L'^q
in total degree n = p+q. The projection equation in homComplex_exists identifies
ψ's projection with a_p followed by φ's projection followed by Hom(b_q,I(c)_n).
Naturality of SheafOfModules.tensorHomEquiv and of the symmetry identifies its
uncurrying with (a_p tensor b_q) followed by U(φ)'s component followed by I(c)_n.
The summand equation schemeTensorHomUncurry_component and coproduct
extensionality therefore give equality of the two chain maps. Apply Q. The
lax-monoidal comparison μ is natural in both chain variables, so
(Qa tensor Qb);μ(P,L) = μ(P',L');Q Tot(a tensor b). Finally the augmentation
M -> I(M) is natural in c, hence QI(c);(Qη_M')⁻¹ = (Qη_M)⁻¹;Qc.
Associativity gives precisely the stated equality. No K-flatness or lift of an
arbitrary derived arrow is needed. For identities this is reflexive; for zero
maps component evaluation is zero; all total degrees and unbounded complexes
use the same coproduct extensionality. -/
theorem schemeTensorHomUncurry_localized_evaluation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P P' L L' M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P' L' ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M'
        (a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
          (X := (op L, (schemeHomKInjectiveResolution X).obj M))
          (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
          (b.op, (schemeHomKInjectiveResolution X).map c))) ≫
        schemeHomResolutionInverse X M' =
      (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
        (pullbackTensorModelMap X P L ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
            schemeHomResolutionInverse X M) ≫ DerivedCategory.Q.map c := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  have (A B : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  let := HomologicalComplex.monoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let := schemeDerivedTensorMonoidal X
  have hchain := uncurry_chain_natural X P P' L L' M M' a b c φ
  have hμ : (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
      pullbackTensorModelMap X P L = pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (.up ℤ)) := by
    exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q a b
  have hη := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).naturality c
  have hres : DerivedCategory.Q.map ((schemeHomKInjectiveResolution X).map c) ≫
      schemeHomResolutionInverse X M' =
        schemeHomResolutionInverse X M ≫ DerivedCategory.Q.map c := by
    have : IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u} _).app M)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
    have : IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u} _).app M')) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M').2
    dsimp only [schemeHomResolutionInverse]
    rw [IsIso.comp_inv_eq, Category.assoc]
    symm
    rw [IsIso.inv_comp_eq]
    simpa only [Functor.map_comp, Functor.id_map, schemeHomKInjectiveResolution]
      using congrArg DerivedCategory.Q.map hη
  rw [hchain, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  simp only [hres]
  simp only [← Category.assoc]
  conv_lhs => rw [← hμ]


end AlgebraicGeometry
