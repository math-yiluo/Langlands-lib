/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverTransport
import WeilConjectures.AlgebraicGeometry.KInjectiveSchemeEvaluationModels

/-! # K-injective models for evaluation on the open scheme

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-exact-source-kinjective-evaluation-open-models).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Transport a comparison square along model isomorphisms and a functor factorization. -/
private theorem comparison_of_transported_evaluation
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    (T : C₁ ⥤ C₂) (Q : C₂ ⥤ D) (E : C₁ ⥤ D) (v : E ≅ T ⋙ Q)
    {A B : C₁} {A' B' : C₂} {S H : D} (f : A ⟶ B) (g : S ⟶ H)
    (t : T.obj A ≅ A') (b : T.obj B ≅ B')
    (h : ∃ a' : S ≅ Q.obj A', ∃ b' : H ≅ Q.obj B',
      g ≫ b'.hom = a'.hom ≫ Q.map (t.inv ≫ T.map f ≫ b.hom)) :
    ∃ a : S ≅ E.obj A, ∃ b : H ≅ E.obj B, g ≫ b.hom = a.hom ≫ E.map f := by
  obtain ⟨a', b', h⟩ := h
  refine ⟨a' ≪≫ (Q.mapIso t).symm ≪≫ (v.app A).symm,
    b' ≪≫ (Q.mapIso b).symm ≪≫ (v.app B).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Functor.mapIso_inv, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Category.comp_id]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc, Iso.app_inv] using
    congrArg (fun z ↦ a'.hom ≫ Q.map t.inv ≫ z) (v.inv.naturality f)

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-exact-source-evaluation-open-models). -/
local instance kInjectiveEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

-- Elaborating the transported models unfolds the exact-functor factorization.
/-- Ordinary representative evaluation when the coefficient complex is K-injective.
Source: Stacks Project, cohomology.tex, Tags 08DJ (lemma-internal-hom),
08DM (lemma-Rhom-strictly-perfect), and 08DQ (lemma-dual-perfect-complex).
(blueprint: lem-pc-exact-source-kinjective-evaluation-open-models).

Proof: Transport P,F and the degree-zero unit through the exact over-equivalence.
The equivalence preserves the tensor inclusions and Hom projections because it
preserves their coproduct and product universal properties. Thus it preserves the
Hom differential, the signed total differential, and the stated evaluation formula.
It preserves K-injectivity by its exact inverse. Resolve the transported unit by
its fixed K-injective resolution. Hom(P,-) preserves that resolution quasi-isomorphism,
so localization identifies the ordinary dual with RHom(K,1). Since F is K-injective,
the Hom factorization identifies Hom(P,F) with RHom(K,N). K-flatness of the ordinary
dual identifies its total tensor with F with N tensor RHom(K,1); this constructs a.
Use these comparisons for b as well. Replace the tensor factors by K-flat resolutions
in the canonical tensor-Hom representative equation. Uncurry the identity of the
dual. Following a degree-(p,q) tensor inclusion and an r-th Hom projection gives
unit-action evaluation if r+q=0, and zero otherwise. These are precisely hf.
Product projections and coproduct inclusions detect equality, and localization
and cancellation of the Hom resolution isomorphisms give the asserted square.
No inverse of f is used. The same argument applies to zero complexes and empty opens. -/
theorem exists_exactSource_kInjective_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) [F.IsKInjective] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f) := by
  -- Keep the evaluation arrow named while unpacking the transported models.
  intro E₀ H D g
  obtain ⟨t, b, hhom, hdual, hF, hf⟩ :=
    exists_ordinaryEvaluation_over_transport X U P F _hhom _hdual f _hf
  let : Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := inferInstance
  let L : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : PreservesFiniteLimits L := inferInstance
  have : PreservesFiniteColimits L := inferInstance
  let T : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
    L.mapHomologicalComplex (.up ℤ)
  let E := L.mapDerivedCategory
  have v : DerivedCategory.Q ⋙ E ≅ T ⋙ DerivedCategory.Q := L.mapDerivedCategoryFactors
  have : CochainComplex.IsKInjective (T.obj F) := hF
  have eK : DerivedCategory.Q.obj (T.obj P) ≅ K := (v.app P).symm ≪≫ _eK
  have eN : DerivedCategory.Q.obj (T.obj F) ≅ N := (v.app F).symm ≪≫ _eN
  apply comparison_of_transported_evaluation T DerivedCategory.Q (DerivedCategory.Q ⋙ E)
    v f g t b
  exact exists_kInjective_scheme_evaluation_models U.toScheme K N
    (T.obj P) (T.obj F) hhom hdual eK eN (t.inv ≫ T.map f ≫ b.hom) hf

end AlgebraicGeometry
