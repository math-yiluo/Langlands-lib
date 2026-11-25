/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPostcomposition
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Ordinary models for evaluation on the open scheme

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-exact-source-evaluation-open-models).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory


attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-exact-source-evaluation-open-models). -/
local instance modelsEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem tensor_quasiIso_of_isKFlat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    {M M' D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (t : M ⟶ M') (ht : QuasiIso t) (hD : D.IsKFlatTensor) :
    QuasiIso (HomologicalComplex.mapBifunctorMap t (𝟙 D) (curriedTensor _) (.up ℤ)) := by
  let : MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic t).1 ht
  have hd := hD (CochainComplex.mappingCone t) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (hd i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso t D (curriedTensor _))

/-- Resolve the coefficient complex and retain the ordinary evaluation square and its
quasi-isomorphisms, independently of the later localization. -/
private theorem exists_localEvaluation_resolution_square (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) :
    ∃ I : CochainComplex (localEvaluationModules X U) ℤ, I.IsKInjective ∧
      ∃ η : F ⟶ I, QuasiIso η ∧
      ∃ fI : localEvaluationTensor X U P I ⟶ homComplex (R := X.sheaf.over U) P I,
        IsLocalOrdinaryEvaluation X U P I fI ∧
      ∃ t : localEvaluationTensor X U P F ⟶ localEvaluationTensor X U P I,
      ∃ h : homComplex (R := X.sheaf.over U) P F ⟶ homComplex (R := X.sheaf.over U) P I,
        QuasiIso t ∧ QuasiIso h ∧ t ≫ fI = f ≫ h := by
  let A := localEvaluationModules X U
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj F
  let η : F ⟶ I := (CochainComplex.toKInjectiveResolution.{u} A).app F
  have hη : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A F).2
  let fI : localEvaluationTensor X U P I ⟶ homComplex (R := X.sheaf.over U) P I :=
    { f := localEvaluationDegreeMap X U P I
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P I n m h }
  have hfI : IsLocalOrdinaryEvaluation X U P I fI := by
    intro p q n r h
    exact localEvaluationDegreeMap_formula X U P I p q n r h
  exact ⟨I, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A F, η, hη,
    fI, hfI,
    HomologicalComplex.mapBifunctorMap η (𝟙 (localEvaluationDual X U P))
      (curriedTensor _) (.up ℤ),
    ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map η,
    tensor_quasiIso_of_isKFlat (R := X.sheaf.over U) η hη hdual,
    hhom F I η hη, ordinaryEvaluation_postcomposition X U P F I η f fI hf hfI⟩

private theorem comparison_of_resolution_square
    {C : Type*} [Category* C] {S H T T' V V' : C}
    (g : S ⟶ H) (f : T ⟶ V) (f' : T' ⟶ V') (t : T ≅ T') (h : V ≅ V')
    (a' : S ≅ T') (b' : H ≅ V')
    (hg : g ≫ b'.hom = a'.hom ≫ f') (hs : t.hom ≫ f' = f ≫ h.hom) :
    ∃ a : S ≅ T, ∃ b : H ≅ V, g ≫ b.hom = a.hom ≫ f := by
  refine ⟨a' ≪≫ t.symm, b' ≪≫ h.symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hg]
  apply (cancel_mono h.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hs]
  simp only [Iso.inv_hom_id_assoc]

/-- Transport a comparison through a square whose vertical maps become isomorphisms. -/
private theorem comparison_of_mapped_resolution_square
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {S H : D} {T T' V V' : C}
    (g : S ⟶ H) (f : T ⟶ V) (f' : T' ⟶ V') (t : T ⟶ T') (h : V ⟶ V')
    [IsIso (L.map t)] [IsIso (L.map h)]
    (hs : t ≫ f' = f ≫ h)
    (hg : ∃ a' : S ≅ L.obj T', ∃ b' : H ≅ L.obj V',
      g ≫ b'.hom = a'.hom ≫ L.map f') :
    ∃ a : S ≅ L.obj T, ∃ b : H ≅ L.obj V, g ≫ b.hom = a.hom ≫ L.map f := by
  obtain ⟨a', b', hg⟩ := hg
  apply comparison_of_resolution_square g (L.map f) (L.map f')
    (asIso (L.map t)) (asIso (L.map h)) a' b' hg
  simpa only [asIso_hom, Functor.map_comp] using L.congr_map hs

/-- The ordinary evaluation calculation, entirely on the open scheme. The functor E
only changes from the over-site to its equivalent scheme site; it does not restrict
an object or an evaluation arrow from X.

Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom),
Tag 08DM (lemma-Rhom-strictly-perfect), and Tag 08DQ (lemma-dual-perfect-complex),
ordinary representative computation without the perfectness-dependent inverse.
(blueprint: lem-pc-exact-source-evaluation-open-models).

Proof:
1. Transport the actual complexes P,F and f along the exact equivalence of module
   categories Modules.overEquiv. It preserves tensor, the unit, Hom complexes,
   their projections, and direct-sum totalization. Thus it preserves the given
   component equations, Hom preservation of quasi-isomorphisms, and K-flatness
   of the actual ordinary dual. Its localization factorization identifies E(QP)
   and E(QF) with the localized transported complexes.
2. Resolve the transported F and the degree-zero unit by the fixed functorial
   K-injective resolution on the open scheme. Hom preservation makes the two
   induced Hom maps quasi-isomorphisms. The derived Hom factorization, followed
   by their localized inverses and eK,eN, supplies the target and dual comparisons.
3. K-flatness of the ordinary dual makes its total tensor with the arbitrary F
   compute the derived tensor. Compose this model comparison with eN and the
   dual comparison to obtain a. In particular, a uses no inverse of f.
4. Replace tensor inputs by K-flat resolutions and use the fixed K-injective
   target. Uncurry the identity of the dual with the canonical representative
   formula. On a summand of degrees p,q followed by the Hom projection indexed
   by r, associativity and symmetry give the unit-action evaluation when r+q=0,
   and zero otherwise. These are exactly hf. Naturality with the resolution maps
   and detection by tensor inclusions and Hom projections identify the chain
   maps. Localization, and cancellation of the two Hom resolution isomorphisms,
   give g;b=a;E(Qf).
This is a local complex calculation: no global restriction compatibility is
asserted. Zero complexes and the empty open obey the same universal properties. -/
theorem exists_exactSource_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (hdual : (localEvaluationDual X U P).IsKFlatTensor)
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
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
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
  classical
  intro E H D g
  let A := localEvaluationModules X U
  let : HasDerivedCategory.{w} A := (inferInstance : HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
  let Q := DerivedCategory.Q.{w} (C := A)
  let L := Q ⋙ E
  obtain ⟨I, hI, η, hη, fI, hfI, t, h, ht, hh, hs⟩ :=
    exists_localEvaluation_resolution_square X U P F hhom hdual f _hf
  have : IsIso (L.map t) := by
    change IsIso (E.map (Q.map t))
    infer_instance
  have : IsIso (L.map h) := by
    change IsIso (E.map (Q.map h))
    infer_instance
  let eI : E.obj (Q.obj I) ≅ N := (E.mapIso (asIso (Q.map η))).symm ≪≫ _eN
  apply comparison_of_mapped_resolution_square L g f fI t h hs
  exact exists_exactSource_kInjective_evaluation_open_models
    X U K N P I hhom hdual _eK eI fI hfI

end AlgebraicGeometry
