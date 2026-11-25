/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.ScalarExtensionChainHomDiagram
import WeilConjectures.AlgebraicGeometry.AffinePerfectChainGeometricModels

/-! # Chain-level affine perfect Hom comparison

Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation, using Tags
08EB and 06Z0 for the models and Tag 08DW for pullback.
(blueprint: lem-pc-affine-perfect-chain-hom-presentation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Affine perfect Hom models with geometric compatibility checked on chain maps.
Source: Stacks Project, perfect.tex, Tag 09RE (affine calculation), Tags 08EB,
06Z0 and 08DW.
(blueprint: lem-pc-affine-perfect-chain-hom-presentation).

Proof: Write Y as Spec of its global sections B and form the tensor-extension
ring diagram B tensor over R(i) with R(j). Tensor extension preserves the
colimit and identifies its spectra with the given pullbacks. Transport the
perfect objects to Spec B and apply the affine bounded-projective criterion
separately to obtain E and K. Flatness of their projective terms computes all
pullbacks by termwise scalar extension. The affine quasi-coherent derived
equivalence supplies the Hom equivalences at each stage and at the limit.
Take H to be the module-derived Hom diagram, with its extension-of-scalars
cocone. The scalar-extension associators give its equations on chain maps.
Naturality of the tilde pullback comparison and the counit-pinned composition
comparison identify the geometric transports on these chain maps. This lemma
only asks for that chain-level comparison; passage to arbitrary derived
morphisms is proved separately by K-projective localization. The zero ring
causes no exception, and the tail has its initial object i. -/
theorem exists_affinePerfectChainHomPresentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    ∃ (F : Set.Ici i ⥤ CommRingCat.{u})
      (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ),
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (E.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (E.X n)) ∧
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (K.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (K.X n)) ∧
      ∃ (H : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) ⥤ Type (u + 1))
        (ident : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), H.obj j ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)))
        (d : Cocone H)
        (e : d.pt ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K)))
        (stage : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), H.obj j ≃
          ((derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
           (derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj Q))
        (limit : d.pt ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          ident k (H.map (homOfLE hjk) ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          e (d.ι.app j ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
              (colimit.ι F ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
              E K f)) ∧
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          stage k (H.map (homOfLE hjk) ((ident j).symm (DerivedCategory.Q.map f))) =
            perfectStageMap R s j.val.property hjk
              (stage j ((ident j).symm (DerivedCategory.Q.map f)))) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          limit (d.ι.app j ((ident j).symm (DerivedCategory.Q.map f))) =
            perfectLimitMap R c s j.val.property
              (stage j ((ident j).symm (DerivedCategory.Q.map f)))) := by
  obtain ⟨F, E, K, hE, hK, stage, limit, hstage, hlimit⟩ :=
    exists_affinePerfectChainGeometricModels R c hc i Y s P Q hP hQ
  obtain ⟨H, ident, d, e, htransition, hcanonical⟩ :=
    exists_scalarExtensionChainHomDiagram i F E K hE
  refine ⟨F, E, K, hE, hK, H, ident, d, e,
    (fun j ↦ (ident j).trans (stage j)), e.trans limit,
    htransition, hcanonical, ?_, ?_⟩
  · intro j k hjk f
    change stage k (ident k (H.map (homOfLE hjk)
      ((ident j).symm (DerivedCategory.Q.map f)))) =
      perfectStageMap R s j.val.property hjk
        (stage j (ident j ((ident j).symm (DerivedCategory.Q.map f))))
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (stage k) (htransition j k hjk f)).trans (hstage j k hjk f)
  · intro j f
    change limit (e (d.ι.app j ((ident j).symm (DerivedCategory.Q.map f)))) =
      perfectLimitMap R c s j.val.property
        (stage j (ident j ((ident j).symm (DerivedCategory.Q.map f))))
    simp only [Equiv.apply_symm_apply]
    exact (congrArg limit (hcanonical j f)).trans (hlimit j f)

end AlgebraicGeometry
