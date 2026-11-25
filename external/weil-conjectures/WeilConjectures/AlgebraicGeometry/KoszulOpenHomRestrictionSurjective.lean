/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomComparisonSquare
import WeilConjectures.Algebra.Homology.SequentialColimitDerivedHomologyRepresentative

/-! # Degree-zero consequences of the Koszul-to-Čech comparison

Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
-/

@[expose] public section

universe uMain wMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem affine_qcoh_representative
    (A : Type uMain) [CommRing A]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    ∃ F : CochainComplex
        (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ,
      (∀ n : ℤ, (F.X n).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj F ≅ E.obj) := by
  let := HasDerivedCategory.standard (ModuleCat.{uMain} A)
  obtain ⟨e, ⟨h⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  let M := DerivedCategory.Q.objPreimage (e.inverse.obj E)
  let F := ((koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  refine ⟨F, ?_, ⟨?_⟩⟩
  · intro n
    change ((tilde.functor (.of A)).obj (M.X n)).IsQuasicoherent
    infer_instance
  · exact (h.app M).symm ≪≫
      (schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso
        (e.functor.mapIso (DerivedCategory.Q.objObjPreimageIso (e.inverse.obj E)) ≪≫
          e.counitIso.app E)

set_option backward.isDefEq.respectTransparency false in
/-- Every derived section on the principal-open union comes from a finite Koszul stage.
Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
(blueprint: lem-sc-koszul-open-hom-restriction-surjective)

Proof: By the affine derived equivalence (Tag 06Z0), represent E by a complex F of
quasi-coherent sheaves, with corresponding A-module complex M. The tails I_e are
bounded complexes of finite free modules, so are K-projective; degree-zero Hom-complex
cohomology computes derived Hom from I_e, naturally in the power transitions. The
Koszul-to-alternating-Čech comparison followed by derived sections is a quasi-isomorphism
(Tags 08D1 and 08D2). Filtered colimits of A-modules are exact, so taking H^0 identifies
its source with the colimit of these derived Hom groups. On the target, evaluation at 1
identifies H^0 of derived sections with Hom from the restricted structure module. The
comparison leg at e is restriction followed by the inverse augmentation: this follows
from the fraction formula of the Koszul comparison on each principal intersection.
The given v is that inverse by its two inverse identities. Surjectivity on H^0 and the
fact that every element of a filtered colimit has a representative give the required
finite stage and morphism. For the empty cover the target group is zero; for E=0 the
zero morphism at stage zero suffices. -/
theorem koszulOpenHom_restriction_surjective
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (v : ∀ e : ℕ,
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenStructure A) ⟶
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenObject A r f e))
    (hv₁ : (∀ e : ℕ,
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) ≫ v e = 𝟙 _))
    (hv₂ : (∀ e : ℕ, v e ≫
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) = 𝟙 _))
 :
    let R := ((SheafOfModules.overFunctor.{uMain}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uMain}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{uMain}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    ∀ ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.1,
      ∃ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1), v e ≫ R.map φ = ψ := by
  intro R
  classical
  let := HasDerivedCategory.standard (ModuleCat.{uMain} A)
  obtain ⟨F, hF, ⟨i⟩⟩ := affine_qcoh_representative A E
  let j (e : ℕ) : R.obj (koszulOpenObject A r f e) ≅ R.obj (koszulOpenStructure A) :=
    ⟨R.map (koszulOpenUnit A r f e), v e, hv₁ e, hv₂ e⟩
  let H := DerivedCategory.homologyFunctor (ModuleCat.{uMain} A) 0
  let D := koszulCechHomDiagram A r f
    (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let c := koszulCechDerivedComparison A r f F ≫ G.map i.hom
  have : IsIso c := affine_koszul_cech_derived_comparison A r f F hF E i
  have : IsIso (H.map c) := inferInstance
  obtain ⟨a, b, hsquare⟩ := koszulOpenHom_comparison_square A r f E F hF i
  intro ψ
  let x : H.obj (DerivedCategory.Q.obj (colimit D)) := inv (H.map c) (b ψ)
  obtain ⟨e, z, hz⟩ := sequentialColimit_derivedHomology_representative A D x
  let φ := (a e).symm z
  refine ⟨e, φ, b.injective ?_⟩
  have hs := hsquare e φ (v e ≫ R.map φ) ((j e).hom_inv_id_assoc (R.map φ))
  have hz' : H.map (DerivedCategory.Q.map (colimit.ι D e)) (a e φ) = x :=
    (congrArg (fun z ↦ H.map (DerivedCategory.Q.map (colimit.ι D e)) z)
      ((a e).apply_symm_apply z)).trans hz
  exact hs.trans ((congrArg (fun z ↦ H.map c z) hz').trans
    (ConcreteCategory.congr_hom (IsIso.inv_hom_id (H.map c)) (b ψ)))

end AlgebraicGeometry
