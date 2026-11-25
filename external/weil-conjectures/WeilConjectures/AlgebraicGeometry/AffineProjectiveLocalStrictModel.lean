/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Projective

/-! # Local strictly perfect models of bounded finite-projective affine complexes -/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Termwise tilde of a bounded finite-projective complex admits strictly perfect models
on the localized sites of all points.
Source: Stacks Project, perfect.tex, Lemma perfect-lemma-perfect-affine (Tag 08EB).
(blueprint: lem-pc-affine-projective-local-strict-model)

Proof: A finite projective module is a retract of a finite free module. Apply the additive
associated-sheaf functor to the splitting maps; its preservation of identities and
composition preserves the retract equation. The associated sheaf of a finite free module
is the corresponding finite free structure-sheaf module, and restriction to the localized
site preserves this finite free module and its splitting. Apply this to every term of P.
Use the whole scheme as the open neighborhood of each point, and take the termwise
restriction of tilde(P) as K. The same bound holds since additive functors preserve zero
objects. The comparison between derived restriction and ordinary restriction on complexes
identifies the restriction of Q(tilde(P)) with Q(K); restriction is exact. This proves
strict perfectness without any derived-object isomorphism transport. Empty spectra have
no points, and zero complexes give the zero strictly perfect model. -/
theorem affine_projective_local_strict_model (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfinite : ∀ n : ℤ, Module.Finite A (P.X n))
    (hprojective : ∀ n : ℤ, Module.Projective A (P.X n)) :
    ∀ x : Spec (.of A), ∃ U : (Spec (.of A)).Opens, x ∈ U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ,
        Scheme.IsStrictlyPerfect (Spec (.of A)) U K ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj P)) ≅ DerivedCategory.Q.obj K) := by
  classical
  let T := tilde.functor (.of A)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let L := (T.mapHomologicalComplex (.up ℤ)).obj P
  let F := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) ⊤
  intro x
  refine ⟨⊤, trivial, (F.mapHomologicalComplex (.up ℤ)).obj L, ?_,
    ⟨F.mapDerivedCategoryFactors.app L⟩⟩
  constructor
  · obtain ⟨a, b, hab⟩ := hbounded
    exact ⟨a, b, fun n hn ↦ F.map_isZero (T.map_isZero (hab n hn))⟩
  · intro n
    have : Module.Finite A (P.X n) := hfinite n
    have : Module.Projective A (P.X n) := hprojective n
    obtain ⟨m, f, g, _, _, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective A (P.X n)
    let c := ((Pi.basisFun A (Fin m)).reindex Equiv.ulift.symm).repr.toModuleIso
    let e := F.mapIso (T.mapIso c ≪≫ tildeFinsupp (ULift.{u} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m)) (Iso.refl _)).symm
    have hsplit : (ModuleCat.ofHom g) ≫ (ModuleCat.ofHom f) = 𝟙 (P.X n) := by
      ext a
      exact congrArg (fun h : (P.X n) →ₗ[A] (P.X n) ↦ h a) hfg
    refine ⟨m, F.map (T.map (ModuleCat.ofHom g)) ≫ e.hom,
      e.inv ≫ F.map (T.map (ModuleCat.ofHom f)), ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, ← T.map_comp,
      hsplit, T.map_id]
    exact F.map_id _

end AlgebraicGeometry
