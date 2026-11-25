/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.RingTheory.RingPseudoCoherentLocalizationGlue
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentLocalizationCover

/-! # Pseudo-coherence on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.2, Tag 08E7,
pseudo-coherent clause (blueprint: lem-pc-affine-pseudo-coherent-criterion).
-/

@[expose] public section

universe u wA wX

open CategoryTheory

namespace AlgebraicGeometry

private theorem tilde_finite_free_restrict_iso (A : Type u) [CommRing A]
    (N : ModuleCat.{u} A) [Module.Free A N] [Module.Finite A N]
    (U : (Spec (.of A)).Opens) :
    ∃ r : ℕ, Nonempty
      ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U).obj
        ((tilde.functor (.of A)).obj N) ≅
          SheafOfModules.free
            (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin r))) := by
  classical
  let r := Fintype.card (Module.Free.ChooseBasisIndex A N)
  let b := (Module.Free.chooseBasis A N).reindex
    ((Fintype.equivFin _).trans (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r)))
  let t := (tilde.functor (.of A)).mapIso (b.repr.toModuleIso) ≪≫
    tildeFinsupp (R := .of A) (ULift.{u} (Fin r))
  let F := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U
  refine ⟨r, ⟨F.mapIso t ≪≫ ?_⟩⟩
  exact (SheafOfModules.mapFreeIso F (ULift.{u} (Fin r)) (Iso.refl _)).symm

/-- The object obtained by associating sheaves termwise to a complex of `A`-modules on
`Spec A` is pseudo-coherent precisely when the module complex is quasi-isomorphic to a
bounded-above complex of finite free modules. The affine equivalence
`lem-pc-affine-qcoh-derived-equivalence` identifies this termwise construction with its
image in the quasi-coherent derived category.

Source: Stacks Project, Tag 08E7, Lemma 36.10.2, pseudo-coherent clause
(blueprint: lem-pc-affine-pseudo-coherent-criterion).

Proof:
1. Given a bounded-above finite free model, associate sheaves termwise, using
   `lem-pc-affine-qcoh-derived-equivalence`. The tilde functor sends A to the structure
   sheaf and preserves finite sums (`lem-weil-pbc-affine-tilde-gamma-adjunction`, part 4).
   The resulting complex is finite free and bounded above on the one-member cover.
   Apply `def-pur-pseudo-coherent-complex`.
2. Conversely, local pseudo-coherence gives bounded-above finite free models near every
   point. Quasi-compactness and the standard-open basis give a finite cover by D(f_i)
   refining these neighbourhoods, with the f_i generating the unit ideal.
3. Over D(f_i), restriction of tilde(M) is tilde(M localized at f_i), by
   `lem-weil-pbc-spec-module-tilde-sections`. Full faithfulness of tilde on free modules
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`, parts 1 and 2) lifts the local model's
   differentials to module maps. The affine derived equivalence then identifies the
   localized module complex with this bounded-above finite free model.
4. Apply `lem-pc-ring-pseudo-coherent-localization-glue` to these finitely many
   localizations to obtain a bounded-above finite free model over A.
-/
theorem isPseudoCoherent_affine_iff (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    Scheme.IsPseudoCoherent (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ↔
      DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) := by
  constructor
  · intro h
    let _ : ∀ f : A, HasDerivedCategory.{u + 1}
        (ModuleCat.{u} (Localization.Away f)) := fun _ ↦ HasDerivedCategory.standard _
    obtain ⟨r, f, hf, hlocal⟩ := affine_pseudoCoherent_localization_cover A M h
    exact (DerivedCategory.ringPseudoCoherent_localization_glue (0 : ℤ) M r f hf).2 hlocal
  · rintro ⟨E, b, hbound, hfree, ⟨i⟩⟩
    obtain ⟨e, ⟨c⟩, _⟩ := exists_affineQCohDerivedEquivalence A
    let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
    let j : DerivedCategory.Q.obj (T.obj M) ≅ DerivedCategory.Q.obj (T.obj E) :=
      (c.app M).symm ≪≫
        (e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).mapIso i.symm ≪≫ c.app E
    intro y
    let U : (Spec (.of A)).Opens := ⊤
    let F := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U
    let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (T.obj E)
    refine ⟨U, by simp [U], P, ⟨b, ?_⟩, ?_, ?_⟩
    · intro n hn
      let _ : (tilde.functor (.of A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
      let _ := hbound
      exact F.map_isZero ((tilde.functor (.of A)).map_isZero
        (E.isZero_of_isStrictlyLE b n hn))
    · intro n
      let _ := (hfree n).1
      let _ := (hfree n).2
      exact tilde_finite_free_restrict_iso A (E.X n) U
    · exact ⟨F.mapDerivedCategory.mapIso j ≪≫ F.mapDerivedCategoryFactors.app (T.obj E)⟩

end AlgebraicGeometry
