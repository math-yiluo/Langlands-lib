/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Finite-free affine model terms

Source: Stacks Project, Tag 068C (finite-free resolutions), and Tag 08C4;
Mathlib's `tildeFinsupp` and `SheafOfModules.mapFreeIso` implement the basis transport.
(blueprint: lem-affine-finite-free-model-term-iso-free).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 068C and 08C4, finite-basis argument.
Each transported term of the affine finite-free model is isomorphic to a finite free
localized structure-sheaf module. This is the finite-basis transport step: choose a finite basis
of `K.X n`, identify its tilde sheaf with `tildeFinsupp`, and transport that identification
through restriction and the inverse affine-site equivalence. The extension contributes the zero
object in the out-of-range degrees. The finite basis theorem and the functorial preservation of
finite coproducts provide the required isomorphism. The finite basis is indexed by `Fin m`; in
the zero-rank case use `m = 0`. Functoriality transports the basis isomorphism, and extension
by zero preserves the resulting term. (blueprint: lem-affine-finite-free-model-term-iso-free) -/
theorem affine_finite_free_model_term_iso_free {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n)) (n : ℤ) :
    ∃ m : ℕ, Nonempty ((affineFiniteFreeModelComplex U hU K).X n ≅
      SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m))) := by
  classical
  let A := Γ(Y, U)
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.hom
  have : F.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).isLeftAdjoint
  let G := (Scheme.Modules.overEquiv U).inverse
  let L := ((tilde.functor A ⋙ F).mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  change ∃ m : ℕ, Nonempty (G.obj ((L.extend ComplexShape.embeddingDownNat).X n) ≅ _)
  by_cases hn : ∃ i, ComplexShape.embeddingDownNat.f i = n
  · obtain ⟨i, hi⟩ := hn
    have := hfree i
    have := hfinite i
    let I := Module.Free.ChooseBasisIndex (A : Type u) (K.X i)
    let m := Fintype.card I
    let b := (Module.Free.chooseBasis (A : Type u) (K.X i)).reindex
      ((Fintype.equivFin I).trans Equiv.ulift.symm)
    let e := (tilde.functor A).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp (ULift.{u} (Fin m))
    let eF := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
      (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm).symm
    let eG := (SheafOfModules.mapFreeIso G (ULift.{u} (Fin m))
      (U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm).symm
    exact ⟨m, ⟨G.mapIso (L.extendXIso ComplexShape.embeddingDownNat hi) ≪≫
      G.mapIso (F.mapIso e ≪≫ eF) ≪≫ eG⟩⟩
  · have hz := L.isZero_extend_X ComplexShape.embeddingDownNat n
      (fun i hi => hn ⟨i, hi⟩)
    have hfreezero : IsZero (SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin 0))) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply Sigma.hom_ext
      intro i
      exact Fin.elim0 i.down
    exact ⟨0, ⟨(G.map_isZero hz).iso hfreezero⟩⟩

end AlgebraicGeometry
