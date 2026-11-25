/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberDegree
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberIsoSpread

/-!
# Local normal forms of lines on projective bundles

## References

* EGA II, Remark 4.2.7
* Stacks, Tag 0BXJ
* Tag 07VK
* Tag 0B8W
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

private theorem invertible_integerLinePower {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (m : ℤ) : (integerLinePower A hA m).IsInvertible := by
  have : A.IsInvertible := hA
  have hnat (M : X.Modules) [M.IsInvertible] (n : ℕ) :
      (tensorPowNat M n).IsInvertible := by
    induction n with
    | zero => exact isInvertible_tensorUnit
    | succ n ih =>
      have := ih
      exact IsInvertible.tensorObj M (tensorPowNat M n)
  cases m with
  | ofNat n => exact hnat A n
  | negSucc n => exact hnat (dual A) (n + 1)

private theorem nonempty_iso_of_top_restriction {X : Scheme.{u}} (M N : X.Modules)
    (e : (tensorPullback (⊤ : X.Opens).ι).obj M ≅
      (tensorPullback (⊤ : X.Opens).ι).obj N) : Nonempty (M ≅ N) := by
  let c : 𝟭 X.Modules ≅ tensorPullback (⊤ : X.Opens).ι ⋙ tensorPullback X.topIso.inv :=
    (tensorPullbackSectionId X).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ tensorPullback f) (Scheme.toIso_inv_ι X).symm) ≪≫
      tensorPullbackSectionComp X.topIso.inv (⊤ : X.Opens).ι
  exact ⟨c.app M ≪≫ (tensorPullback X.topIso.inv).mapIso e ≪≫ (c.app N).symm⟩

/-- Local integer normal forms and their field normalization. This is the local
part of projective-bundle Picard classification; it makes no global descent assertion. -/
theorem projective_bundle_local_normal_form (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E) :
    (∀ (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules),
      L.IsInvertible → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ m : ℤ,
        Nonempty ((tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj L ≅
          (tensorPullback
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
            (integerLinePower D.line D.invertible m))) ∧
    (∀ (k : Type u) [Field k], (S ≅ Spec (CommRingCat.of k)) →
      ∀ L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules,
        L.IsInvertible → ∃! m : ℤ, Nonempty (L ≅ integerLinePower D.line D.invertible m)) := by
  have hlocal (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
      (hL : L.IsInvertible) (s : S) :
      ∃ U : S.Opens, s ∈ U ∧ ∃ m : ℤ,
        Nonempty ((tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj L ≅
          (tensorPullback
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
            (integerLinePower D.line D.invertible m)) := by
    obtain ⟨m, hm, _⟩ := projective_bundle_fiber_degree S E r hr D L hL s
    obtain ⟨U, hs, hU⟩ := projective_bundle_fiber_iso_spread S E r hr L
      (integerLinePower D.line D.invertible m) hL
      (invertible_integerLinePower D.line D.invertible m) s hm
    exact ⟨U, hs, m, hU⟩
  refine ⟨hlocal, ?_⟩
  intro k _ e L hL
  have : Subsingleton S := e.hom.homeomorph.injective.subsingleton
  let s : S := e.inv default
  obtain ⟨U, hs, m, hU⟩ := hlocal L hL s
  have htop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rwa [Subsingleton.elim y s]
  subst U
  obtain ⟨t⟩ := hU
  obtain ⟨t⟩ := nonempty_iso_of_top_restriction L
    (integerLinePower D.line D.invertible m) t
  refine ⟨m, ⟨t⟩, ?_⟩
  rintro n ⟨t'⟩
  obtain ⟨d, _, hd⟩ := projective_bundle_fiber_degree S E r hr D L hL s
  let f := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s
  exact (hd n ⟨(tensorPullback f).mapIso t'⟩).trans
    (hd m ⟨(tensorPullback f).mapIso t⟩).symm

end AlgebraicGeometry.ProjectiveBundlePicardClassification
