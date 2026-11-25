/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.HomogeneousBasisProjCoproduct
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProjTwistInverseTransport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Homogeneous bases give finite sums of twists

## References

* Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The inverse transport of an associated sheaf of a finite graded free module is the
finite sum of twists with the prescribed basis degrees. No resolution or exactness is assumed. -/
theorem homogeneous_basis_sheaf_twists (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (r : ℕ) (d : Fin r → ℤ)
    (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) M)
    (hb : ∀ a : Fin r, b a ∈ 𝓜 (-(d a))) :
    Nonempty ((Scheme.Modules.pullback C.iso.inv).obj F ≅
      ∐ (fun a ↦ ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (d a))) := by
  classical
  obtain ⟨e⟩ := homogeneous_basis_proj_coproduct k M 𝓜 h𝓜 hsmul F
    alpha halpha hscalar hres r d b hb
  let P := Scheme.Modules.pullback C.iso.inv
  let T := fun a : Fin r ↦ twist (homogeneousSubmodule (Fin 2) k) (d a)
  let t := fun a : Fin r ↦ (proj_twist_inverse_transport k C (d a)).some
  exact ⟨P.mapIso e ≪≫ PreservesCoproduct.iso P T ≪≫ Sigma.mapIso t⟩

end AlgebraicGeometry.Proj
