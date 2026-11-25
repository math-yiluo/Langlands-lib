/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Module.ProjAwayDegreeZeroExact
import WeilConjectures.AlgebraicGeometry.Modules.BasisExactness
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Exactness of associated sheaves on the projective line

Source: Stacks Project, Constructions, Lemma 01M7, final paragraph; the sheafifying
clause of blueprint `theorem-riemann-roch-coherent-serre-duality`.
(blueprint: lem-sc-p1-proj-sheafification-exact)

`P = Proj k[x₀,x₁]` is `Proj (homogeneousSubmodule (Fin 2) k)` with the standard
total-degree grading `MvPolynomial.gradedAlgebra`, as in the landed sibling
`coherent_exists_graded_representation`.
The associated sheaves and induced maps are specified using the chart identifications
of `gradedModuleSheaf_exists` and the fraction formula of `tilde_functorial`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Sheafifying a short exact graded sequence over `k[x₀,x₁]` gives a short exact
sequence of modules on its Proj.
Source: Stacks, Constructions, Lemma 01M7, final paragraph.
(blueprint: lem-sc-p1-proj-sheafification-exact)

Proof:
1. By `lem-sc-p1-proj-tilde-functorial`, the given chart fraction formulas are those
   of the induced sheaf maps; composition is preserved, so the composite is zero.
   The stalk identifications of `lem-weil-pbc-proj-graded-module-sheaf-exists` identify
   these maps with the degree-zero localized linear maps at each homogeneous prime.
2. Apply `lem-sc-p1-proj-degreezero-localization-exact` to the given graded sequence
   at every such prime. The sequence of stalks is short exact.
3. Apply `lem-weil-pbc-ringed-space-module-exactness-local-lifting` and the germ
   representation and equality criteria of `def-weil-pbc-module-stalk`: every stalk
   lift is represented on a neighbourhood, which can be shrunk until the image is
   the required section. This gives the epimorphism and exactness at the middle.
   If the first map kills a section, stalkwise injectivity makes all its germs zero;
   shrink around each point and use the sheaf axiom to conclude that the section
   is zero. Thus the first map is a monomorphism, completing short exactness.
-/
theorem proj_sheafification_shortExact
    (k : Type u) [Field k]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (MvPolynomial (Fin 2) k) (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (h𝓜 : ∀ i, DirectSum.IsInternal (𝓜 i))
    (hsmul : ∀ (i : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M i),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 i z → a • y ∈ 𝓜 i (n + z))
    (F : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k), ∀ (d : ℕ), 0 < d →
      f ∈ homogeneousSubmodule (Fin 2) k d →
      (F i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 i n : Set (M i))) (Submonoid.powers f))
    (phi : M 0 →ₗ[MvPolynomial (Fin 2) k] M 1)
    (psi : M 1 →ₗ[MvPolynomial (Fin 2) k] M 2)
    (hphi : ∀ (z : ℤ) (y : M 0), y ∈ 𝓜 0 z → phi y ∈ 𝓜 1 z)
    (hpsi : ∀ (z : ℤ) (y : M 1), y ∈ 𝓜 1 z → psi y ∈ 𝓜 2 z)
    (hinj : Function.Injective phi) (hexact : Function.Exact phi psi)
    (hsurj : Function.Surjective psi)
    (i : F 0 ⟶ F 1) (q : F 1 ⟶ F 2)
    (hi : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 0)
      (s : (F 0).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 0 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 f d hd hf (i.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 1)
      (s : (F 1).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 1 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 f d hd hf (q.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  let B : Set (Proj (homogeneousSubmodule (Fin 2) k)).Opens :=
    {U | ∃ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d ∧ f ∈ homogeneousSubmodule (Fin 2) k d ∧
        U = basicOpen (homogeneousSubmodule (Fin 2) k) f}
  have hB : TopologicalSpace.Opens.IsBasis B :=
    (standardOpenProperties.{u, u, u} (homogeneousSubmodule (Fin 2) k)).1
  have hsections : ∀ U ∈ B,
      Function.Injective (i.val.app (op U)) ∧
      Function.Exact (i.val.app (op U)) (q.val.app (op U)) ∧
      Function.Surjective (q.val.app (op U)) := by
    rintro U ⟨f, d, hd, hf, rfl⟩
    exact proj_away_degreeZero_exact k M 𝓜 h𝓜 hsmul f d hd hf
      (fun j ↦ (F j).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
      (fun j ↦ alpha j f d hd hf) (fun j ↦ halpha j f d hd hf)
      phi psi hphi hpsi hinj hexact hsurj
      (i.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom
      (q.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom
      (hi f d hd hf) (hq f d hd hf)
  obtain ⟨hcomp, hmono, hepi, hex⟩ :=
    Scheme.Modules.exactness_of_basis_sections
      (Proj (homogeneousSubmodule (Fin 2) k)) B hB (F 0) (F 1) (F 2) i q hsections
  let : Mono i := hmono
  let : Epi q := hepi
  exact ⟨hcomp, ⟨hex hcomp⟩⟩

end AlgebraicGeometry.Proj
