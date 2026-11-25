/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.FreeRestrictionTorBound

/-! # Tor bounds for projective modules after scalar restriction

Source: Stacks Project, Tags 066K and 0655, the one-module case.
(blueprint: lem-pc-projective-restriction-tor-bound).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Projective B-modules inherit the Tor bound of B after restriction to A.

Source: Stacks Project, Tags 066K and 0655, applied to a projective module in degree zero.
(blueprint: lem-pc-projective-restriction-tor-bound).

Proof: a projective B-module E is a retract of the free module on its underlying set,
via the split surjection sending the basis element indexed by x to x. After scalar
restriction the splitting is still A-linear and the free module is a direct sum of
copies of the restricted regular B-module. For fixed M, compute Tor by resolving M
with free A-modules. Tensor commutes with arbitrary direct sums and direct sums of
modules are exact. Thus Tor_j of the restricted free module with M is the direct sum
of copies of Tor_j(B,M), which is zero for j>d. To identify this calculation with
Tor' (which resolves the first argument), totalize the double complex of projective
resolutions of both arguments. Tensoring with each free term is exact, so augmenting
in either direction gives a quasi-isomorphism; the complexes are bounded above,
which ensures convergence. The splitting of E makes its Tor a retract of the Tor
of the free module. A retract of zero is zero. No finite generation is used.
This includes infinite free modules, d=0, zero rings and zero modules. -/
theorem projective_restriction_tor_bound
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (E : ModuleCat.{u} B) (hE : Projective E) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj (of B B))).obj M)) :
    ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj ((restrictScalars ρ).obj E)).obj M) := by
  classical
  let F := (free B).obj E
  let g : F ⟶ E := freeDesc (↾fun x ↦ x)
  have : Epi g := (epi_iff_surjective g).2 (fun x ↦ ⟨freeMk x, by
    change freeDesc (↾fun x : E ↦ x) (freeMk x) = x
    exact freeDesc_apply _ x⟩)
  have : Projective E := hE
  let f : E ⟶ F := Projective.factorThru (𝟙 E) g
  have hfg : f ≫ g = 𝟙 E := Projective.factorThru_comp (𝟙 E) g
  intro M j hj
  let R := (restrictScalars ρ)
  let T := (Tor' (ModuleCat.{u} A) j)
  let α : (T.obj (R.obj E)).obj M ⟶ (T.obj (R.obj F)).obj M :=
    (T.map (R.map f)).app M
  let : IsSplitMono α := IsSplitMono.mk' ⟨(T.map (R.map g)).app M, by
    simpa [α, R, T, ← Functor.map_comp] using
      congrArg (fun k ↦ (T.map (R.map k)).app M) hfg⟩
  have hα : Mono α := inferInstance
  exact IsZero.of_mono α (free_restriction_tor_isZero ρ E M j (hTor M j hj))

end ModuleCat
