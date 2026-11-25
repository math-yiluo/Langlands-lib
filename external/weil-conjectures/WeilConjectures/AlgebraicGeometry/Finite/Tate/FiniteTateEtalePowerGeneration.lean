/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local generation of finite etale Tate powers

Source: Stacks Project, sites-modules.tex, section-tensor-product (03EK),
and sites.tex, lemma-sections-sheafification (00WK).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

private noncomputable def rawPower (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) : ℕ → T.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A
  | 0 => (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A)
  | 1 => finiteEtaleMuModulePresheaf T m ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA)
  | k + 2 => rawPower T A m hA (k + 1) ⊗
      (finiteEtaleMuModulePresheaf T m ⋙
        ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))

private noncomputable def rawPowerMap (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) :
    (d : ℕ) → rawPower T A m hA d ⟶ (finiteEtaleTateTwist T m A hA d).obj
  | 0 => toSheafify T.smallEtaleTopology _
  | 1 => toSheafify T.smallEtaleTopology _
  | k + 2 => by
    dsimp only [rawPower, finiteEtaleTateTwist]
    exact ((rawPowerMap T A m hA (k + 1) ⊗ₘ
        toSheafify T.smallEtaleTopology (finiteEtaleMuModulePresheaf T m ⋙
          ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))) ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T m A hA (k + 1)) (finiteEtaleTateLine T m A hA))

private theorem rawPowerMap_local (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (d : ℕ) :
    Presheaf.IsLocallySurjective T.smallEtaleTopology (rawPowerMap T A m hA d) := by
  have h1 : T.smallEtaleTopology.W (rawPowerMap T A m hA 1) := by
    simpa only [rawPowerMap] using (T.smallEtaleTopology.W_adj_unit_app
      (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (rawPower T A m hA 1))
  have hw (d : ℕ) : T.smallEtaleTopology.W (rawPowerMap T A m hA d) := by
    induction d using Nat.twoStepInduction with
    | zero =>
      simpa only [rawPowerMap] using T.smallEtaleTopology.W_adj_unit_app
        (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (rawPower T A m hA 0)
    | one =>
      exact h1
    | more k _ ih =>
      simp only [rawPowerMap]
      exact T.smallEtaleTopology.W.comp_mem _ _
        (T.smallEtaleTopology.W.tensorHom_mem _ _ ih h1)
        (T.smallEtaleTopology.W_μ_sheafToPresheaf _ _)
  exact (hw d).isLocallySurjective

private noncomputable def rawGenerator (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (U : T.Etaleᵒᵖ) (a : A) :
    (d : ℕ) → (Fin d → (T.rootsOfUnitySheaf m).obj.obj U) →
      (rawPower T A m hA d).obj U
  | 0, _ => a
  | 1, z => a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA]
      (show finiteEtaleMuModuleObj T m U from z 0)
  | k + 2, z => by
    dsimp only [rawPower]
    exact (rawGenerator T A m hA U a (k + 1) (fun i ↦ z i.castSucc) ⊗ₜ[A]
      ((1 : A) ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA]
        (show finiteEtaleMuModuleObj T m U from z (Fin.last (k + 1)))))

private theorem rawGenerator_map (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (U : T.Etaleᵒᵖ) (d : ℕ)
    (a : A) (z : Fin d → (T.rootsOfUnitySheaf m).obj.obj U) :
    (rawPowerMap T A m hA d).app U (rawGenerator T A m hA U a d z) =
      finiteTateEtalePowerGenerator T A m hA U a d z := by
  induction d using Nat.twoStepInduction generalizing a with
  | zero => rfl
  | one => rfl
  | more k _ ih =>
    change (Functor.LaxMonoidal.μ
      (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _).app U
        ((rawPowerMap T A m hA (k + 1)).app U
          (rawGenerator T A m hA U a (k + 1) (fun i ↦ z i.castSucc)) ⊗ₜ[A]
          finiteEtaleTateOneGenerator A m T hA U 1 (z (Fin.last (k + 1)))) = _
    rw [ih]
    rfl

private theorem rawGenerator_span (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (U : T.Etaleᵒᵖ) (d : ℕ)
    (t : (rawPower T A m hA d).obj U) :
    t ∈ Submodule.span A (Set.range (fun q :
      A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj U) ↦
        rawGenerator T A m hA U q.1 d q.2)) := by
  classical
  induction d using Nat.twoStepInduction with
  | zero =>
    exact Submodule.subset_span ⟨(t, Fin.elim0), rfl⟩
  | one =>
    induction t using TensorProduct.inductionOn with
    | tmul a z => exact Submodule.subset_span ⟨(a, fun _ ↦ z), rfl⟩
    | add t s ht hs => exact Submodule.add_mem _ ht hs
  | more k _ ih =>
    simp only [rawPower] at t
    change t ∈ Submodule.span A _
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => exact Submodule.add_mem _ ht hs
    | tmul t s =>
      change t ⊗ₜ[A] s ∈ Submodule.span A _
      induction s using TensorProduct.inductionOn with
      | add x y hx hy =>
        simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hx hy
      | tmul b z =>
        have ht := ih t
        induction ht using Submodule.span_induction with
        | zero => simpa only [TensorProduct.zero_tmul] using Submodule.zero_mem _
        | add x y hx hy hx' hy' =>
          simpa only [TensorProduct.add_tmul] using Submodule.add_mem _ hx' hy'
        | smul a x hx hx' =>
          simpa only [TensorProduct.smul_tmul'] using Submodule.smul_mem _ a hx'
        | mem x hx =>
          obtain ⟨⟨a, zs⟩, rfl⟩ := hx
          have hb : b ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z =
              (show A from b) •
                ((1 : A) ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z) := by
            simpa only [mul_one] using
              (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar m A hA)
                (M := finiteEtaleMuModuleObj T m U) b 1 z).symm
          rw [hb, TensorProduct.tmul_smul]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          refine ⟨(a, Fin.snoc zs z), ?_⟩
          simp only [rawGenerator, Fin.snoc_castSucc, Fin.snoc_last]
          rfl

/-- Sections of finite etale Tate powers locally belong to the span of pure root tensors.
Source: Stacks Project, sites-modules.tex, section-tensor-product (03EK),
and sites.tex, lemma-sections-sheafification (00WK).
(blueprint: lem-pur-finite-tate-etale-power-generation)

Proof: form the unsheafified ordered powers of the scalar-extension presheaf,
using the constant scalar presheaf in degree zero. Their maps to the finite Tate
sheaves are locally surjective: the degree-zero and degree-one maps are sheafification
units; the higher-degree maps are tensors of local equivalences followed by the
lax tensor comparison of sheafToPresheaf, also a local equivalence. Tensor induction
shows that sections of each raw power are spanned by ordered pure root tensors.
In the successor step, move the scalar in the final scalar-extension factor outside
the tensor and append its root with Fin.snoc. Induction identifies the images of
these generators with finiteTateEtalePowerGenerator. The image sieve of a section
is covering by local surjectivity, and mapping the raw span gives the required span
on each member. Degree zero, the empty sum and the zero ring require no exceptions.
No invertibility or finiteness assumption on the coefficient ring is needed. -/
theorem finiteTateEtalePowerGenerator_locally_span
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (d : ℕ) (U : T.Etaleᵒᵖ)
    (t : (finiteEtaleTateTwist T m A hA d).obj.obj U) :
    ∃ S : Sieve U.unop, S ∈ T.smallEtaleTopology U.unop ∧
      ∀ (V : T.Etale) (v : V ⟶ U.unop), S v →
        (finiteEtaleTateTwist T m A hA d).obj.map v.op t ∈
          Submodule.span A (Set.range (fun q :
            A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj (op V)) ↦
              finiteTateEtalePowerGenerator T A m hA (op V) q.1 d q.2)) := by
  let η := rawPowerMap T A m hA d
  let := rawPowerMap_local T A m hA d
  refine ⟨Presheaf.imageSieve η t, Presheaf.imageSieve_mem _ _ t, ?_⟩
  rintro V v ⟨x, hx⟩
  rw [← hx]
  have hspan : Submodule.span A (Set.range (fun q :
      A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj (op V)) ↦
        rawGenerator T A m hA (op V) q.1 d q.2)) ≤
      (Submodule.span A (Set.range (fun q :
        A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj (op V)) ↦
          finiteTateEtalePowerGenerator T A m hA (op V) q.1 d q.2))).comap
        (η.app (op V)).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, z⟩, rfl⟩
    change (rawPowerMap T A m hA d).app (op V)
        (rawGenerator T A m hA (op V) a d z) ∈
      Submodule.span A (Set.range (fun q :
        A × (Fin d → (T.rootsOfUnitySheaf m).obj.obj (op V)) ↦
          finiteTateEtalePowerGenerator T A m hA (op V) q.1 d q.2))
    rw [rawGenerator_map]
    exact Submodule.subset_span ⟨(a, z), rfl⟩
  exact hspan (rawGenerator_span T A m hA (op V) d x)

end AlgebraicGeometry.Scheme
