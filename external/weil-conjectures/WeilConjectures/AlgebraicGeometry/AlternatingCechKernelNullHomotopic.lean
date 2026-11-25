/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import WeilConjectures.AlgebraicGeometry.AlternatingCechSecondSortingIdentity

/-!
# Null homotopy for the kernel of ordered restriction

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A full Čech endomorphism whose increasing coordinates vanish is null homotopic.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equations 20.23.6.1 and
20.23.6.2. (blueprint: lem-pc-alternating-cech-kernel-null-homotopic)

Proof: Let kappa be signed stable sorting of tuples. The first operator H of equation
20.23.6.1 satisfies dH+Hd = id-kappa: for each tuple t, sum over a the section on
[t(sigma(0)),...,t(sigma(a)),t(sigma_a(a)),...,t(sigma_a(p))], with coefficient
(-1)^a sign(sigma_a), where sigma sorts t stably and sigma_a keeps its first a positions
and orders the remaining positions increasingly. Transport between equal intersections
using the unique maps of opens. On expanding the two differentials, terms deleting a
nonjunction position cancel with the corresponding face term; the junction terms
telescope, with endpoints id and minus kappa. This identity also shows kappa is a
cochain map. Its image is identified by restriction with nondecreasing-tuple cochains.
On that image use K of equation 20.23.6.2: on a strictly increasing tuple put zero;
otherwise insert one copy at the first adjacent equality in position a, with sign
(-1)^a. In dK+Kd the faces away from this first equality cancel in pairs, while the
faces in the repeated block give the original value. Consequently dK+Kd is id minus
the projection that kills repeated tuples. Pull K back by the signed stable-sorting
identification and precompose with kappa. Together with H this gives an operator L
on the full complex satisfying dL+Ld = id-P, where P is signed extension of
increasing restriction. Since f vanishes on increasing coordinates, P after f is zero.
Precomposing L with f yields d(Lf)+(Lf)d=f, the required null homotopy. Degree-zero
incoming components are zero; when I is empty all products are trivial. No covering
hypothesis or nonempty index type is used. -/
theorem alternatingCechKernelNullHomotopic (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (f : S.complex F ⟶ S.complex F)
    (hf : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}), (f.f p s) t.1 = 0) :
    Nonempty (Homotopy f 0) := by
  classical
  let h := Homotopy.nullHomotopy' (cechFirstSortingFamily X U F S)
  let k := Homotopy.nullHomotopy' (cechSecondSortingFamily X U F S)
  have he : f ≫ (Homotopy.nullHomotopicMap' (cechFirstSortingFamily X U F S) +
      Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)) = f := by
    apply HomologicalComplex.Hom.ext
    funext p
    rw [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      cechFirstSortingIdentity, cechSecondSortingIdentity]
    have hz : f.f p ≫ cechAlternatingProjectionMap X U F S p = 0 := by
      ext s
      funext t
      change (∑ σ : Equiv.Perm (Fin (p + 1)),
        if StrictMono (t ∘ σ) then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op
            ((f.f p s) (t ∘ σ)) else 0) = 0
      apply Finset.sum_eq_zero
      intro σ _
      split_ifs with ht
      · rw [hf p s ⟨t ∘ σ, ht⟩]
        simp
      · rfl
    rw [sub_add_sub_cancel]
    change (f.f p : S.cochains F p ⟶ S.cochains F p) ≫
      (𝟙 (S.cochains F p) - cechAlternatingProjectionMap X U F S p) = f.f p
    erw [Preadditive.comp_sub, Category.comp_id, hz, sub_zero]
  refine ⟨?_⟩
  simpa only [he, comp_zero, add_zero] using (h.add k).compLeft f

end AlgebraicGeometry.Scheme
