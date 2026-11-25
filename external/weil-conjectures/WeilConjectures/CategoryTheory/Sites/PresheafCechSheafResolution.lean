/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Sites.PresheafCechSheafPositiveExact
import WeilConjectures.CategoryTheory.Sites.PresheafCechSheafAugmentationExact

/-!
# The augmented sheafified free presheaf Čech resolution

Source: Stacks Project, Hypercoverings, Tag 01GC, and Cohomology on Sites, Tag 079Z.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The free abelian sheaf functor on presheaves of sets.
Source: Stacks Project, Tag 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
noncomputable abbrev presheafCechFreeSheafFunctor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] :
    (Cᵒᵖ ⥤ Type v) ⥤ Sheaf J AddCommGrpCat.{v} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat

/-- The chain complex of sheafified free abelian presheaves on the Čech nerve.
Source: Stacks Project, Tags 01GC and 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
noncomputable abbrev presheafCechSheafComplex
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v)) :
    ChainComplex (Sheaf J AddCommGrpCat.{v}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ presheafCechFreeSheafFunctor J)

/-- An exact syzygy ladder for the actual sheafified free Čech chain complex.
The maps factor its differentials; the initial augmentation is the original map,
under the degree-zero identification. All data and proofs are explicit fields.
Source: Stacks Project, Tag 079Z, augmented free nerve argument.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
structure PresheafCechSheafResolution
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v)) where
  K : ℕ → Sheaf J AddCommGrpCat.{v}
  i : ∀ n, K n ⟶ (presheafCechSheafComplex J f).X n
  p : ∀ n, (presheafCechSheafComplex J f).X (n + 1) ⟶ K n
  e₀ : (presheafCechSheafComplex J f).X 0 ≅
    (presheafCechFreeSheafFunctor J).obj f.left
  initial_zero : i 0 ≫ (e₀.hom ≫ (presheafCechFreeSheafFunctor J).map f.hom) = 0
  initial_exact : (ShortComplex.mk (i 0)
    (e₀.hom ≫ (presheafCechFreeSheafFunctor J).map f.hom) initial_zero).ShortExact
  zero : ∀ n, i (n + 1) ≫ p n = 0
  exact : ∀ n, (ShortComplex.mk (i (n + 1)) (p n) (zero n)).ShortExact
  differential : ∀ n, p n ≫ i n = (presheafCechSheafComplex J f).d (n + 1) n

/-- A locally surjective presheaf map has an exact augmented sheafified free nerve.
Source: Stacks Project, Hypercoverings, Tag 01GC, and Cohomology on Sites, Tag 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution)

Proof: evaluate the free presheaf chain complex objectwise. Replace the target
set by the image of the evaluated map; this does not change the nerve. Choose
one vertex in every nonempty fibre and prefix it to tuples. The alternating
faces give a contraction, so the free presheaf chain complex is exact in positive
degrees and its degree-zero cokernel is the free abelian presheaf on the image.
Sheafification is exact. Local surjectivity identifies the sheafification of
that image with the sheafification of the target, so the augmented sheaf complex
is exact also at degree zero and the augmentation is epic. Identify the zeroth
nerve term with the source presheaf to obtain e₀. Take K₀ to be the kernel of
the augmentation and Kₙ₊₁ to be the kernel of the map onto Kₙ. Exactness factors
each differential as an epimorphism pₙ followed by the kernel inclusion iₙ;
these maps give the asserted short exact sequences and differential identities.
The kernel universal properties determine all chosen syzygies up to unique iso.
-/
theorem exists_presheafCechSheafResolution
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) :
    Nonempty (PresheafCechSheafResolution (J := J) f) := by
  let F := presheafCechFreeSheafFunctor J
  let A := presheafCechSheafComplex J f
  let ε : A.X 0 ⟶ F.obj f.right :=
    F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))
  obtain ⟨hε, hex, hepi⟩ := presheafCechSheaf_augmentation_exact f hf
  have hpos := presheafCechSheaf_positive_exact J f
  let B : ℕ → Sheaf J AddCommGrpCat.{v}
    | 0 => F.obj f.right
    | n + 1 => A.X n
  let g : ∀ n, A.X n ⟶ B n
    | 0 => ε
    | n + 1 => A.d (n + 1) n
  have hz : ∀ n, A.d (n + 1) n ≫ g n = 0 := by
    intro n
    cases n with
    | zero => exact hε
    | succ n => exact A.d_comp_d _ _ _
  let S : ℕ → ShortComplex (Sheaf J AddCommGrpCat.{v}) := fun n ↦
    ShortComplex.mk (A.d (n + 1) n) (g n) (hz n)
  have hS : ∀ n, (S n).Exact := by
    intro n
    cases n with
    | zero => exact hex
    | succ n =>
      exact (HomologicalComplex.exactAt_iff' A (n + 2) (n + 1) n
        (by simp) (by simp)).1 (hpos n)
  let K := fun n ↦ (S n).cycles
  let i : ∀ n, K n ⟶ A.X n := fun n ↦ (S n).iCycles
  let p : ∀ n, A.X (n + 1) ⟶ K n := fun n ↦ (S n).toCycles
  have hi : ∀ n, Mono (i n) := fun n ↦ inferInstanceAs (Mono (S n).iCycles)
  have hp : ∀ n, Epi (p n) := fun n ↦ (hS n).epi_toCycles
  have hd : ∀ n, p n ≫ i n = A.d (n + 1) n := fun n ↦ (S n).toCycles_i
  have hzero : ∀ n, i (n + 1) ≫ p n = 0 := by
    intro n
    apply (cancel_mono (i n)).1
    rw [Category.assoc, hd, zero_comp]
    exact (S (n + 1)).iCycles_g
  have hshort : ∀ n, (ShortComplex.mk (i (n + 1)) (p n) (hzero n)).ShortExact := by
    intro n
    let T := ShortComplex.mk (i (n + 1)) (p n) (hzero n)
    let U := ShortComplex.mk (i (n + 1)) (A.d (n + 1) n)
      ((S (n + 1)).iCycles_g)
    let φ : T ⟶ U := ShortComplex.homMk (𝟙 _) (𝟙 _) (i n)
      (by dsimp [T, U]; simp) (by dsimp [T, U]; simpa using (hd n).symm)
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono φ.τ₃ := hi n
    refine ShortComplex.ShortExact.mk' ?_ (hi (n + 1)) (hp n)
    apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    exact U.exact_of_f_is_kernel (S (n + 1)).cyclesIsKernel
  let e : f.cechNerve.obj (Opposite.op (SimplexCategory.mk 0)) ≅ f.left :=
    { hom := WidePullback.π (fun _ : Fin 1 ↦ f.hom) 0
      inv := WidePullback.lift f.hom (fun _ : Fin 1 ↦ 𝟙 f.left) (by simp)
      hom_inv_id := by
        apply WidePullback.hom_ext
        · intro j
          have hj : j = 0 := by
            apply Fin.ext
            have hj := j.isLt
            change j.val < 1 at hj
            change j.val = 0
            omega
          subst j
          simp [Category.assoc]
        · simp [Category.assoc]
      inv_hom_id := by simp }
  let e₀ : A.X 0 ≅ F.obj f.left := F.mapIso e
  have he₀ : e₀.hom ≫ F.map f.hom = ε := by
    change F.map e.hom ≫ F.map f.hom = ε
    rw [← F.map_comp]
    exact congrArg F.map (WidePullback.π_arrow _ 0)
  have hinitial : i 0 ≫ (e₀.hom ≫ F.map f.hom) = 0 := by
    rw [he₀]
    exact (S 0).iCycles_g
  refine ⟨⟨K, i, p, e₀, hinitial, ?_, hzero, hshort, hd⟩⟩
  have : Epi ε := hepi
  have : Epi (e₀.hom ≫ F.map f.hom) := by rwa [he₀]
  refine ShortComplex.ShortExact.mk' ?_ (hi 0) inferInstance
  let T := ShortComplex.mk (i 0) ε (S 0).iCycles_g
  have hT : T.Exact := T.exact_of_f_is_kernel (S 0).cyclesIsKernel
  let φ : (ShortComplex.mk (i 0) (e₀.hom ≫ F.map f.hom) hinitial) ≅ T :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [T]) (by dsimp [T]; simpa using he₀.symm)
  exact (ShortComplex.exact_iff_of_iso φ).2 hT

end CategoryTheory.Sheaf
