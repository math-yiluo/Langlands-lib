/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License 2.0; see licenses/Anthropic-FLT/LICENSE.
Adapted by Worker 344 from
P2M/Sol/S_Module_Grassmannian_adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq.lean
and its Theorems wrapper at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Changes: focused imports and ordinary namespaces; reuse the published chart
coordinate equivalence. See the paired Markdown.
-/
import Langlands.RingTheory.Grassmannian.Charts
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Generators of the coordinate algebra of a quotient-Grassmannian chart -/

open scoped TensorProduct
open TensorProduct CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Module.Grassmannian.ChartAlgebraGeneration

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ}

open Module.Grassmannian.ChartLinear (Chart HomX)

section chart

noncomputable abbrev ptx (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (k : ℕ) (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A] :
    Chart R x A ≃ HomX R x A :=
  ChartLinear.chartEquiv (R := R) (A := A) x

theorem sum_ptx_smul (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) (m : M) :
    ∑ i, (ptx R M k x A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
      N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m) :=
  by
    change ChartLinear.cmap x N.1.toSubmodule
      ((ChartLinear.coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m))) = _
    rw [← ChartLinear.coordEquiv_apply, LinearEquiv.apply_symm_apply]

theorem ptx_natural (x : Fin k → M) {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) (N : Chart R x A) :
    ∃ h : Function.Bijective fun v : Fin k → B =>
        ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
      ∀ (m : M) (i : Fin k),
        (ptx R M k x B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((ptx R M k x A N).1 m i) :=
  by
    refine ⟨ChartLinear.map_mem_chart x φ N, fun m i => ?_⟩
    exact congrArg (fun ψ : HomX R x B => ψ.1 m i) (ChartLinear.chartEquiv_map x φ N)

end chart

section algebra

variable (x : Fin k → M) {S : Type} [CommRing S] [Algebra R S] (N : Chart R x S)
  {ι : Type} (g : ι → M)

noncomputable def T : Subalgebra R S :=
  Algebra.adjoin R {s : S | ∃ (a : ι) (c : Fin k → S) (i : Fin k),
    ∑ j, c j • N.1.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x j) = N.1.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] g a) ∧ s = c i}

theorem ptx_g_mem (a : ι) (i : Fin k) : (ptx R M k x S N).1 (g a) i ∈ T x N g :=
  Algebra.subset_adjoin ⟨a, (ptx R M k x S N).1 (g a), i, sum_ptx_smul x N (g a), rfl⟩

theorem ptx_mem (hg : Submodule.span R (Set.range g) = ⊤) (m : M) (i : Fin k) :
    (ptx R M k x S N).1 m i ∈ T x N g := by
  have hm : m ∈ Submodule.span R (Set.range g) := by rw [hg]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨a, rfl⟩ := hm
    exact ptx_g_mem x N g a i
  | zero => rw [map_zero]; exact zero_mem _
  | add m m' _ _ hm hm' => rw [map_add]; exact add_mem hm hm'
  | smul r m _ hm =>
    rw [map_smul, Pi.smul_apply]
    exact Subalgebra.smul_mem _ hm r

noncomputable def ψT (hg : Submodule.span R (Set.range g) = ⊤) : M →ₗ[R] (Fin k → T x N g) where
  toFun m i := ⟨(ptx R M k x S N).1 m i, ptx_mem x N g hg m i⟩
  map_add' m m' := by
    funext i; apply Subtype.ext
    simp only [map_add, Pi.add_apply, Subalgebra.coe_add]
  map_smul' r m := by
    funext i; apply Subtype.ext
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Subalgebra.coe_smul]

theorem ψT_apply_val (hg : Submodule.span R (Set.range g) = ⊤) (m : M) (i : Fin k) :
    ((ψT x N g hg m i : T x N g) : S) = (ptx R M k x S N).1 m i := rfl

theorem ψT_x (hg : Submodule.span R (Set.range g) = ⊤) (j : Fin k) : ψT x N g hg (x j) = Pi.single j 1 := by
  funext i
  apply Subtype.ext
  rw [ψT_apply_val, (ptx R M k x S N).2 j, Pi.single_apply, Pi.single_apply]
  split_ifs <;> rfl

noncomputable def NT (hg : Submodule.span R (Set.range g) = ⊤) : Chart R x (T x N g) :=
  (ptx R M k x (T x N g)).symm ⟨ψT x N g hg, ψT_x x N g hg⟩

theorem map_val_NT (hg : Submodule.span R (Set.range g) = ⊤) :
    Module.Grassmannian.map (T x N g).val (NT x N g hg).1 = N.1 := by
  obtain ⟨h, hnat⟩ := ptx_natural x (T x N g).val (NT x N g hg)
  have key : (⟨Module.Grassmannian.map (T x N g).val (NT x N g hg).1, h⟩ : Chart R x S) = N := by
    apply (ptx R M k x S).injective
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    funext i
    rw [hnat m i]
    unfold NT
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg Subtype.val key

end algebra

end Module.Grassmannian.ChartAlgebraGeneration

open Module.Grassmannian.ChartLinear (Chart) in
open Module.Grassmannian.ChartAlgebraGeneration in
theorem Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens)
    (hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i))
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (x : Fin k → M) (S : Type) [CommRing S] [Algebra R S] (N : Module.Grassmannian S (S ⊗[R] M) k)
    [IsOpenImmersion (pt S N).1] (hN : (pt S N).1.opensRange = V x) :
    Algebra.adjoin R {s : S | ∃ (a : ι) (c : Fin k → S) (i : Fin k),
        ∑ j, c j • N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x j) = N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] g a) ∧
          s = c i} = ⊤ := by

  have hrange : Set.range (pt S N).1.base = (V x : Set Gr) := by
    rw [← hN]; rfl
  have hx : Function.Bijective fun v : Fin k → S => ∑ i, v i • N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x i) :=
    (hVchart x S N).mp hrange.le
  let Nc : Chart R x S := ⟨N, hx⟩
  change T x Nc g = ⊤

  set T' : Subalgebra R S := T x Nc g with hT'
  let NT' : Chart R x T' := NT x Nc g hg
  let t : Spec (CommRingCat.of T') ⟶ Gr := (pt T' NT'.1).1
  have ht : Set.range t.base ⊆ Set.range (pt S N).1.base := by
    rw [hrange]
    exact (hVchart x T' NT'.1).mpr NT'.2
  let l : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S) := IsOpenImmersion.lift (pt S N).1 t ht
  have hl : l ≫ (pt S N).1 = t := IsOpenImmersion.lift_fac _ _ _
  let σ : CommRingCat.of S ⟶ CommRingCat.of T' := Spec.preimage l
  have hσ : Spec.map σ = l := Spec.map_preimage l

  have hmap : Module.Grassmannian.map T'.val NT'.1 = N := map_val_NT x Nc g hg
  have hnat := hpt T' S T'.val NT'.1
  rw [hmap] at hnat

  have hcomp : Spec.map (σ ≫ CommRingCat.ofHom T'.val.toRingHom) ≫ (pt S N).1 = 𝟙 _ ≫ (pt S N).1 := by
    rw [Spec.map_comp, Category.assoc, hσ, hl, Category.id_comp]
    exact hnat.symm
  rw [cancel_mono] at hcomp
  rw [Spec.map_eq_id] at hcomp

  rw [eq_top_iff]
  intro s _
  have hs : (T'.val) (σ.hom s) = s := by
    have := congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of S => f.hom s) hcomp
    simpa using this
  rw [← hs]
  exact (σ.hom s).2
