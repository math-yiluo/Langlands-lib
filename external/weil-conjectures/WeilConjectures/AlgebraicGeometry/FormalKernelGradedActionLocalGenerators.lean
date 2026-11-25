/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Local degree-zero generators for the kernel action

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable local instance restrictedSectionModule {X : Scheme.{u}}
    (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    Module Γ(X, U)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i.op).hom).obj
        (M.val.obj (op U))) :=
  inferInstanceAs (Module Γ(X, U) (M.val.obj (op U)))

-- Iterate the error term until the annihilating ideal power makes it vanish.
private theorem span_eq_top_of_nilpotent_error {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] (J : Ideal R) (L : Submodule R N)
    (h : L ⊔ J • ⊤ = ⊤) (k : ℕ) (hk : J ^ k • (⊤ : Submodule R N) = ⊥) :
    L = ⊤ := by
  have hp : ∀ n : ℕ, L ⊔ J ^ n • ⊤ = ⊤ := by
    intro n
    induction n with
    | zero => simp [Ideal.one_eq_top]
    | succ n ih =>
      calc
        L ⊔ J ^ (n + 1) • ⊤ = L ⊔ J ^ n • (J • ⊤) := by
          rw [pow_succ, Submodule.mul_smul]
        _ = L ⊔ J ^ n • (L ⊔ J • ⊤) := by
          rw [Submodule.smul_sup, ← sup_assoc,
            sup_of_le_left (Submodule.smul_le_right (I := J ^ n) (N := L))]
        _ = ⊤ := by rw [h]; exact ih
  simpa [hk] using hp k

-- Lift the generators one level at a time; the transition kernel is an ideal error.
private theorem adic_lifts_span {R : Type u} [CommRing R] (J : Ideal R)
    (T : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hz : ∀ n : ℕ, J ^ (n + 1) • (⊤ : Submodule R (T.obj (op n))) = ⊥)
    (ht : ∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        J ^ (n + 1) • (⊤ : Submodule R (T.obj (op (n + 1)))))
    (r : ℕ) (s : Fin r → T.obj (op 0))
    (hs : Submodule.span R (Set.range s) = ⊤) (n : ℕ) :
    ∃ x : Fin r → T.obj (op n),
      (∀ i, T.map (homOfLE (Nat.zero_le n)).op (x i) = s i) ∧
      Submodule.span R (Set.range x) = ⊤ := by
  classical
  induction n with
  | zero =>
    refine ⟨s, ?_, hs⟩
    intro i
    have he : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) := Subsingleton.elim _ _
    rw [he, T.map_id]
    rfl
  | succ n ih =>
    obtain ⟨x, hx, hspan⟩ := ih
    choose y hy using fun i ↦ (ht n).1 (x i)
    let f := (T.map (homOfLE (Nat.le_succ n)).op).hom
    have hcomp (i : Fin r) :
        T.map (homOfLE (Nat.zero_le (n + 1))).op (y i) = s i := by
      have he : (homOfLE (Nat.zero_le (n + 1))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (Nat.zero_le n)).op :=
        Subsingleton.elim _ _
      rw [he, T.map_comp]
      change T.map (homOfLE (Nat.zero_le n)).op
        (T.map (homOfLE (Nat.le_succ n)).op (y i)) = _
      rw [hy, hx]
    refine ⟨y, hcomp, ?_⟩
    let L := Submodule.span R (Set.range y)
    have hm : L.map f = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp]
      have heq : f ∘ y = x := funext hy
      rw [heq]
      exact hspan
    have hsup : L ⊔ LinearMap.ker f = ⊤ := by
      rw [← Submodule.comap_map_eq, hm]
      exact Submodule.comap_top f
    apply span_eq_top_of_nilpotent_error J L _ (n + 2) (hz (n + 1))
    apply top_unique
    conv_lhs => rw [← hsup]
    have hj : J ^ (n + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hk : LinearMap.ker f ≤ J • (⊤ : Submodule R (T.obj (op (n + 1)))) := by
      rw [(ht n).2]
      exact Submodule.smul_mono_left hj
    exact sup_le_sup_left hk L

-- The affine base-change formula carries the spanning family to a smaller affine open.
private theorem affine_restriction_span {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] (U W : X.affineOpens) (hWU : W.1 ≤ U.1)
    (r : ℕ) (s : Fin r → Γ(G, U.1))
    (hs : Submodule.span Γ(X, U.1) (Set.range s) = ⊤) :
    Submodule.span Γ(X, W.1)
      (Set.range fun i ↦ G.val.map (homOfLE hWU).op (s i)) = ⊤ := by
  let ρ := (X.presheaf.map (homOfLE hWU).op).hom
  let : Algebra Γ(X, U.1) Γ(X, W.1) := ρ.toAlgebra
  let : Module Γ(X, U.1) Γ(G, W.1) := Module.compHom _ ρ
  obtain ⟨c, hc, _, ht⟩ :=
    Scheme.Modules.quasiCoherent_affine_section_baseChange X G W U hWU
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨q, rfl⟩ := hc.2 z
  induction q using TensorProduct.inductionOn with
  | tmul x b =>
    rw [ht]
    apply Submodule.smul_mem
    have hx : x ∈ Submodule.span Γ(X, U.1) (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (Set.mem_range_self i)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      change G.val.map (homOfLE hWU).op (a • x) ∈ _
      rw [G.val.map_smul]
      exact Submodule.smul_mem _ _ hx
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- A kernel action with the representative formula in module degree zero is locally
finitely generated in degree zero.
Source: Stacks Project, Lemma 087Z, affine finite-generation argument via Lemma 087W;
https://stacks.math.columbia.edu/tag/087Z and https://stacks.math.columbia.edu/tag/087W.
(blueprint: lem-weil-pbc-formal-kernel-graded-action-local-generators).

Proof: Choose an affine neighbourhood U of the given point. Restrict the coherent
formal system to U, and apply coherentFormalModules_affine to obtain its finite
completion module N with projections having kernels I^(r+1)N. The tilde/global
sections adjunction and the ideal-power and quotient affine-sections formulas
identify B_n and K_n on U with the sheaves of I^n/I^(n+1) and I^n N/I^(n+1)N.
In particular K_0 is N/IN. Choose a finite family generating N/IN, and lift it to N;
its quotient classes give sections s of K_0 on U. The completed-module associated
graded generator theorem says that every class in I^n N/I^(n+1)N is a sum of
classes of a_i times those fixed lifted generators, with a_i in I^n. Under the
identifications, hact identifies each such product with M.act n 0 of the coefficient
class and s_i: apply hact to the projection of the fixed lift to F_(n+1).
Thus the finite sum of these degree-n action maps is an epimorphism on U. Tilde,
a left adjoint, preserves the relevant quotient epimorphisms. On any smaller open
V and any q in V, local surjectivity of this sheaf epimorphism supplies an open
W inside V containing q and coefficient sections a_i of B_n on W expressing the
restriction of y. This is exactly IsLocallyGeneratedInDegreeZero, including its
HEq for n+0=n. No global lift on V or generating family on X is required.
For n=0 the same quotient-generator argument applies. For the zero module use an
empty family. If I is the unit ideal, every formal term is zero by annihilation;
if I=0, all positive kernel degrees vanish. Empty schemes have no points to check.
Only the action formula with module degree zero is used; no formula in positive
module degree, nor a new construction of A or M, is needed. -/
theorem formalKernel_graded_action_local_generators {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (A : GradedSheafAlgebra (formalAssociatedGradedPiece I))
    (M : GradedSheafModule A (formalKernelPiece F))
    (hact : ∀ (n : ℕ) (U : X.Opens)
      (a : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U))
      (s : (formalKernelPiece F 0).val.obj (op U))
      (t : (F.obj.obj (op n)).val.obj (op U)),
      (F.obj.map (homOfLE (Nat.zero_le n)).op).val.app (op U) t =
        (formalKernelι F 0).val.app (op U) s →
      (formalKernelι F n).val.app (op U)
        (M.act n 0 U ((formalAssociatedGradedπ I n).val.app (op U) a) s) =
          (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) a)) • t) :
    M.IsLocallyGeneratedInDegreeZero := by
  classical
  have hqc (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      X (F.obj.obj (op n))).mp (F.property.1 n)).1
  intro p
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := p) (show p ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).2
  have hUadic := coherentFormalModule_affine_open_sections_adic X I F ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(F.obj.obj (op 0), U) := hUadic.1 0
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := Γ(X, U))
    (M := Γ(F.obj.obj (op 0), U))
  refine ⟨U, hpU, r, s, ?_⟩
  intro V hVU n y q hq
  obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := q) hq V.2
  let hWU : W ≤ U := hWV.trans hVU
  let sW : Fin r → Γ(F.obj.obj (op 0), W) :=
    fun i ↦ (F.obj.obj (op 0)).val.map (homOfLE hWU).op (s i)
  have hsW : Submodule.span Γ(X, W) (Set.range sW) = ⊤ :=
    affine_restriction_span (F.obj.obj (op 0)) ⟨U, hU⟩ ⟨W, hW⟩ hWU r s hs
  let T := F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op W)
  have hWadic := coherentFormalModule_affine_open_sections_adic X I F ⟨W, hW⟩
  obtain ⟨x, hx, hspan⟩ :=
    adic_lifts_span (I.ideal ⟨W, hW⟩) T hWadic.2.1 hWadic.2.2 r sW hsW n
  let yW := (formalKernelPiece F n).val.map (homOfLE hWV).op y
  let v := (formalKernelι F n).val.app (op W) yW
  have hv : v ∈ I.ideal ⟨W, hW⟩ ^ n •
      (⊤ : Submodule Γ(X, W) (T.obj (op n))) := by
    cases n with
    | zero => simp [Ideal.one_eq_top]
    | succ m =>
      rw [← (hWadic.2.2 m).2]
      change (T.map (homOfLE (Nat.le_succ m)).op) v = 0
      have hk := congrArg (fun f ↦ f.val.app (op W) yW)
        (kernel.condition (F.obj.map (homOfLE (Nat.le_succ m)).op))
      exact hk
  rw [← hspan] at hv
  obtain ⟨c, hc, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum _ x v).mp hv
  have hsum' : ∑ i : Fin r, c i • x i = v := by
    rw [Finsupp.sum_fintype c (fun i a ↦ a • x i) (fun i ↦ zero_smul _ (x i))] at hsum
    exact hsum
  have hrange : ∀ i : Fin r, ∃ a :
      (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op W),
      (Scheme.idealSheafPower I.toModulesι n).2.val.app (op W) a = c i := by
    intro i
    cases n with
    | zero => exact ⟨c i, rfl⟩
    | succ m =>
      have hh := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
        (F.obj.obj (op 0))).2.2.2.1 ⟨W, hW⟩).2.2.2 (m + 1) (Nat.succ_pos m)
      exact (Set.ext_iff.mp hh (c i)).mpr (hc i)
  choose a ha using hrange
  refine ⟨W, hWV, hqW, fun i ↦ (formalAssociatedGradedπ I n).val.app (op W) (a i), ?_⟩
  have hinj : Function.Injective ((formalKernelι F n).val.app (op W)) := by
    cases n with
    | zero => exact Function.injective_id
    | succ m => exact Scheme.Modules.injective_map_kernelι W _
  apply heq_of_eq
  apply hinj
  rw [map_sum]
  calc
    v = ∑ i : Fin r, c i • x i := hsum'.symm
    _ = ∑ i : Fin r, (formalKernelι F n).val.app (op W)
        (M.act n 0 W ((formalAssociatedGradedπ I n).val.app (op W) (a i))
          ((formalKernelPiece F 0).val.map
            (homOfLE (le_trans hWV hVU)).op (s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      change c i • x i = (formalKernelι F n).val.app (op W)
        (M.act n 0 W ((formalAssociatedGradedπ I n).val.app (op W) (a i)) (sW i))
      simpa only [ha i, id_eq] using (hact n W (a i) (sW i) (x i) (hx i)).symm


end AlgebraicGeometry
