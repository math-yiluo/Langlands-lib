/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantProjectionMaps
import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentation.CompletedConstantCompletionRightExact
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRankOneComparison
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Invertibility of the canonical finite-module comparison

Source: Stacks Project, More on Algebra, Tag 0912, and Modules on Sites, Tags 093J--093M.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem isIso_on_finite_free
    {R : Type (u + 1)} [CommRing R]
    {D : Type*} [Category D] [Preadditive D]
    (F G : ModuleCat.{u + 1} R ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
    [IsIso (α.app (ModuleCat.of R R))] (n : ℕ) :
    IsIso (α.app (ModuleCat.of R (Fin n → R))) := by
  classical
  let P := ModuleCat.of R (Fin n → R)
  let p (i : Fin n) : P ⟶ ModuleCat.of R R := ModuleCat.ofHom (LinearMap.proj i)
  let q (i : Fin n) : ModuleCat.of R R ⟶ P :=
    ModuleCat.ofHom (LinearMap.single R (fun _ : Fin n ↦ R) i)
  have htotal : ∑ i, p i ≫ q i = 𝟙 P := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    ext j
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    change (∑ i : Fin n, Pi.single i (x i)) j = x j
    simp [Finset.sum_apply, Pi.single_apply]
  let β : G.obj P ⟶ F.obj P :=
    ∑ i, G.map (p i) ≫ inv (α.app (ModuleCat.of R R)) ≫ F.map (q i)
  have hleft : α.app P ≫ β = 𝟙 _ := by
    dsimp only [β]
    rw [Preadditive.comp_sum]
    calc
      _ = ∑ i, F.map (p i) ≫ F.map (q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Category.assoc, ← α.naturality, Category.assoc,
          IsIso.hom_inv_id_assoc]
      _ = F.map (∑ i, p i ≫ q i) := by simp only [Functor.map_sum, Functor.map_comp]
      _ = 𝟙 _ := by rw [htotal, F.map_id]
  have hright : β ≫ α.app P = 𝟙 _ := by
    dsimp only [β]
    rw [Preadditive.sum_comp]
    calc
      _ = ∑ i, G.map (p i) ≫ G.map (q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Category.assoc]
        rw [α.naturality, IsIso.inv_hom_id_assoc]
      _ = G.map (∑ i, p i ≫ q i) := by simp only [Functor.map_sum, Functor.map_comp]
      _ = 𝟙 _ := by rw [htotal, G.map_id]
  exact ⟨⟨β, hleft, hright⟩⟩

/-- The already constructed tensor-to-limit map is invertible for finite modules.
Source: Stacks Project, More on Algebra, Tag 0912 (lemma-limit-flat), and Modules on
Sites, Tags 093J--093M (lemma-constant-exact, lemma-tensor-with-finitely-presented,
lemma-flat-sections, lemma-completion-flat).
(blueprint: lem-weil-pbc-completed-constant-comparison-is-iso).

Proof: put C = AdicCompletion I A and J = IC. The Noetherian completion theorem makes
C Noetherian; its evaluation maps identify C/J^(n+1) with A/I^(n+1), preserving transitions.
For any C-module N, J^k N = I^k N after restriction to A: multiplication by elements of C
can be absorbed into the module factor. In particular the quotient towers agree.
For finite N, choose a finite presentation over C. On each site object U the sections of
the constant quotient rings are flat over their quotient rings, and have surjective
transition maps by exactness of constant sections. Tag 0912 therefore identifies
N tensor_C H(U) with the compatible families in N tensor_C constant(C/J^(n+1))(U).
Tag 093K identifies the factors with the sections of constant(N/J^(n+1)N), using the
finite presentation. Every map used sends a pure tensor h tensor x to the product of
the projected h with residue(x). They commute with restrictions. Locally every section
of constant N is represented by an actual element, so sheafifying sectionwise scalar
extension gives the same map from H tensor_(constant C) constant N. Its finite
projections agree with completedConstantProjection by their pure-tensor formula and
local tensor generation. Hence the resulting invertible map is precisely the fixed
completedConstantComparisonMap. The argument includes N = 0, the zero ring, I = 0
and I = top; all presentations and quotient diagrams retain those cases. -/
theorem completedConstantComparisonMap_isIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (N : ModuleCat.{u + 1} (AdicCompletion I A))
    (_hN : Module.Finite (AdicCompletion I A) N) :
    IsIso (completedConstantComparisonMap X I φ hφ N) := by
  let C := AdicCompletion I A
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing I
  have : Module.Finite C N := _hN
  have : Module.FinitePresentation C N := Module.finitePresentation_of_finite C N
  let F := CompletedConstantPresentation.realization X I φ
  let G := CompletedConstantPresentation.completion X I
  let α : F ⟶ G := CompletedConstantPresentation.comparison X I φ hφ
  have : IsIso (α.app (ModuleCat.of C C)) :=
    completedConstantComparisonMap_rankOne_isIso X I φ hφ
  have hfrees (n : ℕ) : IsIso (α.app (ModuleCat.of C (Fin n → C))) :=
    isIso_on_finite_free F G α n
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' C N
  let S : ShortComplex (ModuleCat.{u + 1} C) :=
    ShortComplex.moduleCatMk f g hfg.linearMap_comp_eq_zero
  have hS : S.Exact := ModuleCat.shortComplex_exact S hfg
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hg
  have : PreservesFiniteColimits F :=
    CompletedConstantPresentation.realization_preservesFiniteColimits X I φ
  have : Module.Finite C S.X₁ := by
    change Module.Finite C (Fin m → C)
    infer_instance
  have : Module.Finite C S.X₂ := by
    change Module.Finite C (Fin n → C)
    infer_instance
  have : PreservesColimit (parallelPair S.f 0) G :=
    CompletedConstantPresentation.completion_preservesCokernel X I S.f
  have hα : ∀ j : WalkingParallelPair,
      IsIso ((Functor.whiskerLeft (parallelPair S.f 0) α).app j) := by
    intro j
    cases j
    · exact hfrees m
    · exact hfrees n
  have : IsIso (Functor.whiskerLeft (parallelPair S.f 0) α) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit (parallelPair S.f 0) α
    (CokernelCofork.ofπ S.g S.zero) hS.gIsCokernel

end AlgebraicGeometry.Scheme
