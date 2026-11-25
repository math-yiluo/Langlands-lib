/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Eventual generation from a finite affine section cover

Source: EGA II, proof of Proposition 4.5.5, local-generator extension paragraphs;
Stacks Project, Properties, Proposition 01Q3, (1) ⇒ (5).
(blueprint: lem-weil-pbc-affine-section-cover-twist-generation).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem eqToHom_app_tmul_tensorPow {X : Scheme.{u}} (G M : X.Modules)
    (s : 𝟙_ X.Modules ⟶ M) {m n : ℕ} (h : m = n) (U : X.Opens) (t : Γ(G, U)) :
    (eqToHom (congrArg (fun a ↦ G ⊗ M.tensorPow a) h)).app U
      (tmulSection t (tensorPowSectionOne s m U)) =
        tmulSection t (tensorPowSectionOne s n U) := by
  cases h
  rfl

/-- A finite affine cover by section loci of one invertible module gives finite global
 generators for all sufficiently large powers of that module, after tensoring with a
 finite type quasi-coherent module. No ampleness assumption or residue argument is used.

Source: EGA II, proof of Proposition 4.5.5, paragraphs extending the local generators;
Stacks Project, Properties, Proposition 01Q3, (1) ⇒ (5), using Lemma 01PW.
(blueprint: lem-weil-pbc-affine-section-cover-twist-generation).

Proof:
1. Restrict G to the affine opens U_i = X minus the support of the zero locus of s_i.
   Finite type and quasi-coherence restrict to opens. The affine finite-generator
   theorem gives finitely many sections t_ij generating G on each U_i.
2. Apply clearing denominators (01PW) on the compact separated scheme X to each t_ij:
   obtain an exponent a_ij and a global section of G tensor M^a_ij whose restriction
   is t_ij tensor s_i^a_ij. Take K to be the maximum of these finitely many exponents,
   taking zero when there are no generators.
3. For k >= K multiply each lifted section by s_i^(k-a_ij), using the tensor-power
   addition isomorphism. The resulting global sections of G tensor M^k restrict to
   t_ij tensor s_i^k. On U_i the section s_i freely generates M, and every tensor
   power of this free generator freely generates M^k (including k = 0).
4. Tensoring by that generator identifies G|U_i with (G tensor M^k)|U_i, so these
   restrictions generate on U_i. The finite union of all the lifted sections gives
   an evaluation map from a finite free sheaf. On each U_i its image contains the
   generating family indexed by i, hence it is locally surjective. Since the U_i
   cover X, the evaluation map is epi, giving a finite GeneratingSections family.
   The empty scheme and zero module cause no exception: the empty family is epi. -/
theorem exists_finite_generatingSections_tensorPow_of_affine_section_cover
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (M G : X.Modules) [M.IsInvertible] [G.IsQuasicoherent] [G.IsFiniteType]
    {I : Type u} [Finite I] (s : I → (𝟙_ X.Modules ⟶ M))
    (haff : ∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl)
    (hcover : (⨆ i, (Hom.zeroLocus (s i)).support.compl) = ⊤) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ σ : (tensorObj G (M.tensorPow k)).GeneratingSections, σ.IsFiniteType := by
  classical
  -- Finite local generators on the section opens.
  let U : I → X.Opens := fun i ↦ (Hom.zeroLocus (s i)).support.compl
  have hfin (i : I) : Module.Finite Γ(X, U i) Γ(G, U i) :=
    finite_sections_of_finiteType G (haff i)
  choose r t ht using fun i ↦ (hfin i).exists_fin
  let J := Σ i : I, ULift.{u} (Fin (r i))
  have : Fintype J := Fintype.ofFinite J
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    IsInvertible.sheafOfModules_isInvertible M
  -- Clear all denominators and take one bound, including the empty-family case.
  choose a v hv using fun j : J ↦
    exists_tensorPowSection_eq_restrict (Limits.terminal.from X) M (s j.1) G (t j.1 j.2.down)
  let K := Finset.univ.sup a
  have ha (j : J) : a j ≤ K := Finset.le_sup (Finset.mem_univ j)
  refine ⟨K, fun k hk ↦ ?_⟩
  have hpower (j : J) : a j + (k - a j) = k :=
    Nat.add_sub_of_le ((ha j).trans hk)
  -- Multiply each lift to degree k and transport the equality of degrees.
  let w (j : J) : Γ(G ⊗ M.tensorPow k, ⊤) :=
    (eqToHom (congrArg (fun n ↦ G ⊗ M.tensorPow n) (hpower j))).app ⊤
      ((mulTensorPowSection (s j.1) G (a j) (k - a j)).app ⊤ (v j))
  have hw (j : J) : (G ⊗ M.tensorPow k).presheaf.map (homOfLE le_top).op (w j) =
      tmulSection (t j.1 j.2.down) (tensorPowSectionOne (s j.1) k (U j.1)) := by
    dsimp only [w]
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, hv,
      rightUnitor_inv_comp_whiskerLeft_app, mulTensorPowSection_app_tmulSection]
    exact eqToHom_app_tmul_tensorPow G M (s j.1) (hpower j) _ _
  -- Evaluate the global lifts on the free basis.
  let N := G ⊗ M.tensorPow k
  let z : J → N.sections := fun j ↦
    PresheafOfModules.sectionsMk
      (fun V ↦ N.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op (w j))
      (fun V W f ↦ by
        change N.presheaf.map f _ = _
        rw [← Functor.map_comp_apply]
        rfl)
  let P : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) J
  let bsec (j : J) (V : X.Opens) : Γ(P, V) :=
    (SheafOfModules.freeSection (R := X.ringCatSheaf) j).1 (.op V)
  let φ : P ⟶ N := N.freeHomEquiv.symm z
  have hφ (j : J) (V : X.Opens) :
      Hom.app φ V (bsec j V) =
        N.presheaf.map (homOfLE le_top).op (w j) :=
    congrArg (fun q : N.sections ↦ q.1 (.op V))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection z j)
  have : N.IsQuasicoherent := isQuasicoherent_tensorObj G (M.tensorPow k)
  -- On each affine open, tensoring with s_i^k carries the spanning family to
  -- the image of the evaluation map.
  have hE : Epi φ := by
    apply epi_of_surjective_app φ U haff hcover
    intro i y
    obtain ⟨x, hx⟩ := (isFreeGenerator_tensorPowSectionOne (s i)
      (isFreeGenerator_app_one_of_le (s i) le_rfl) k).bijective_tmulSection_right
        (M := G) le_rfl |>.2 y
    have hxspan : x ∈ Submodule.span Γ(X, U i) (Set.range (t i)) := by
      rw [ht i]
      trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxspan
    refine ⟨∑ b, c b • bsec ⟨i, ⟨b⟩⟩ (U i), ?_⟩
    rw [map_sum]
    simp only [Hom.app_smul, hφ]
    simp only [presheaf_map_id_apply] at hx
    rw [← hx]
    rw [tmulSection, TensorProduct.sum_tmul, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact (congrArg (fun q : Γ(N, U i) ↦ c b • q) (hw ⟨i, ⟨b⟩⟩)).trans
      (smul_tmulSection (c b) (t i b) (tensorPowSectionOne (s i) k (U i))).symm
  exact ⟨{ I := J, s := z, epi := hE }, ⟨inferInstanceAs (Finite J)⟩⟩

end AlgebraicGeometry.Scheme.Modules
