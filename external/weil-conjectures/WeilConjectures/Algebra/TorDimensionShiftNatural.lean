/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Dimension shifting for Tor

Source: literature/stacks-project/algebra.tex, Tags 00LY, 00LZ, 00M0, 00S2
(blueprint: lem-sc-p1-tor-dimension-shift-natural).
-/

@[expose] public section

universe u

namespace CategoryTheory

noncomputable section Helpers

-- Splice a projective resolution of the kernel onto the free presentation.
private def spliceX {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) :
    ℕ → ModuleCat.{u} R
  | 0 => S.X₂
  | n + 1 => Q.complex.X n

private def spliceD {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) :
    ∀ n, spliceX S Q (n + 1) ⟶ spliceX S Q n
  | 0 => Q.π.f 0 ≫ S.f
  | n + 1 => Q.complex.d (n + 1) n

private lemma spliceD_sq {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) (n : ℕ) :
    spliceD S Q (n + 1) ≫ spliceD S Q n = 0 := by
  cases n with
  | zero => simp [spliceD, ← Category.assoc]
  | succ n => exact Q.complex.d_comp_d _ _ _

private def spliceComplex {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (spliceX S Q) (spliceD S Q) (spliceD_sq S Q)

private def spliceAugmentation {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) :
    spliceComplex S Q ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, by
    simp [spliceComplex, ChainComplex.of.d, spliceD, Category.assoc, S.zero]⟩

private lemma splice_exact_zero {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (Q : ProjectiveResolution S.X₁) :
    (ShortComplex.mk (Q.π.f 0 ≫ S.f) S.g (by simp [Category.assoc])).Exact := by
  let φ : ShortComplex.mk (Q.π.f 0 ≫ S.f) S.g (by simp [Category.assoc]) ⟶ S :=
    { τ₁ := Q.π.f 0
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS.exact

private lemma splice_exact_one {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (Q : ProjectiveResolution S.X₁) :
    (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0 ≫ S.f)
      (by simp [← Category.assoc])).Exact := by
  have : Mono S.f := hS.mono_f
  let φ : ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0)
      Q.complex_d_comp_π_f_zero ⟶
      ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0 ≫ S.f)
        (by simp [← Category.assoc]) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := S.f }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 Q.exact₀

private def spliceResolution {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (Q : ProjectiveResolution S.X₁) :
    ProjectiveResolution S.X₃ where
  complex := spliceComplex S Q
  projective n := by
    cases n with
    | zero => change Projective S.X₂; infer_instance
    | succ n => exact Q.projective n
  π := spliceAugmentation S Q
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · have : Epi S.g := hS.epi_g
        simpa [HomologicalComplex.shortComplexFunctor', spliceComplex,
          ChainComplex.of.d, spliceD, spliceAugmentation, spliceX,
          ChainComplex.toSingle₀Equiv] using
          (show (ShortComplex.mk (Q.π.f 0 ≫ S.f) S.g
            (by simp [Category.assoc])).Exact ∧ Epi S.g from
            ⟨splice_exact_zero S hS Q, inferInstance⟩)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
        cases n with
        | zero => simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
            spliceComplex, ChainComplex.of.d, spliceD, spliceX, Nat.add_assoc]
            using splice_exact_one S hS Q
        | succ n => simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
            spliceComplex, ChainComplex.of.d, spliceD, spliceX, Nat.add_assoc]
            using Q.exact_succ n
      · apply ChainComplex.exactAt_succ_single_obj⟩

-- Keep tensoring functorial in the coefficient module before taking homology.
private def tensorComplex {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj N :=
    (((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj N).mapHomologicalComplex _).obj K
  map g := (NatTrans.mapHomologicalComplex
    ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).map g) _).app K
  map_id N := by
    simp only [Functor.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp g h := by
    simp only [Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

private def torResolutionIso {R : Type u} [CommRing R] {X : ModuleCat.{u} R}
    (Q : ProjectiveResolution X) (i : ℕ) :
    (Tor' (ModuleCat.{u} R) i).obj X ≅
      tensorComplex Q.complex ⋙ HomologicalComplex.homologyFunctor _ _ i :=
  NatIso.ofComponents
    (fun N ↦ Q.isoLeftDerivedObj
      ((MonoidalCategory.tensoringRight (ModuleCat.{u} R)).obj N) i)
    (fun g ↦ by
      dsimp [tensorComplex]
      rw [Tor'_obj_map, Q.leftDerived_app_eq]
      simp)

-- The three terms determining positive-degree homology agree literally.
private def spliceScIso {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) (n : ℕ) :
    tensorComplex (spliceComplex S Q) ⋙
        HomologicalComplex.shortComplexFunctor' _ _ (n + 3) (n + 2) (n + 1) ≅
      tensorComplex Q.complex ⋙
        HomologicalComplex.shortComplexFunctor' _ _ (n + 2) (n + 1) n :=
  NatIso.ofComponents (fun N ↦
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [tensorComplex, spliceComplex, ChainComplex.of.d, spliceD,
        spliceX, Nat.add_assoc])
      (by simp [tensorComplex, spliceComplex, ChainComplex.of.d, spliceD,
        spliceX, Nat.add_assoc]))
    (fun g ↦ by ext <;> simp [tensorComplex, spliceComplex, spliceX])

private def spliceHomologyIso {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (Q : ProjectiveResolution S.X₁) (n : ℕ) :
    tensorComplex (spliceComplex S Q) ⋙
        HomologicalComplex.homologyFunctor _ _ (n + 2) ≅
      tensorComplex Q.complex ⋙ HomologicalComplex.homologyFunctor _ _ (n + 1) :=
  Functor.isoWhiskerLeft _
      (HomologicalComplex.homologyFunctorIso' _ _ (n + 3) (n + 2) (n + 1)
        (by simp [ComplexShape.prev, Nat.add_assoc]) (by simp)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spliceScIso S Q n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _
      (HomologicalComplex.homologyFunctorIso' _ _ (n + 2) (n + 1) n
        (by simp [ComplexShape.prev, Nat.add_assoc]) (by simp))).symm

end Helpers

/-- Dimension shifting for Tor along a free presentation, natural in the second variable.
Source: literature/stacks-project/algebra.tex, Tags 00LY, 00LZ, 00M0, 00S2
(blueprint: lem-sc-p1-tor-dimension-shift-natural).

Step 1. Fix Mathlib's projective resolution `G` of `K = S.X₁`, independently
of the second module `N`. Projective resolutions suffice to compute Tor.
Step 2. Splice it to the given short exact sequence: put `P₀ = F = S.X₂`,
`Pₙ₊₁ = Gₙ`, with first differential `jη` and augmentation `p` to `M = S.X₃`.
All terms are projective: `F` is free and the other terms come from `G`.
Exactness follows from
`image j = kernel p` and injectivity of `j` (def-weil-pbc-exact-sequence):
`image (jη) = kernel p` and `kernel (jη) = kernel η = image e₁`;
all higher degrees inherit exactness from `G`.
Step 3. Compute Tor using these resolutions (def-weil-pbc-tor-modules).
For `i ≥ 1`, the three terms around degree `i+1` of `P ⊗ N` are
`Gᵢ₊₁ ⊗ N → Gᵢ ⊗ N → Gᵢ₋₁ ⊗ N`, with the same differentials as in `G ⊗ N`.
The identity on `Gᵢ ⊗ N` induces the desired quotient-of-cycles isomorphism.
Compose with the canonical resolution identifications to obtain `θ N`.
Step 4. For a map `g : N → N'`, the maps `1 ⊗ g` at these three terms coincide
in both complexes. They preserve cycles and boundaries, so the quotient isomorphism
commutes with the induced homology maps. The canonical identifications are functorial
(def-weil-pbc-tor-modules), giving the displayed naturality equation.
-/
theorem tor_dimension_shift_natural
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (i : ℕ) (hi : 1 ≤ i) :
    ∃ θ : ∀ N : ModuleCat.{u} R,
      (((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N),
      ∀ (N N' : ModuleCat.{u} R) (g : N ⟶ N'),
        ((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).map g ≫ (θ N').hom =
          (θ N).hom ≫ ((Tor' (ModuleCat.{u} R) i).obj S.X₁).map g := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  let Q := projectiveResolution S.X₁
  let P := spliceResolution S hS Q
  let e : (Tor' (ModuleCat.{u} R) (n + 1 + 1)).obj S.X₃ ≅
      (Tor' (ModuleCat.{u} R) (n + 1)).obj S.X₁ :=
    torResolutionIso P (n + 2) ≪≫ spliceHomologyIso S Q n ≪≫
      (torResolutionIso Q (n + 1)).symm
  exact ⟨fun N ↦ e.app N, fun N N' g ↦ e.hom.naturality g⟩

end CategoryTheory
