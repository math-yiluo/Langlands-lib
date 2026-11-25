/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Surjectivity of the change-of-rings map on first Tor

Source: Stacks Project, Algebra, Lemma Tag 00MN
(`literature/stacks-project/algebra.tex`, lemma-surjective-on-tor-one-trivial).
(blueprint: lem-weil-pbc-tor-one-surjective-change-rings)

The first homology of a tensor product of a free resolution is the Tor module
of `def-weil-pbc-tor-modules`, realized by Mathlib's `CategoryTheory.Tor'`.
Tensor associativity identifies `(A ⊗[R] F) ⊗[A] (A/J)` with
`F ⊗[R] (A/J)`, with symmetry exchanging the tensor factors. Thus the
homology map below is precisely the node's resolution-induced change-of-rings map.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

-- Only the right-exact augmented pair and the projective target in degrees 0 and 1
-- are needed. The partial right inverse becomes a right inverse modulo boundaries.
private theorem epi_homology_one_of_right_exact
    {C D : Type u} [Category C] [Category D] [Abelian C] [Abelian D]
    {N : C} (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ N)
    (hε : K.d 1 0 ≫ ε = 0) (he : (ShortComplex.mk _ _ hε).Exact) [Epi ε]
    (G : ProjectiveResolution N) (φ : K ⟶ G.complex)
    (hφ : φ.f 0 ≫ G.π.f 0 = ε) (T : C ⥤ D) [T.Additive] :
    Epi ((HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 1).map
      ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)) := by
  let b₀ : G.complex.X 0 ⟶ K.X 0 := Projective.factorThru (G.π.f 0) ε
  have hb₀ : b₀ ≫ ε = G.π.f 0 := Projective.factorThru_comp _ _
  have hbε : (G.complex.d 1 0 ≫ b₀) ≫ ε = 0 := by
    rw [Category.assoc, hb₀, G.complex_d_comp_π_f_zero]
  let b₁ : G.complex.X 1 ⟶ K.X 1 := he.liftFromProjective _ hbε
  have hb₁ : b₁ ≫ K.d 1 0 = G.complex.d 1 0 ≫ b₀ :=
    he.liftFromProjective_comp _ _
  have hsε : (b₀ ≫ φ.f 0 - 𝟙 _) ≫ G.π.f 0 = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc, hφ, hb₀, Category.id_comp, sub_self]
  let s₀ : G.complex.X 0 ⟶ G.complex.X 1 := G.exact₀.liftFromProjective _ hsε
  have hs₀ : s₀ ≫ G.complex.d 1 0 = b₀ ≫ φ.f 0 - 𝟙 _ :=
    G.exact₀.liftFromProjective_comp _ _
  have hsδ : (b₁ ≫ φ.f 1 - 𝟙 _ - G.complex.d 1 0 ≫ s₀) ≫
      G.complex.d 1 0 = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc, φ.comm,
      Category.id_comp, hs₀, Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc b₁, hb₁, Category.assoc]
    abel
  let s₁ : G.complex.X 1 ⟶ G.complex.X 2 := (G.exact_succ 0).liftFromProjective _ hsδ
  have hs₁ : s₁ ≫ G.complex.d 2 1 =
      b₁ ≫ φ.f 1 - 𝟙 _ - G.complex.d 1 0 ≫ s₀ :=
    (G.exact_succ 0).liftFromProjective_comp _ _
  let L := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let H := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj G.complex
  let ψ := (T.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  have hbm : T.map b₁ ≫ L.d 1 0 = H.d 1 0 ≫ T.map b₀ := by
    change T.map b₁ ≫ T.map (K.d 1 0) = T.map (G.complex.d 1 0) ≫ T.map b₀
    simp only [← T.map_comp, hb₁]
  have hcycle : (H.iCycles 1 ≫ T.map b₁) ≫ L.d 1 0 = 0 := by
    rw [Category.assoc, hbm, ← Category.assoc, H.iCycles_d, Limits.zero_comp]
  let z : H.cycles 1 ⟶ L.cycles 1 := L.liftCycles _ 0 (by simp) hcycle
  let t₀ : H.X 0 ⟶ H.X 1 := T.map s₀
  let t₁ : H.X 1 ⟶ H.X 2 := T.map s₁
  have hzm : z ≫ HomologicalComplex.cyclesMap ψ 1 =
      𝟙 _ + (H.iCycles 1 ≫ t₁) ≫ H.toCycles 2 1 := by
    rw [← cancel_mono (H.iCycles 1)]
    simp only [Preadditive.add_comp, Category.id_comp, Category.assoc,
      HomologicalComplex.toCycles_i]
    rw [HomologicalComplex.cyclesMap_i, ← Category.assoc]
    change (L.liftCycles _ 0 _ hcycle ≫ L.iCycles 1) ≫ T.map (φ.f 1) = _
    rw [HomologicalComplex.liftCycles_i]
    have hm := congrArg T.map hs₁
    simp only [T.map_comp, T.map_sub, T.map_id] at hm
    have hm' : T.map b₁ ≫ T.map (φ.f 1) =
        𝟙 _ + T.map (G.complex.d 1 0) ≫ T.map s₀ +
          T.map s₁ ≫ T.map (G.complex.d 2 1) := by
      rw [hm]
      abel
    rw [Category.assoc, hm']
    change H.iCycles 1 ≫ (𝟙 (H.X 1) + H.d 1 0 ≫ t₀ +
      t₁ ≫ H.d 2 1) = _
    simp only [Preadditive.comp_add, Category.comp_id]
    rw [← Category.assoc _ (H.d 1 0), H.iCycles_d, Limits.zero_comp, add_zero]
  have hzπ : (z ≫ L.homologyπ 1) ≫ HomologicalComplex.homologyMap ψ 1 =
      H.homologyπ 1 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, hzm, Preadditive.add_comp, Category.id_comp, Category.assoc,
      HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero, add_zero]
  have : Epi ((z ≫ L.homologyπ 1) ≫ HomologicalComplex.homologyMap ψ 1) := by
    rw [hzπ]
    infer_instance
  exact epi_of_epi (z ≫ L.homologyπ 1) (HomologicalComplex.homologyMap ψ 1)

/-- The change-of-rings map on first Tor with coefficients in `A/IA` is surjective.

Source: Stacks Project, Algebra, Lemma Tag 00MN
(`literature/stacks-project/algebra.tex`, lines 23881--23919).
(blueprint: lem-weil-pbc-tor-one-surjective-change-rings)

Proof (a shorter comparison argument using the right-exact presentation of Stacks 00MN):
Scalar extension is a left adjoint, hence preserves the exact augmented pair in
resolution degrees one and zero and its epimorphic augmentation. For this
base-changed complex `K`, lift the augmentation of `G` through that of `K` to
obtain `b₀ : G₀ → K₀`. Exactness at `K₀` and projectivity of `G₁` give
`b₁ : G₁ → K₁` satisfying `b₁ d_K = d_G b₀`.

The augmentation condition on `φ` implies that `b₀ φ₀ - 1` lifts through `d_G`
to `s₀ : G₀ → G₁`. The morphism `b₁ φ₁ - 1 - d_G s₀` is killed by `d_G`;
exactness at `G₁` and projectivity of `G₁` lift it to `s₁ : G₁ → G₂`.
Thus `b₁ φ₁ = 1 + d_G s₀ + s₁ d_G`. Apply the additive tensor functor.
The map induced by `b₁` carries cycles of `G` to cycles of `K`. Its composite
with the cycle map induced by `φ` is the identity plus a boundary; the term
through the outgoing differential vanishes on cycles. After projecting to
homology this composite is the surjective cycle projection of `G`. Consequently
the map on first homology is an epimorphism, hence a surjective module map.
No choice of an auxiliary resolution, nor comparison of derived functors, is needed.
-/
theorem tor_one_change_of_rings_surjective
    (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) (M : ModuleCat.{u} R)
    (F : ProjectiveResolution M)
    (hF : ∀ i : ℕ, Module.Free R (F.complex.X i))
    (G : ProjectiveResolution ((ModuleCat.extendScalars f).obj M))
    (hG : ∀ i : ℕ, Module.Free A (G.complex.X i))
    (φ : ((ModuleCat.extendScalars f).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj F.complex ⟶ G.complex)
    (hφ : φ.f 0 ≫ G.π.f 0 = (ModuleCat.extendScalars f).map (F.π.f 0)) :
    Function.Surjective
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
        (ComplexShape.down ℕ) 1).map
        ((((MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ I.map f))).mapHomologicalComplex
            (ComplexShape.down ℕ)).map φ)) := by
  have _hfreeR := hF
  have _hfreeA := hG
  let E := ModuleCat.extendScalars f
  let K := (E.mapHomologicalComplex (ComplexShape.down ℕ)).obj F.complex
  let ε : K.X 0 ⟶ E.obj M := E.map (F.π.f 0)
  have hε : K.d 1 0 ≫ ε = 0 := by
    change E.map (F.complex.d 1 0) ≫ E.map (F.π.f 0) = 0
    rw [← E.map_comp, F.complex_d_comp_π_f_zero, E.map_zero]
  have he : (ShortComplex.mk _ _ hε).Exact := by
    exact F.exact₀.map_of_epi_of_preservesCokernel E inferInstance inferInstance
  let T := (MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ I.map f))
  have : Epi ε := by dsimp [ε, E]; infer_instance
  have := epi_homology_one_of_right_exact K ε hε he G φ hφ T
  exact (ModuleCat.epi_iff_surjective _).mp this

end CategoryTheory
