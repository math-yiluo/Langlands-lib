/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedOffDiagonalPresentation
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedFreeDefectCoordinates
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedFreeBoundaryComparison

/-! # The raw cyclic five-term Hom sequence

Source: Stacks Tag 0149, applied to the free triangle, and the identification of its
boundary with strict off-diagonal presentations in Tag 0152.
(blueprint: lem-sf-cyclic-derived-off-diagonal-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

private theorem coordinate_range {A : Type*} [AddCommGroup A]
    (p T D : A →+ A) (hT : Function.Surjective T)
    (h : ∀ x, p (T x) = -D x) (x : A) :
    (∃ y, p y = x) ↔ ∃ y, D y = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hT y
    exact ⟨-z, by simpa only [map_neg] using (h z).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨T (-y), by simp only [h, map_neg, neg_neg]⟩

private theorem coordinate_kernel {A : Type*} [AddCommGroup A]
    (p T : A →+ A) (hT : Function.Bijective T)
    (h : ∀ x, p (T x) = -(x - T x)) (x : A) :
    p x = 0 ↔ x - T x = 0 := by
  obtain ⟨y, rfl⟩ := hT.2 x
  rw [h, neg_eq_zero, sub_eq_zero, sub_eq_zero]
  exact ⟨fun h ↦ congrArg T h, fun h ↦ hT.1 h⟩

/-- Additivity, the three exact pairs of the raw five-term sequence, and naturality of
its middle arrow, before passing to an invariant subgroup or a coinvariant quotient.
The middle arrow is the uniquely specified off-diagonal extension class.

Proof: apply contravariant representable exactness to the natural free-resolution
triangle and its rotations and shifts. Under the exact free/forgetful adjunction its
Hom groups are V^r. The counit induces precisely cyclicDerivedForget, including the
canonical zero-shift isomorphism. The cyclic differential, evaluated at summand zero,
is 1-(T^r)⁻¹: the adjunct of u has summand n equal to θ_N,n P^n(u), and summand -1
is P⁻¹(θ_N⁻¹ u). The action T^r is invertible. Since
1-T⁻¹ = -T⁻¹(1-T), and T preserves the image of 1-T, these two defects have identical
kernels and images. Thus the three consecutive exact pairs are the ones stated here.

The middle map is u ↦ δ_M ≫ adjunct(u)[1], followed by shift cancellation; both
adjunction and shift are additive, proving its additivity. The free-to-off-diagonal
extension comparison in the presentation theorem identifies it with the boundary
used here, with the same sign. Naturality of δ in M and of adjunction in both variables
proves the precomposition/postcomposition identity. These arguments use no boundedness:
the free resolution and its derived triangle are unbounded. Independently chosen
localizations are compared by their canonical localization equivalences; the standard
factorization isomorphisms transport the displayed formulas unchanged.

Source: steps 1--5 and 8 of lem-sf-cyclic-derived-hom-exact-sequence; Stacks Tags 0149
and 0152, and the explicitly normalized free-resolution triangle.
(blueprint: lem-sf-cyclic-derived-off-diagonal-calculus). -/
theorem cyclicDerivedOffDiagonal_calculus [IsGrothendieckAbelian.{v} C] :
    (∀ (M N : DerivedCategory (IsoAlgebra F)) (u v : CyclicDerivedHom F M N (-1)),
      cyclicDerivedOffDiagonalBoundary F (u + v) =
        cyclicDerivedOffDiagonalBoundary F u + cyclicDerivedOffDiagonalBoundary F v) ∧
    (∀ M N : DerivedCategory (IsoAlgebra F),
      Function.Exact (cyclicDerivedHomDefect F M N (-1))
        (cyclicDerivedOffDiagonalBoundary F (M := M) (N := N)) ∧
      Function.Exact (cyclicDerivedOffDiagonalBoundary F (M := M) (N := N))
        (cyclicDerivedForget F M N) ∧
      Function.Exact (cyclicDerivedForget F M N) (cyclicDerivedHomDefect F M N 0)) ∧
    (∀ (M N M' N' : DerivedCategory (IsoAlgebra F)) (a : M' ⟶ M) (c : N ⟶ N')
      (u : CyclicDerivedHom F M N (-1)),
      a ≫ cyclicDerivedOffDiagonalBoundary F u ≫ c =
        cyclicDerivedOffDiagonalBoundary F
          ((forget F).mapDerivedCategory.map a ≫ u ≫
            ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧')) := by
  obtain ⟨R⟩ := exists_cyclicDerivedFreeResolution F
  let b (M N : DerivedCategory (IsoAlgebra F)) :
      CyclicDerivedHom F M N (-1) →+ (M ⟶ N) :=
    (Preadditive.leftComp _ (R.delta.app M)).comp
      (cyclicDerivedFreeShiftedHomEquiv F M N).symm.toAddMonoidHom
  have hb (M N : DerivedCategory (IsoAlgebra F)) (u : CyclicDerivedHom F M N (-1)) :
      cyclicDerivedOffDiagonalBoundary F u = b M N u :=
    cyclicDerivedFreeBoundary_comparison F R u
  refine ⟨?_, ?_, ?_⟩
  · intro M N u v
    rw [hb, hb, hb]
    exact map_add (b M N) u v
  · intro M N
    let e₀ := cyclicDerivedFreeHomEquiv F M N
    let e₁ := cyclicDerivedFreeShiftedHomEquiv F M N
    let p₀ : CyclicDerivedHom F M N 0 →+ CyclicDerivedHom F M N 0 :=
      e₀.toAddMonoidHom.comp
        ((Preadditive.leftComp _ (R.differential.app M)).comp e₀.symm.toAddMonoidHom)
    let p₁ : CyclicDerivedHom F M N (-1) →+ CyclicDerivedHom F M N (-1) :=
      e₁.toAddMonoidHom.comp
        ((Preadditive.leftComp _ ((R.differential.app M)⟦(1 : ℤ)⟧')).comp
          e₁.symm.toAddMonoidHom)
    let T := Triangle.mk (R.differential.app M)
      ((cyclicDerivedFreeAdjunction F).counit.app M) (R.delta.app M)
    have hT : T ∈ distTriang _ := R.distinguished M
    have hcoords := cyclicDerivedFreeDefect_coordinates F R M N
    have hfirst : Function.Exact p₁ (b M N) := by
      intro u
      constructor
      · intro hu
        obtain ⟨g, hg⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang T hT)
          (e₁.symm u) hu
        refine ⟨e₁ (-g), ?_⟩
        apply e₁.symm.injective
        change e₁.symm (e₁ ((R.differential.app M)⟦(1 : ℤ)⟧' ≫
          e₁.symm (e₁ (-g)))) = e₁.symm u
        rw [e₁.symm_apply_apply, e₁.symm_apply_apply, hg]
        simp [T, Preadditive.comp_neg, Preadditive.neg_comp]
      · rintro ⟨x, rfl⟩
        change R.delta.app M ≫ e₁.symm
          (e₁ ((R.differential.app M)⟦(1 : ℤ)⟧' ≫ e₁.symm x)) = 0
        rw [e₁.symm_apply_apply, ← Category.assoc]
        simpa only [T, Triangle.mk, Limits.zero_comp] using
          (comp_distTriang_mor_zero₃₁ T hT) =≫ e₁.symm x
    have hmiddle : Function.Exact (b M N) (cyclicDerivedForget F M N) := by
      intro f
      rw [← cyclicDerivedFreeHomEquiv_counit F M N f, ← e₀.map_zero,
        e₀.injective.eq_iff]
      constructor
      · intro hf
        obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f hf
        refine ⟨e₁ g, ?_⟩
        change R.delta.app M ≫ e₁.symm (e₁ g) = f
        rw [e₁.symm_apply_apply]
        exact hg.symm
      · rintro ⟨u, rfl⟩
        change (cyclicDerivedFreeAdjunction F).counit.app M ≫
          (R.delta.app M ≫ e₁.symm u) = 0
        rw [← Category.assoc]
        simpa only [T, Triangle.mk, Limits.zero_comp] using
          (comp_distTriang_mor_zero₂₃ T hT) =≫ e₁.symm u
    have hlast : Function.Exact (cyclicDerivedForget F M N) p₀ := by
      intro u
      change e₀ (R.differential.app M ≫ e₀.symm u) = 0 ↔ _
      rw [← e₀.map_zero, e₀.injective.eq_iff]
      constructor
      · intro hu
        obtain ⟨f, hf⟩ := T.yoneda_exact₂ hT (e₀.symm u) hu
        change M ⟶ N at f
        change e₀.symm u = (cyclicDerivedFreeAdjunction F).counit.app M ≫ f at hf
        refine ⟨f, ?_⟩
        rw [← cyclicDerivedFreeHomEquiv_counit]
        change e₀ (_ ≫ f) = u
        rw [← hf, e₀.apply_symm_apply]
      · rintro ⟨f, rfl⟩
        rw [← cyclicDerivedFreeHomEquiv_counit]
        change R.differential.app M ≫ e₀.symm (e₀ (_ ≫ f)) = 0
        rw [e₀.symm_apply_apply, ← Category.assoc]
        simpa only [T, Triangle.mk, Limits.zero_comp] using
          (comp_distTriang_mor_zero₁₂ T hT) =≫ f
    refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [hb]
      exact (hfirst u).trans (coordinate_range p₁ (cyclicDerivedHomAction F M N (-1))
        (cyclicDerivedHomDefect F M N (-1))
        (cyclicDerivedHomAction_bijective F M N (-1)).2 hcoords.2 u)
    · intro f
      constructor
      · intro hf
        obtain ⟨u, hu⟩ := (hmiddle f).1 hf
        exact ⟨u, (hb M N u).trans hu⟩
      · rintro ⟨u, hu⟩
        exact (hmiddle f).2 ⟨u, (hb M N u).symm.trans hu⟩
    · intro u
      have hker := coordinate_kernel p₀ (cyclicDerivedHomAction F M N 0)
        (cyclicDerivedHomAction_bijective F M N 0) hcoords.1 u
      exact hker.symm.trans (hlast u)
  · intro M N M' N' a c u
    rw [hb, hb]
    change a ≫ (R.delta.app M ≫
      (cyclicDerivedFreeShiftedHomEquiv F M N).symm u) ≫ c =
        R.delta.app M' ≫ (cyclicDerivedFreeShiftedHomEquiv F M' N').symm
          ((forget F).mapDerivedCategory.map a ≫ u ≫
            ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧')
    have hδ := R.delta.naturality a
    change a ≫ R.delta.app M = R.delta.app M' ≫
      ((cyclicDerivedFreeFunctor F).map a)⟦(1 : ℤ)⟧' at hδ
    simp only [← Category.assoc]
    rw [hδ]
    simp only [Category.assoc]
    congr 1
    apply (cyclicDerivedFreeShiftedHomEquiv F M' N').injective
    rw [cyclicDerivedFreeShiftedHomEquiv_naturality,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The raw connecting map as an additive homomorphism.
Source: the additive free-adjunction boundary of Stacks Tags 0149 and 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-calculus). -/
def cyclicDerivedOffDiagonalBoundaryHom [IsGrothendieckAbelian.{v} C]
    (M N : DerivedCategory (IsoAlgebra F)) : CyclicDerivedHom F M N (-1) →+ (M ⟶ N) :=
  AddMonoidHom.mk' (cyclicDerivedOffDiagonalBoundary F)
    ((cyclicDerivedOffDiagonal_calculus F).1 M N)

end CategoryTheory.Endofunctor.IsoAlgebra
