/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Affine schemes of finite type over a base embed into projective space

Let `S` be a scheme and let `g : V ⟶ S` be a morphism that is locally of finite type, with `V`
affine. We construct a finite index type `n` and an immersion `V ⟶ ℙ(n; S)` over `S`.

The construction is elementary. Cover `V` by finitely many basic opens `V_{b l}` each lying
over an affine open `W l` of `S`. Since `V_{b l} ⟶ W l` is a morphism of affine schemes of
finite type, the ring `Γ(V_{b l}, ⊤)` is generated over `Γ(W l, ⊤)` by finitely many fractions
with denominator a power of `b l`; multiplying numerators by `b l` and adding the fraction
`1 / b l` to the family, one gets a finite family `t l` of global sections of `V` such that
`Γ(V_{b l}, ⊤)` is generated over `Γ(W l, ⊤)` by the quotients `t l μ / b l`.

Taking for `n` the disjoint union of the index set of the cover with the index sets of these
families, and for `s : n → Γ(V, ⊤)` the sections `b l` and `t l μ`, the morphism
`j := ProjectiveSpace.homOfSections g s` restricts on the standard chart `D₊(T_{b l})` to the
morphism into affine space over `S` classified by the quotients `s i / b l`. This factors
through the affine space over `W l`, where it is `Spec` of a surjection of rings, hence a closed
immersion; composing with the open immersion `𝔸(m; W l) ⟶ 𝔸(m; S)` shows the restriction of `j`
is an immersion. Since the standard charts used cover the image of `j`, this proves `j` is an
immersion.

## Main results

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace` — an affine scheme locally of finite
  type over `S` admits an immersion over `S` into a projective space `ℙ(n; S)` with `n` finite.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {V S : Scheme.{u}}

section Auxiliary

/-- **Generators with a common denominator, geometrically.** If `g : V ⟶ S` is locally of finite
type with `V` affine, and the basic open `V_b` lies over an affine open `W` of `S`, then there
is a finite family `t` of global sections of `V` such that `Γ(V_b, ⊤)` is generated as a ring by
the image of `Γ(W, ⊤)` together with the quotients `t μ / b`. -/
lemma exists_finite_subring_closure_divBasicOpen_eq_top (g : V ⟶ S) [IsAffine V]
    [LocallyOfFiniteType g] (b : Γ(V, ⊤)) (W : S.Opens) (hW : IsAffineOpen W)
    (hle : V.basicOpen b ≤ g ⁻¹ᵁ W) :
    ∃ (m : Type u) (_ : Finite m) (t : m → Γ(V, ⊤)),
      Subring.closure (Set.range (g.resLE W (V.basicOpen b) hle).appTop ∪
        Set.range fun μ ↦ V.divBasicOpen (t μ) b) = ⊤ := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (V.basicOpen b : Scheme.{u}) := (isAffineOpen_top V).basicOpen b
  have : LocallyOfFiniteType (g.resLE W (V.basicOpen b) hle) := by
    delta Scheme.Hom.resLE; infer_instance
  let : Algebra Γ(W.toScheme, ⊤) Γ((V.basicOpen b : Scheme.{u}), ⊤) :=
    (g.resLE W (V.basicOpen b) hle).appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(W.toScheme, ⊤) Γ((V.basicOpen b : Scheme.{u}), ⊤) :=
    HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType (g.resLE W (V.basicOpen b) hle)›
  obtain ⟨N, M, hM, c, hc⟩ := Algebra.FiniteType.exists_surjective_aeval_mk'
    (A := Γ(W.toScheme, ⊤)) b Γ((V.basicOpen b : Scheme.{u}), ⊤)
  refine ⟨ULift.{u} (Option M), inferInstance, fun μ ↦ μ.down.elim 1 fun ν ↦ c ν * b,
    (Subring.eq_top_iff' _).mpr fun x ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hc x
  have hone : V.divBasicOpen 1 b ∈
      Subring.closure (Set.range ⇑(g.resLE W (V.basicOpen b) hle).appTop ∪
        Set.range fun μ : ULift.{u} (Option M) ↦
          V.divBasicOpen (μ.down.elim 1 fun ν ↦ c ν * b) b) :=
    Subring.subset_closure (Or.inr ⟨⟨none⟩, rfl⟩)
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine Subring.subset_closure (Or.inl ⟨a, ?_⟩)
    rw [MvPolynomial.aeval_C]
    rfl
  | add p q hp hq => simpa only [map_add] using Subring.add_mem _ hp hq
  | mul_X p μ hp =>
    rw [map_mul, MvPolynomial.aeval_X,
      mk'_eq_divBasicOpen_pow V b (c μ) N ⟨N, rfl⟩]
    exact Subring.mul_mem _ hp (Subring.mul_mem _ (Subring.pow_mem _ hone N)
      (Subring.subset_closure (Or.inr ⟨⟨some μ⟩, rfl⟩)))

/-- The morphism into affine space over `S` classified by the quotients `s j / s i` on the basic
open `V_{s i}` is an immersion, provided the sections over `V_{s i}` are generated as a ring by
the image of the sections of an affine open `W` of `S` receiving `V_{s i}` together with those
quotients. -/
lemma isImmersion_homOfVector_divBasicOpen (g : V ⟶ S) [IsAffine V] {n : Type u}
    (s : n → Γ(V, ⊤)) (i : n) (W : S.Opens) (hW : IsAffineOpen W)
    (hle : V.basicOpen (s i) ≤ g ⁻¹ᵁ W)
    (hgen : Subring.closure (Set.range (g.resLE W (V.basicOpen (s i)) hle).appTop ∪
      Set.range fun j : {j : n // j ≠ i} ↦ V.divBasicOpen (s j.1) (s i)) = ⊤) :
    IsImmersion (AffineSpace.homOfVector ((V.basicOpen (s i)).ι ≫ g)
      fun j : {j : n // j ≠ i} ↦ V.divBasicOpen (s j.1) (s i)) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (V.basicOpen (s i) : Scheme.{u}) := (isAffineOpen_top V).basicOpen (s i)
  have := AffineSpace.isClosedImmersion_homOfVector (m := {j : n // j ≠ i})
    (g.resLE W (V.basicOpen (s i)) hle) _ hgen
  rw [show (V.basicOpen (s i)).ι ≫ g = g.resLE W (V.basicOpen (s i)) hle ≫ W.ι from
    (Scheme.Hom.resLE_comp_ι g hle).symm, ← AffineSpace.homOfVector_comp_map]
  infer_instance

end Auxiliary

/-- **An affine scheme locally of finite type over `S` admits an immersion into a projective
space over `S`.** -/
theorem exists_isImmersion_projectiveSpace [IsAffine V] (g : V ⟶ S) [LocallyOfFiniteType g] :
    ∃ (n : Type u) (_ : Finite n) (j : V ⟶ ℙ(n; S)),
      IsImmersion j ∧ j ≫ ℙ(n; S) ↘ S = g := by
  obtain ⟨Λ, hΛ, b, W, hW, hWle, hcov⟩ :=
    exists_finite_basicOpen_cover_le_preimage_isAffineOpen g
  have := hΛ
  choose m hm t ht using fun l : Λ ↦
    exists_finite_subring_closure_divBasicOpen_eq_top g (b l) (W l) (hW l) (hWle l)
  have : ∀ l, Finite (m l) := hm
  set n : Type u := Λ ⊕ (Σ l : Λ, m l)
  set s : n → Γ(V, ⊤) := Sum.elim b fun p ↦ t p.1 p.2
  have hs : Ideal.span (Set.range s) = ⊤ := by
    rw [← (isAffineOpen_top V).iSup_basicOpen_eq_self_iff, iSup_range']
    exact top_le_iff.mp
      (hcov.ge.trans (iSup_le fun l ↦ le_iSup (fun i ↦ V.basicOpen (s i)) (Sum.inl l)))
  have hpre : ∀ l : Λ, ProjectiveSpace.homOfSections g s hs ⁻¹ᵁ
      ProjectiveSpace.standardOpen n S (Sum.inl l) = V.basicOpen (s (Sum.inl l)) :=
    fun l ↦ ProjectiveSpace.homOfSections_preimage_standardOpen g s hs (Sum.inl l)
  refine ⟨n, inferInstance, ProjectiveSpace.homOfSections g s hs, ?_,
    ProjectiveSpace.homOfSections_over g s hs⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun l : Λ ↦ ProjectiveSpace.standardOpen n S (Sum.inl l)) ?_ fun l ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ l : Λ, V.basicOpen (b l) := by rw [hcov]; trivial
    obtain ⟨l, hxl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨l, ?_⟩)
    change x ∈ ProjectiveSpace.homOfSections g s hs ⁻¹ᵁ
      ProjectiveSpace.standardOpen n S (Sum.inl l)
    rw [hpre l]
    exact hxl
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr (ProjectiveSpace.homOfSections g s hs)
        (U := ProjectiveSpace.standardOpen n S (Sum.inl l)) le_rfl rfl (hpre l) @IsImmersion,
      ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
        (ProjectiveSpace.standardOpenIso n S (Sum.inl l)).hom,
      ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom g s hs (Sum.inl l)]
    refine isImmersion_homOfVector_divBasicOpen g s (Sum.inl l) (W l) (hW l) (hWle l)
      (eq_top_iff.mpr ((ht l).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
    rintro _ ⟨μ, rfl⟩
    exact ⟨⟨Sum.inr ⟨l, μ⟩, Sum.inr_ne_inl⟩, rfl⟩

end AlgebraicGeometry
