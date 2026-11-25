/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.RingTheory.KrullDimension.FiniteType
public import WeilConjectures.Topology.KrullDimension.Open

/-!
# Dimensions of closures of points along a morphism of finite type over a field

Let `f : X ⟶ Y` be a morphism locally of finite type, where `Y` is locally of finite type over a
field `k`. The closure of a point of `X` has dimension at least that of the closure of its image:
both are transcendence degrees over `k` of the residue fields. Consequently, for a closed subset
`Z ⊆ X` and a point `y ∈ Y`, `dim {y}⁻ + dim (Z ∩ f⁻¹(y)) ≤ dim Z`.

## Main statements

- `AlgebraicGeometry.Scheme.topologicalKrullDim_closure_singleton_of_isAffine`: in an affine
  scheme, the closure of a point `x` has the dimension of `Γ(X, ⊤) ⧸ 𝔭ₓ`.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le`:
  `dim {f x}⁻ ≤ dim {x}⁻`.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_closure_singleton_add_le`:
  `dim {y}⁻ + dim (Z ∩ f⁻¹(y)) ≤ dim Z`.
-/

@[expose] public section

open CategoryTheory Topology Order

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- In an affine scheme `X`, the closure of a point `x` has the dimension of the quotient of
`Γ(X, ⊤)` by the prime ideal of `x`. -/
theorem Scheme.topologicalKrullDim_closure_singleton_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (x : X) :
    topologicalKrullDim (closure {x} : Set X) =
      ringKrullDim (Γ(X, ⊤) ⧸ (X.isoSpec.hom x).asIdeal) := by
  rw [← X.isoSpec.hom.isOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range,
    Set.range_eq_univ.2 X.isoSpec.hom.surjective, Set.inter_univ]
  exact PrimeSpectrum.topologicalKrullDim_closure_singleton _

/-- The ring of global sections of an affine scheme of finite type over a field `k` is of
finite type over `k`. -/
lemma Scheme.finiteType_ΓSpecIso_inv_comp_appTop {k : Type u} [Field k] (U : Scheme.{u})
    [IsAffine U] (a : U ⟶ Spec (.of k)) [LocallyOfFiniteType a] :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop).hom.FiniteType := by
  rw [CommRingCat.hom_comp]
  refine RingHom.FiniteType.comp (HasRingHomProperty.iff_of_isAffine.1 ‹_›)
    (RingHom.FiniteType.of_surjective _ fun r ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom r, ?_⟩)
  simp

/-- The affine case of `Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le`: for a
morphism `g : U ⟶ V` of affine schemes of finite type over a field, `dim {g u}⁻ ≤ dim {u}⁻`,
by `ringKrullDim_quotient_comap_le` applied to `g^♯ : Γ(V, ⊤) ⟶ Γ(U, ⊤)`. -/
theorem Scheme.topologicalKrullDim_closure_singleton_apply_le_of_isAffine {k : Type u} [Field k]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aV] (g : U ⟶ V) [LocallyOfFiniteType g] (u : U) :
    topologicalKrullDim (closure {g u} : Set V) ≤ topologicalKrullDim (closure {u} : Set U) := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ aV.appTop).hom.toAlgebra
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ aV).appTop).hom.toAlgebra
  have : Algebra.FiniteType k Γ(V, ⊤) := finiteType_ΓSpecIso_inv_comp_appTop V aV
  have : Algebra.FiniteType k Γ(U, ⊤) := finiteType_ΓSpecIso_inv_comp_appTop U (g ≫ aV)
  let φ : Γ(V, ⊤) →ₐ[k] Γ(U, ⊤) :=
    { g.appTop.hom with
      commutes' r := by simp [RingHom.algebraMap_toAlgebra] }
  have hgu : V.isoSpec.hom (g u) = Spec.map g.appTop (U.isoSpec.hom u) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply]
  rw [topologicalKrullDim_closure_singleton_of_isAffine,
    topologicalKrullDim_closure_singleton_of_isAffine, hgu]
  exact ringKrullDim_quotient_comap_le k φ _

/-- **Dimension of the closure of an image point.** For a morphism `f : X ⟶ Y` locally of finite
type, with `Y` locally of finite type over a field, `dim {f x}⁻ ≤ dim {x}⁻`: on affine opens both
dimensions are transcendence degrees of finitely generated domains over `k`, and the closure of
`f x` is covered by its traces on the affine opens around its points. -/
theorem Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) :
    topologicalKrullDim (closure {f x} : Set Y) ≤ topologicalKrullDim (closure {x} : Set X) := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen isClosed_closure fun z hz ↦ ?_
  obtain ⟨V, hV, hzV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Y.Opens) from trivial)
  have hyV : f x ∈ V := (specializes_iff_mem_closure.2 hz).mem_open V.isOpen hzV
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hyV)
  have : IsAffine U := hU
  have : IsAffine V := hV
  refine ⟨V, V.isOpen, hzV, ?_⟩
  let g := f.resLE V U hUV
  let u : (U : Scheme) := ⟨x, hxU⟩
  have hgu : V.ι (g u) = f x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
    rfl
  have h₁ := V.ι.isOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range (g u)
  rw [hgu, Scheme.Opens.range_ι] at h₁
  have h₂ := U.ι.isOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range u
  rw [Scheme.Opens.range_ι] at h₂
  rw [h₁]
  refine (topologicalKrullDim_closure_singleton_apply_le_of_isAffine (V.ι ≫ aY) g u).trans ?_
  rw [← h₂]
  exact (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le

/-- **Dimension of a closed subset and its fibres.** For a morphism `f : X ⟶ Y` locally of finite
type, with `Y` locally of finite type over a field, a closed subset `Z ⊆ X` and a point `y ∈ Y`,
`dim {y}⁻ + e ≤ dim Z` whenever `Z ∩ f⁻¹(y)` has dimension at least `e`: a chain of
specializations of length `e` in `Z ∩ f⁻¹(y)` extends below its special end `z` by a chain of
length `dim {z}⁻ ≥ dim {y}⁻`. -/
theorem Scheme.Hom.topologicalKrullDim_closure_singleton_add_le {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsClosed Z) (y : Y) (e : ℕ)
    (he : (e : WithBot ℕ∞) ≤ topologicalKrullDim (Z ∩ f ⁻¹' {y} : Set X)) :
    topologicalKrullDim (closure {y} : Set Y) + e ≤ topologicalKrullDim Z := by
  have : QuasiSober (f ⁻¹' {y}) := (f.fiberHomeo y).symm.isOpenEmbedding.quasiSober
  let W : Set (f ⁻¹' {y}) := Subtype.val ⁻¹' Z
  have : QuasiSober W :=
    (hZ.preimage continuous_subtype_val).isClosedEmbedding_subtypeVal.quasiSober
  let : Preorder W := (specializationOrder W).toPreorder
  let i : W → X := fun w ↦ w.1.1
  have hi : IsEmbedding i := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hr : Set.range i = Z ∩ f ⁻¹' {y} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.2, w.1.2⟩
    · rintro ⟨hxZ, hxy⟩
      exact ⟨⟨⟨x, hxy⟩, hxZ⟩, rfl⟩
  rw [← hr, ← hi.topologicalKrullDim_eq_range, topologicalKrullDim_eq_krullDim_specializationOrder]
    at he
  obtain ⟨l, hl⟩ := le_krullDim_iff.1 he
  have hmono : StrictMono i :=
    strictMono_of_le_iff_le fun a b ↦ (hi.isInducing.specializes_iff (x := b) (y := a)).symm
  have h₁ := height_head_add_length_le_height_last (l.map i hmono)
  rw [LTSeries.map_length, LTSeries.head_map, LTSeries.last_map, hl] at h₁
  have hy : f (i l.head) = y := l.head.1.2
  have h₂ := Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le aY f (i l.head)
  rw [hy, topologicalKrullDim_closure_singleton (i l.head)] at h₂
  have hl : i l.last ∈ Z := l.last.2
  have hsub : (closure {i l.last} : Set X) ⊆ Z := closure_minimal (Set.singleton_subset_iff.2 hl) hZ
  have h₃ : topologicalKrullDim (closure {i l.last} : Set X) ≤ topologicalKrullDim Z :=
    (IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_closure_singleton] at h₃
  calc topologicalKrullDim (closure {y} : Set Y) + e ≤ (height (i l.head) : WithBot ℕ∞) + e :=
        add_le_add_left h₂ _
    _ = ((height (i l.head) + e : ℕ∞) : WithBot ℕ∞) := by norm_cast
    _ ≤ height (i l.last) := by exact_mod_cast h₁
    _ ≤ topologicalKrullDim Z := h₃

end AlgebraicGeometry
