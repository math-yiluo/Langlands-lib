/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field
public import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# The dimension of the Lie algebra of a group scheme over a field

Let `G` be a group scheme locally of finite type over a field `k`. The dimension of `G` is at most
the dimension of its Lie algebra, and in characteristic zero they are equal (Cartier).

The upper bound is proved after base change to an algebraic closure `K` of `k`. The dimension of
`G` is at most that of `G_K`, as `Spec (K ⊗[k] B)` is integral over `Spec B` for every affine open
`Spec B` of `G`. Over `K` the left translations act transitively on the closed points, and every
point specialises to a closed point, so `dim G_K` is the codimension of any closed point. In the
base change `Spec (K ⊗[k] A)` of an affine chart `Spec A` at the identity, the base change of the
identity is a closed point whose codimension is bounded by the dimension of the cotangent space
of `A` at the identity, which is the dimension of `Lie(G)`.

## Main results

- `AlgebraicGeometry.Scheme.topologicalKrullDim_eq_iSup_coheight`: the dimension of a scheme is
  the supremum of the codimensions of its points.
- `AlgebraicGeometry.topologicalKrullDim_le_pullback`: the dimension of a scheme over `k` is at
  most the dimension of its base change to an algebraic extension of `k`.
- `AlgebraicGeometry.GrpObj.topologicalKrullDim_le_coheight`: over an algebraically closed field,
  the dimension of a group scheme locally of finite type is at most the codimension of any of its
  closed points.
- `AlgebraicGeometry.GrpObj.topologicalKrullDim_le_finrank_lie`: `dim G ≤ dim Lie(G)`.
- `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim`: in characteristic zero,
  `dim Lie(G) = dim G`.
- `AlgebraicGeometry.GrpObj.isIso_left_of_differential_bijective`: in characteristic zero, a
  closed subgroup scheme of a connected group scheme of finite type with the same Lie algebra is
  everything.

## Blueprint

- `proposition-cartier-s-theorem`: the Lie algebra clauses of Cartier's theorem.
- `lemma-connected-components-images-homomorphisms--3`: the Lie criterion for closed subgroups.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The codimension of a point of a scheme is at most the dimension of the scheme. -/
theorem Scheme.coheight_le_topologicalKrullDim {X : Scheme.{u}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim, krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  exact coheight_le_krullDim x

/-- The dimension of a scheme is the supremum of the codimensions of its points. -/
theorem Scheme.topologicalKrullDim_eq_iSup_coheight (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, (coheight x : WithBot ℕ∞) := by
  rw [topologicalKrullDim, krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    krullDim_eq_iSup_coheight]

section Field

variable {k : Type u} [Field k]

/-- Every point of a scheme `X` over `k` lies in an affine open subscheme `Spec B ⟶ X` over
`k`. -/
theorem exists_affine_chart_mem {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (j : Spec (.of B) ⟶ X)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  obtain ⟨R, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  let : Algebra k R := (Spec.preimage (j ≫ f)).hom.toAlgebra
  exact ⟨R, _, _, j, inferInstance, hx, (Spec.map_preimage (j ≫ f)).symm⟩

/-- The base change of an affine open subscheme `Spec B ⟶ X` over `k` along `Spec L ⟶ Spec k` is
an affine open subscheme `Spec (L ⊗[k] B) ⟶ X_L` of the base change. -/
theorem exists_isOpenImmersion_tensorProduct {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {B : Type u} [CommRing B] [Algebra k B] (j : Spec (.of B) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) (L : Type u) [CommRing L]
    [Algebra k L] :
    ∃ j' : Spec (.of (L ⊗[k] B)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      IsOpenImmersion j' := by
  have := MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := j)
    (i₂ := 𝟙 (Spec (.of L))) (g := Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap k L))) ‹_› (MorphismProperty.id_mem _ _)
    hj.symm (Category.id_comp _).symm
  exact ⟨(pullbackSpecIso k L B).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hj.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm), inferInstance⟩

/-- The dimension of a scheme `X` over `k` is at most the dimension of its base change `X_K` to an
algebraic extension `K` of `k`: for an affine open `Spec B` of `X`, the ring `K ⊗[k] B` is
integral over `B` and contains `B`, hence has the same dimension, and `Spec (K ⊗[k] B)` is open in
`X_K`. -/
theorem topologicalKrullDim_le_pullback {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u)
    [Field K] [Algebra k K] [Algebra.IsIntegral k K] :
    topologicalKrullDim X ≤
      topologicalKrullDim
        (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  rw [Scheme.topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨B, _, _, j, _, ⟨y, rfl⟩, hj⟩ := exists_affine_chart_mem f x
  obtain ⟨j', _⟩ := exists_isOpenImmersion_tensorProduct f j hj K
  have : FaithfulSMul B (B ⊗[k] K) := (faithfulSMul_iff_algebraMap_injective _ _).2
    (Algebra.TensorProduct.includeLeft_injective (S := B) (algebraMap k K).injective)
  calc ((coheight (j y) : ℕ∞) : WithBot ℕ∞) = coheight y := by
        rw [coheight_eq_of_isOpenImmersion]
    _ ≤ topologicalKrullDim (Spec (.of B)) := Scheme.coheight_le_topologicalKrullDim y
    _ = ringKrullDim B := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B
    _ = ringKrullDim (B ⊗[k] K) := (ringKrullDim_eq_of_isIntegral B (B ⊗[k] K)).symm
    _ = ringKrullDim (K ⊗[k] B) :=
        ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm k B K).toRingEquiv
    _ = topologicalKrullDim (Spec (.of (K ⊗[k] B))) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ ≤ _ := j'.isOpenEmbedding.isInducing.topologicalKrullDim_le

end Field

namespace GrpObj

/-- Over an algebraically closed field `K`, a group scheme locally of finite type has dimension at
most the codimension of any of its closed points `w`: every point specialises to a closed point,
and the left translations act transitively on the closed points. -/
theorem topologicalKrullDim_le_coheight {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom] {w : G.left}
    (hw : IsClosed {w}) :
    topologicalKrullDim G.left ≤ coheight w := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  rw [Scheme.topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun z ↦ ?_
  obtain ⟨y, hzy, hy⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty z).closure
    isClosed_closure.isLocallyClosed
  obtain ⟨φ, hφ⟩ := exists_homeomorph_apply_eq G hy hw
  calc ((coheight z : ℕ∞) : WithBot ℕ∞) ≤ coheight y := by
        exact_mod_cast coheight_anti
          (Scheme.le_iff_specializes.2 (specializes_iff_mem_closure.2 hzy))
    _ = coheight w := by
        rw [← hφ, φ.isOpenEmbedding.coheight_eq]

variable {k : Type u} [Field k]

/-- **Upper bound in Cartier's dimension formula**: a group scheme `G` locally of finite type over
a field `k` has dimension at most the dimension of its Lie algebra. After base change to an
algebraic closure `K`, `dim G_K` is the codimension of the base change of the identity in an
affine chart `Spec (K ⊗[k] A)`, which is at most the dimension of the cotangent space of `A` at
the identity, that is of `Lie(G)`. -/
theorem topologicalKrullDim_le_finrank_lie (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] :
    topologicalKrullDim G.left ≤ (Module.finrank k (Lie G) : WithBot ℕ∞) := by
  obtain ⟨A, _, _, j, _, e, _, hj, he⟩ := exists_affine_chart G
  rw [finrank_lie_eq_finrank_cotangent j hj e he]
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  let : GrpObj (Over.mk (pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd G.hom g)
  obtain ⟨j', _⟩ := exists_isOpenImmersion_tensorProduct G.hom j hj K
  set ε := AlgHom.liftEquiv k K A K ((Algebra.ofId k K).comp e)
  have hε : Function.Surjective ε := fun c ↦ ⟨algebraMap K _ c, ε.commutes c⟩
  let x : Spec (.of (K ⊗[k] A)) := ⟨RingHom.ker ε, RingHom.ker_isPrime ε⟩
  have hx : IsClosed {j' x} := by
    refine isClosed_singleton_of_isLocallyClosed_singleton ?_
    rw [← Set.image_singleton]
    exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2
      (RingHom.ker_isMaximal_of_surjective ε hε)).isLocallyClosed.image
      j'.isOpenEmbedding.isInducing j'.isOpenEmbedding.isOpen_range.isLocallyClosed
  have : LocallyOfFiniteType (Over.mk (pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom g))
  have h : coheight (j' x) = (RingHom.ker ε).height :=
    (coheight_eq_of_isOpenImmersion j').trans (idealHeight_eq_coheight (.of (K ⊗[k] A)) x).symm
  have h' : (RingHom.ker ε).height ≤ Module.finrank k (RingHom.ker e).Cotangent :=
    AlgHom.height_ker_liftEquiv_le K
  calc topologicalKrullDim G.left ≤ topologicalKrullDim (pullback (C := Scheme.{u}) G.hom g) :=
        topologicalKrullDim_le_pullback G.hom K
    _ ≤ coheight (j' x) := topologicalKrullDim_le_coheight (Over.mk (pullback.snd G.hom g)) hx
    _ = (RingHom.ker ε).height := by
        exact_mod_cast h
    _ ≤ _ := by
        exact_mod_cast h'

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of a
group scheme `G` of finite type has dimension the dimension of `G`. The lower bound is
`AlgebraicGeometry.GrpObj.finrank_lie_le_topologicalKrullDim`, the upper bound
`AlgebraicGeometry.GrpObj.topologicalKrullDim_le_finrank_lie`.
(blueprint: `proposition-cartier-s-theorem`) -/
theorem finrank_lie_eq_topologicalKrullDim (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [CharZero k] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) = topologicalKrullDim G.left :=
  le_antisymm finrank_lie_le_topologicalKrullDim (topologicalKrullDim_le_finrank_lie G)

/-- The Lie criterion for closed subgroups: over a field of characteristic zero, a closed subgroup
scheme `K` of a connected group scheme `G` of finite type with the same Lie algebra (the
differential of the inclusion is bijective) is all of `G`. By Cartier's theorem
`dim K = dim Lie(K) = dim Lie(G) = dim G`, and `K` and `G` are reduced, so
`AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq` applies.
(blueprint: `lemma-connected-components-images-homomorphisms--3`, clause (1)) -/
theorem isIso_left_of_differential_bijective [CharZero k] {K G : Over (Spec (.of k))} [GrpObj K]
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace G.left]
    (f : K ⟶ G) [IsMonHom f] [IsClosedImmersion f.left]
    (h : Function.Bijective (differential f)) : IsIso f.left := by
  have hK : K.hom = f.left ≫ G.hom := (Over.w f).symm
  have : LocallyOfFiniteType K.hom := by rw [hK]; infer_instance
  have : QuasiCompact K.hom := by rw [hK]; infer_instance
  have := isReduced_of_charZero K
  have := isReduced_of_charZero G
  refine isIso_left_of_topologicalKrullDim_eq f ?_
  rw [← finrank_lie_eq_topologicalKrullDim, ← finrank_lie_eq_topologicalKrullDim,
    (LinearEquiv.ofBijective (differential f).toLinearMap h).finrank_eq]

end GrpObj

end AlgebraicGeometry
