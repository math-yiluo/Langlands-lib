/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.Mathlib.CategoryTheory.Yoneda

/-!
# The degree decomposition of the Picard scheme: group structures and translations

Let `X` be a smooth projective geometrically integral curve over a field `k`. This file completes
the degree decomposition `Pic_{X/k} = ∐_d Pic^d_{X/k}` of
`AlgebraicGeometry.exists_decomposition_picardFunctor` by its group-theoretic parts.

* The fibrewise degree is a group homomorphism `Pic (X_T) →* (T → ℤ)`, natural in `T`
  (`AlgebraicGeometry.picardPresheafDegreeHom`), whose kernel is the degree-zero subgroup
  (`AlgebraicGeometry.ker_picardPresheafDegreeHom`); hence `Pic^d · Pic^e ⊆ Pic^{d+e}`
  (`AlgebraicGeometry.mul_mem_picardSubfunctorDegree`). On the sheafification `Pic_{X/k}` with its
  inherited group law, the degree is again additive (`AlgebraicGeometry.picardDegree_mul`).
* The open and closed subscheme `P^0` of a scheme `P` representing `Pic_{X/k}` is a subgroup
  scheme: the inclusion `P^0 ⟶ P` is a morphism of group objects
  (`AlgebraicGeometry.exists_decomposition_picardFunctor_isMonHom`).
* Tensoring with a class `M ∈ Pic X` of degree `e` induces an isomorphism between schemes
  representing `Pic^d_{X/k}` and `Pic^{d+e}_{X/k}` whose functor of points is
  `ℒ ↦ ℒ ⊗ pr_X^* M` (`AlgebraicGeometry.exists_iso_representableBy_picardFunctorDegree`); with
  `M = 𝒪_X(d x)` for a rational point `x` this identifies `P^0` with `P^d`
  (`AlgebraicGeometry.exists_iso_representableBy_picardFunctorDegree_zero`).
* The translation `τ_M` of a scheme `P` representing `Pic_{X/k}` by a class `M ∈ Pic X`
  (`AlgebraicGeometry.picardTranslation`), on points `x ↦ x · [M]`
  (`AlgebraicGeometry.picardTranslation_hom_eq_mul`), has inverse `τ_{M⁻¹}`
  (`AlgebraicGeometry.picardTranslation_inv`) and restricts to the isomorphisms between the
  degree components (`AlgebraicGeometry.comp_picardTranslation_hom`,
  `AlgebraicGeometry.exists_decomposition_picardTranslation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme

section DegreeHom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f]

omit [SmoothOfRelativeDimension 1 f] in
/-- The fibrewise degree of a class at a point `t` is its degree on the fibre over the residue
field `κ(t)`. -/
lemma exists_picardFibreDegree_eq_picardPresheafDegree {T : Over (Spec (.of k))} (t : T.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T),
      ∀ L : (picardPresheaf f).obj (.op T),
        picardFibreDegree f L τ = picardPresheafDegree f L t := by
  let φ := T.left.fromSpecResidueField t ≫ T.hom
  let : Algebra k (T.left.residueField t) := (Spec.preimage φ).hom.toAlgebra
  let τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) (Spec.map_preimage φ).symm
  obtain ⟨s⟩ : Nonempty (Spec (T.left.residueField t)) := inferInstance
  refine ⟨_, inferInstance, inferInstance, τ, fun L ↦ ?_⟩
  rw [picardFibreDegree_eq_picardPresheafDegree f L τ s,
    show τ.left s = t from Scheme.fromSpecResidueField_apply _ _]

/-- **The fibrewise degree is additive**: `deg (ℒ ⊗ ℳ)_t = deg ℒ_t + deg ℳ_t`. -/
lemma picardPresheafDegree_mul {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic)
    (t : T.left) :
    picardPresheafDegree f (L * M : (pullback f T.hom).Pic) t =
      picardPresheafDegree f L t + picardPresheafDegree f M t := by
  obtain ⟨K, _, _, τ, h⟩ := exists_picardFibreDegree_eq_picardPresheafDegree f t
  rw [← h, ← h, ← h]
  exact picardFibreDegree_mul f τ L M

omit [SmoothOfRelativeDimension 1 f] in
/-- The fibrewise degree of the unit class is zero. -/
lemma picardPresheafDegree_one {T : Over (Spec (.of k))} (t : T.left) :
    picardPresheafDegree f (1 : (pullback f T.hom).Pic) t = 0 := by
  obtain ⟨K, _, _, τ, h⟩ := exists_picardFibreDegree_eq_picardPresheafDegree f t
  rw [← h]
  exact picardFibreDegree_one f τ

/-- **The degree as a homomorphism.** For a smooth proper curve `f: X ⟶ Spec k` and a
`k`-scheme `T`, the fibrewise degree `ℒ ↦ (t ↦ deg ℒ_t)` is a group homomorphism from `Pic (X_T)`
to the group of functions `T → ℤ` (written multiplicatively); it is natural in `T`
(`AlgebraicGeometry.picardPresheafDegreeHom_map`) and its values are locally constant
(`AlgebraicGeometry.isLocallyConstant_picardPresheafDegree`). -/
noncomputable def picardPresheafDegreeHom (T : Over (Spec (.of k))) :
    (pullback f T.hom).Pic →* (T.left → Multiplicative ℤ) where
  toFun L t := .ofAdd (picardPresheafDegree f L t)
  map_one' := funext fun t ↦ by
    change Multiplicative.ofAdd (picardPresheafDegree f (1 : (pullback f T.hom).Pic) t) = 1
    rw [picardPresheafDegree_one, ofAdd_zero]
  map_mul' L M := funext fun t ↦ by
    change Multiplicative.ofAdd (picardPresheafDegree f (L * M : (pullback f T.hom).Pic) t) = _
    rw [picardPresheafDegree_mul, ofAdd_add]
    rfl

lemma picardPresheafDegreeHom_apply (T : Over (Spec (.of k))) (L : (pullback f T.hom).Pic)
    (t : T.left) :
    picardPresheafDegreeHom f T L t = .ofAdd (picardPresheafDegree f L t) :=
  rfl

/-- **The degree homomorphism is natural**: the degree of the pullback of `ℒ` along `φ: T' ⟶ T`
is the degree of `ℒ` composed with `φ`. -/
lemma picardPresheafDegreeHom_map {T T' : Over (Spec (.of k))} (φ : T' ⟶ T)
    (L : (pullback f T.hom).Pic) (t : T'.left) :
    picardPresheafDegreeHom f T' (Pic.map (baseChangeMap f φ) L) t =
      picardPresheafDegreeHom f T L (φ.left t) :=
  congrArg Multiplicative.ofAdd (picardPresheafDegree_map f φ L t)

/-- **`Pic^0` is the kernel of the degree.** The classes of fibrewise degree zero are the kernel
of the degree homomorphism `AlgebraicGeometry.picardPresheafDegreeHom`. -/
theorem ker_picardPresheafDegreeHom (T : Over (Spec (.of k))) :
    (picardPresheafDegreeHom f T).ker = picardSubgroupDegreeZero f T := by
  ext L
  change _ ↔ L ∈ (picardSubfunctorDegree f 0).obj (.op T)
  rw [MonoidHom.mem_ker, mem_picardSubfunctorDegree_iff, funext_iff]
  exact forall_congr' fun t ↦ ofAdd_eq_one

/-- **`Pic^d · Pic^e ⊆ Pic^{d+e}`**: the product of a class of fibrewise degree `d` and a class
of fibrewise degree `e` has fibrewise degree `d + e`. -/
theorem mul_mem_picardSubfunctorDegree {T : Over (Spec (.of k))} {d e : ℤ}
    {L M : (pullback f T.hom).Pic} (hL : L ∈ (picardSubfunctorDegree f d).obj (.op T))
    (hM : M ∈ (picardSubfunctorDegree f e).obj (.op T)) :
    L * M ∈ (picardSubfunctorDegree f (d + e)).obj (.op T) := fun K _ _ t ↦ by
  rw [picardFibreDegree_mul f t L M, hL K t, hM K t]

/-- The inverse of a class of fibrewise degree `d` has fibrewise degree `-d`. -/
theorem inv_mem_picardSubfunctorDegree {T : Over (Spec (.of k))} {d : ℤ}
    {L : (pullback f T.hom).Pic} (hL : L ∈ (picardSubfunctorDegree f d).obj (.op T)) :
    L⁻¹ ∈ (picardSubfunctorDegree f (-d)).obj (.op T) := fun K _ _ t ↦ by
  have h := picardFibreDegree_mul f t L⁻¹ L
  rw [inv_mul_cancel, picardFibreDegree_one, hL K t] at h
  omega

attribute [local instance] sheafifyGroup in
/-- **The degree on `Pic_{X/k}` is a homomorphism of sheaves of groups.** For sections `x`, `y`
of the relative Picard functor over `T`, with the group law that the sheafification inherits
from the Picard presheaf (`CategoryTheory.sheafifyGroup`), the degree of `x * y` is the sum of
the degrees of `x` and `y`. -/
theorem picardDegree_mul {T : Over (Spec (.of k))}
    (x y : (sheafify (fppfTopology.over (Spec (.of k)))
      (picardPresheafGrp f ⋙ forget GrpCat)).obj (.op T)) :
    picardDegree f (x * y) = picardDegree f x + picardDegree f y := by
  let J := fppfTopology.over (Spec (.of k))
  funext t
  obtain ⟨Z, g, ⟨⟨L, hL⟩, ⟨M, hM⟩⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (J.intersection_covering (SheafifyGrp.imageSieve_mem (J := J) x)
      (SheafifyGrp.imageSieve_mem (J := J) y)) t
  rw [Pi.add_apply, picardDegree_eq f x g L hL, picardDegree_eq f y g M hM,
    picardDegree_eq f (x * y) g (L * M : (pullback f Z.hom).Pic)
      (map_sheafify_mul J (picardPresheafGrp f) x y g L M hL hM).symm, picardPresheafDegree_mul]

end DegreeHom

section SubgroupScheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The inclusion of `Pic^0` is a group homomorphism.** Let `P` represent `Pic_{X/k}` and `P₀`
represent `Pic^0_{X/k}`, both respecting the group laws, and let `j: P₀ ⟶ P` send the point of
`P₀` classifying a class of fibrewise degree zero to the point of `P` classifying the same
class. Then `j` is a morphism of group objects. -/
theorem isMonHom_of_isPicardMul {P P₀ : Over (Spec (.of k))} [GrpObj P] [GrpObj P₀]
    (hP : (picardFunctor f).obj.RepresentableBy P) (hPm : IsPicardMul f hP)
    (e : (picardFunctorDegree f 0).obj.RepresentableBy P₀) (he : IsPicardZeroMul f e)
    (hsub : ∀ {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic),
      L ∈ (picardSubfunctorDegree f 0).obj (.op T) →
        M ∈ (picardSubfunctorDegree f 0).obj (.op T) →
          L * M ∈ (picardSubfunctorDegree f 0).obj (.op T))
    (j : P₀ ⟶ P)
    (hj : ∀ {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T))
      (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op T)),
      e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨L, hL⟩) ≫ j =
        hP.homEquiv.symm ((toPicardFunctor f).app (.op T) L)) :
    IsMonHom j := by
  let J := fppfTopology.over (Spec (.of k))
  let S := (picardSubfunctorDegree f 0).toFunctor
  have hmul {Y : Over (Spec (.of k))} (a b : Y ⟶ P₀) : (a * b) ≫ j = (a ≫ j) * (b ≫ j) := by
    apply hP.homEquiv.injective
    refine SheafifyGrp.ext (J := J) (P := picardPresheaf f) _
      (J.intersection_covering (SheafifyGrp.imageSieve_mem (J := J) (P := S) (e.homEquiv a))
        (SheafifyGrp.imageSieve_mem (J := J) (P := S) (e.homEquiv b)))
      fun Z g ⟨⟨⟨L, hL₀⟩, hL⟩, ⟨⟨M, hM₀⟩, hM⟩⟩ ↦ ?_
    have ha : g ≫ a = e.homEquiv.symm ((toSheafify J S).app (.op Z) ⟨L, hL₀⟩) := by
      rw [hL]; exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g a)
    have hb : g ≫ b = e.homEquiv.symm ((toSheafify J S).app (.op Z) ⟨M, hM₀⟩) := by
      rw [hM]; exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g b)
    have hLM := he (T := Z) L M hL₀ hM₀ (hsub L M hL₀ hM₀)
    refine (hP.homEquiv_comp g _).symm.trans (Eq.trans ?_ (hP.homEquiv_comp g _))
    congr 1
    rw [← Category.assoc, MonObj.comp_mul, ha, hb, ← hLM, hj, hPm, MonObj.comp_mul,
      ← Category.assoc, ← Category.assoc, ha, hb, hj, hj]
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    have h := hmul (1 : 𝟙_ _ ⟶ P₀) 1
    rw [_root_.mul_one] at h
    exact mul_eq_left.mp h.symm
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd]

/-- **The comparison of two Jacobians is a homomorphism.** Let `J` and `J'` be group schemes
representing `Pic^0_{X/k}` by `e` and `e'`, both respecting the group laws. Then the unique
isomorphism `u: J ≅ J'` compatible with `e` and `e'`
(`CategoryTheory.Functor.RepresentableBy.uniqueUpToIso`) is a morphism of group objects. -/
theorem isMonHom_uniqueUpToIso_hom_of_isPicardZeroMul [SmoothOfRelativeDimension 1 f]
    [IsProper f] {J J' : Over (Spec (.of k))} [GrpObj J] [GrpObj J']
    (e : (picardFunctorDegree f 0).obj.RepresentableBy J) (he : IsPicardZeroMul f e)
    (e' : (picardFunctorDegree f 0).obj.RepresentableBy J') (he' : IsPicardZeroMul f e') :
    IsMonHom (e.uniqueUpToIso e').hom := by
  let Jt := fppfTopology.over (Spec (.of k))
  let S := (picardSubfunctorDegree f 0).toFunctor
  let u := e.uniqueUpToIso e'
  have hsub {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic)
      (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op T))
      (hM : M ∈ (picardSubfunctorDegree f 0).obj (.op T)) :
      L * M ∈ (picardSubfunctorDegree f 0).obj (.op T) := by
    simpa using mul_mem_picardSubfunctorDegree f hL hM
  have hj {T : Over (Spec (.of k))} (s : (picardFunctorDegree f 0).obj.obj (.op T)) :
      e.homEquiv.symm s ≫ u.hom = e'.homEquiv.symm s := by
    apply e'.homEquiv.injective
    rw [Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_hom, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have hmul {Y : Over (Spec (.of k))} (a b : Y ⟶ J) :
      (a * b) ≫ u.hom = (a ≫ u.hom) * (b ≫ u.hom) := by
    apply e'.homEquiv.injective
    refine SheafifyGrp.ext (J := Jt) (P := S) _
      (Jt.intersection_covering (SheafifyGrp.imageSieve_mem (J := Jt) (P := S) (e.homEquiv a))
        (SheafifyGrp.imageSieve_mem (J := Jt) (P := S) (e.homEquiv b)))
      fun Z g ⟨⟨⟨L, hL₀⟩, hL⟩, ⟨⟨M, hM₀⟩, hM⟩⟩ ↦ ?_
    have ha : g ≫ a = e.homEquiv.symm ((toSheafify Jt S).app (.op Z) ⟨L, hL₀⟩) := by
      rw [hL]
      exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g a)
    have hb : g ≫ b = e.homEquiv.symm ((toSheafify Jt S).app (.op Z) ⟨M, hM₀⟩) := by
      rw [hM]
      exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g b)
    refine (e'.homEquiv_comp g _).symm.trans (Eq.trans ?_ (e'.homEquiv_comp g _))
    congr 1
    rw [← Category.assoc, MonObj.comp_mul, ha, hb, ← he L M hL₀ hM₀ (hsub L M hL₀ hM₀), hj,
      he' L M hL₀ hM₀ (hsub L M hL₀ hM₀), MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      ha, hb, hj, hj]
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    have h := hmul (1 : 𝟙_ _ ⟶ J) 1
    rw [_root_.mul_one] at h
    exact mul_eq_left.mp h.symm
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd]

/-- **Uniqueness of the Jacobian.** Let `J` and `J'` be group schemes representing `Pic^0_{X/k}`
by `e` and `e'`, both respecting the group laws. Then there is a unique isomorphism `u: J ≅ J'`
with `e' ∘ h_u = e`, and it is an isomorphism of group schemes. -/
theorem existsUnique_iso_isMonHom_of_isPicardZeroMul [SmoothOfRelativeDimension 1 f]
    [IsProper f] {J J' : Over (Spec (.of k))} [GrpObj J] [GrpObj J']
    (e : (picardFunctorDegree f 0).obj.RepresentableBy J) (he : IsPicardZeroMul f e)
    (e' : (picardFunctorDegree f 0).obj.RepresentableBy J') (he' : IsPicardZeroMul f e') :
    ∃! u : J ≅ J', (∀ {T : Over (Spec (.of k))} (a : T ⟶ J),
      e'.homEquiv (a ≫ u.hom) = e.homEquiv a) ∧ IsMonHom u.hom := by
  obtain ⟨u, hu, huniq⟩ := Functor.RepresentableBy.existsUnique_iso e e'
  have hu' : u = e.uniqueUpToIso e' :=
    (huniq _ fun a ↦ Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_hom e e' a).symm
  refine ⟨u, ⟨hu, hu' ▸ isMonHom_uniqueUpToIso_hom_of_isPicardZeroMul f e he e' he'⟩,
    fun v hv ↦ huniq v hv.1⟩

variable [IsSepClosed k] [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **`Pic^0` is an open and closed subgroup scheme of the Picard scheme.** Let `X` be a smooth
projective curve over a separably closed field `k` and let `P` represent `Pic_{X/k}`. Then `P`
is a commutative group scheme whose group law is the tensor product of invertible modules, and
its decomposition into the open and closed subschemes `P^d` representing `Pic^d_{X/k}`
(`AlgebraicGeometry.exists_decomposition_picardFunctor_representableBy`) can be chosen such
that `P^0` is a commutative group scheme representing `Pic^0_{X/k}` compatibly with the group
laws, and the open immersion `P^0 ⟶ P` is a morphism of group objects. -/
theorem exists_decomposition_picardFunctor_isMonHom (P : Over (Spec (.of k)))
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) :
    ∃ (_ : CommGrpObj P) (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P)
      (e : ∀ d, (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d))
      (_ : CommGrpObj (Pd 0)),
      IsPicardMul (X ↘ Spec (.of k)) hP ∧ IsPicardZeroMul (X ↘ Spec (.of k)) (e 0) ∧
      IsMonHom (j 0) ∧
      (∀ d, IsOpenImmersion (j d).left) ∧
      (∀ d, IsClopen (Set.range (j d).left.base)) ∧
      (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
      (⋃ d, Set.range (j d).left.base) = Set.univ := by
  obtain ⟨Pd, j, e, h₁, -, h₂, h₃, h₄, hj⟩ :=
    exists_decomposition_picardFunctor_representableBy P hP
  obtain ⟨_, hPm⟩ := exists_commGrpObj_isPicardMul (X ↘ Spec (.of k)) hP
  obtain ⟨_, he⟩ := exists_commGrpObj_isPicardZeroMul (X ↘ Spec (.of k)) (e 0)
  refine ⟨inferInstance, Pd, j, e, inferInstance, hPm, he,
    isMonHom_of_isPicardMul _ hP hPm (e 0) he (fun L M hL hM ↦ ?_) (j 0) (hj 0), h₁, h₂, h₃, h₄⟩
  simpa using mul_mem_picardSubfunctorDegree (X ↘ Spec (.of k)) hL hM

end SubgroupScheme

section Translation

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Translation by a class of degree `e`.** Let `M ∈ Pic X` have degree `e` and `d' = d + e`.
Schemes `P`, `P'` representing `Pic^d_{X/k}` and `Pic^{d'}_{X/k}` are isomorphic through an
isomorphism whose functor of points is tensoring with `pr_X^* M`: the point of `P` classifying a
class `ℒ` is sent to the point of `P'` classifying `ℒ ⊗ pr_X^* M`
(`AlgebraicGeometry.picardSubfunctorDegreeMulMapFst`). -/
theorem exists_iso_representableBy_picardFunctorDegree {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) (P P' : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P)
    (hP' : (picardFunctorDegree (X ↘ Spec (.of k)) d').obj.RepresentableBy P') :
    ∃ φ : P ≅ P', ∀ {T : Over (Spec (.of k))}
      (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor.obj (.op T)),
      hP.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) L) ≫ φ.hom =
        hP'.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor).app (.op T)
            ((picardSubfunctorDegreeMulMapFst M hM h).app (.op T) L)) := by
  let J := fppfTopology.over (Spec (.of k))
  let ε := picardSubfunctorDegreeIsoOfDegree M hM h
  let E := (sheafToPresheaf J _).mapIso ((presheafToSheaf J (Type (u + 1))).mapIso ε)
  let R' := hP'.ofIso E.symm
  refine ⟨hP.uniqueUpToIso R', fun {T} L ↦ ?_⟩
  rw [eq_comm, Equiv.symm_apply_eq]
  have h₁ := hP.homEquiv_comp_uniqueUpToIso_hom R'
    (hP.homEquiv.symm ((toSheafify J (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app
      (.op T) L))
  rw [Equiv.apply_symm_apply] at h₁
  have h₂ := ((E.app (.op T)).toEquiv.symm_apply_eq).1 h₁
  refine Eq.trans ?_ h₂.symm
  exact (congr_arg (fun ψ ↦ ψ.app (.op T) L) (toSheafify_naturality J ε.hom))

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- Tensoring with the pullback `pr_X^* M` of a class `M ∈ Pic X`, as an endomorphism of the
Picard presheaf `T ↦ Pic (X_T)`. -/
noncomputable def picardPresheafMulMapFst (M : X.Pic) :
    picardPresheaf (X ↘ Spec (.of k)) ⟶ picardPresheaf (X ↘ Spec (.of k)) where
  app T := TypeCat.ofHom fun L ↦ (show (pullback (X ↘ Spec (.of k)) T.unop.hom).Pic from L) *
    Pic.map (pullback.fst (X ↘ Spec (.of k)) T.unop.hom) M
  naturality {T T'} φ := by
    ext L
    exact (pic_map_baseChangeMap_mul_map_fst φ.unop L M).symm

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
lemma picardPresheafMulMapFst_app_apply (M : X.Pic) (T : (Over (Spec (.of k)))ᵒᵖ)
    (L : (pullback (X ↘ Spec (.of k)) T.unop.hom).Pic) :
    (picardPresheafMulMapFst M).app T L =
      L * Pic.map (pullback.fst (X ↘ Spec (.of k)) T.unop.hom) M :=
  rfl

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- Tensoring with `pr_X^* M` is an automorphism of the Picard presheaf, with inverse tensoring
with `pr_X^* M⁻¹`. -/
noncomputable def picardPresheafMulMapFstIso (M : X.Pic) :
    picardPresheaf (X ↘ Spec (.of k)) ≅ picardPresheaf (X ↘ Spec (.of k)) where
  hom := picardPresheafMulMapFst M
  inv := picardPresheafMulMapFst M⁻¹
  hom_inv_id := by
    ext T L
    change _ * _ * _ = _
    rw [show Pic.map _ M⁻¹ = (Pic.map _ M)⁻¹ from map_inv (Pic.mapHom _) M,
      mul_inv_cancel_right]
    rfl
  inv_hom_id := by
    ext T L
    change _ * _ * _ = _
    rw [show Pic.map _ M⁻¹ = (Pic.map _ M)⁻¹ from map_inv (Pic.mapHom _) M,
      inv_mul_cancel_right]
    rfl

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **Translation on the Picard scheme.** Let `P` represent the relative Picard functor
`Pic_{X/k}` through `hP` and let `M ∈ Pic X`. The translation `τ_M: P ≅ P` is the automorphism
of `P` whose functor of points is the sheafification of `ℒ ↦ ℒ ⊗ pr_X^* M`: a `T`-point `x` of
`P` is sent to the point `hP.homEquiv.symm (x · (a_M)_T)` (`picardTranslation_homEquiv`,
`picardTranslation_hom_eq_mul`), where `a_M` is the `k`-point `[M]`. -/
noncomputable def picardTranslation {P : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) (M : X.Pic) : P ≅ P :=
  hP.uniqueUpToIso (hP.ofIso ((sheafToPresheaf (fppfTopology.over (Spec (.of k))) _).mapIso
    ((presheafToSheaf (fppfTopology.over (Spec (.of k))) (Type (u + 1))).mapIso
      (picardPresheafMulMapFstIso M))).symm)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- The functor of points of the translation `τ_M` is the sheafification of tensoring with
`pr_X^* M`. -/
lemma picardTranslation_homEquiv {P : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) (M : X.Pic)
    {T : Over (Spec (.of k))} (a : T ⟶ P) :
    hP.homEquiv (a ≫ (picardTranslation hP M).hom) =
      (sheafifyMap (fppfTopology.over (Spec (.of k))) (picardPresheafMulMapFst M)).app (.op T)
        (hP.homEquiv a) := by
  have h := hP.homEquiv_comp_uniqueUpToIso_hom (hP.ofIso
    ((sheafToPresheaf (fppfTopology.over (Spec (.of k))) _).mapIso
      ((presheafToSheaf (fppfTopology.over (Spec (.of k))) (Type (u + 1))).mapIso
        (picardPresheafMulMapFstIso M))).symm) a
  exact (((((sheafToPresheaf (fppfTopology.over (Spec (.of k))) _).mapIso
      ((presheafToSheaf (fppfTopology.over (Spec (.of k))) (Type (u + 1))).mapIso
        (picardPresheafMulMapFstIso M))).app (.op T)).toEquiv.symm_apply_eq).1 h)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **The translation `τ_M` on points coming from invertible modules**: the point classifying
`ℒ ∈ Pic (X_T)` is sent to the point classifying `ℒ ⊗ pr_X^* M`. -/
lemma homEquiv_symm_toPicardFunctor_comp_picardTranslation_hom {P : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) (M : X.Pic)
    {T : Over (Spec (.of k))} (L : (pullback (X ↘ Spec (.of k)) T.hom).Pic) :
    hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T) L) ≫
        (picardTranslation hP M).hom =
      hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T)
        (L * Pic.map (pullback.fst (X ↘ Spec (.of k)) T.hom) M)) := by
  rw [Equiv.eq_symm_apply, picardTranslation_homEquiv, Equiv.apply_symm_apply]
  exact (congr_arg (fun ψ ↦ ψ.app (.op T) L)
    (toSheafify_naturality (fppfTopology.over (Spec (.of k))) (picardPresheafMulMapFst M))).symm

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **The inverse of `τ_M` is `τ_{M⁻¹}`.** For `M = 𝒪_X(dx)` this says `τ_d⁻¹ = τ_{-d}`. -/
theorem picardTranslation_inv {P : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) (M : X.Pic) :
    (picardTranslation hP M).inv = (picardTranslation hP M⁻¹).hom := by
  have h : sheafifyMap (fppfTopology.over (Spec (.of k))) (picardPresheafMulMapFst M) ≫
      sheafifyMap (fppfTopology.over (Spec (.of k))) (picardPresheafMulMapFst M⁻¹) = 𝟙 _ := by
    rw [← sheafifyMap_comp]
    exact (congrArg (sheafifyMap (fppfTopology.over (Spec (.of k))))
      (picardPresheafMulMapFstIso M).hom_inv_id).trans (sheafifyMap_id _ _)
  refine Iso.inv_ext (hP.homEquiv.injective ?_)
  rw [← Category.id_comp ((picardTranslation hP M).hom ≫ _), ← Category.assoc,
    picardTranslation_homEquiv, picardTranslation_homEquiv]
  exact congr_arg (fun ψ ↦ ψ.app (.op P) (hP.homEquiv (𝟙 P))) h

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **`τ_M` is translation by the `k`-point `[M]`.** If `P` is a group scheme representing
`Pic_{X/k}` compatibly with the group laws, then `τ_M = m ∘ (id, a_M ∘ π)`: a `T`-point `x` is
sent to `x · (a_M)_T`, where `a_M: Spec k ⟶ P` classifies `M` and `π: T ⟶ Spec k`. -/
theorem picardTranslation_hom_eq_mul {P : Over (Spec (.of k))} [GrpObj P]
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P)
    (hPm : IsPicardMul (X ↘ Spec (.of k)) hP) (M : X.Pic) {T : Over (Spec (.of k))}
    (a : T ⟶ P) :
    a ≫ (picardTranslation hP M).hom = a * (toUnit T ≫ hP.homEquiv.symm
      ((toPicardFunctor (X ↘ Spec (.of k))).app (.op (𝟙_ (Over (Spec (.of k)))))
        (Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) M))) := by
  apply hP.homEquiv.injective
  refine SheafifyGrp.ext (J := fppfTopology.over (Spec (.of k)))
    (P := picardPresheaf (X ↘ Spec (.of k))) _
    (SheafifyGrp.imageSieve_mem (J := fppfTopology.over (Spec (.of k))) (hP.homEquiv a))
    fun Z g ⟨L, hL⟩ ↦ ?_
  have ha : g ≫ a = hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op Z) L) := by
    refine hP.homEquiv.eq_symm_apply.2 ((hP.homEquiv_comp g a).trans ?_)
    exact hL.symm
  have hb (N : (pullback (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom).Pic) :
      toUnit Z ≫ hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app _ N) =
        hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op Z)
          (Pic.map (baseChangeMap (X ↘ Spec (.of k)) (toUnit Z)) N)) := by
    rw [hP.comp_homEquiv_symm]
    exact congrArg hP.homEquiv.symm
      (NatTrans.naturality_apply (toPicardFunctor (X ↘ Spec (.of k))) (toUnit Z).op N).symm
  have hfst : baseChangeMap (X ↘ Spec (.of k)) (toUnit Z) ≫
      pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom =
        pullback.fst (X ↘ Spec (.of k)) Z.hom :=
    pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  refine (hP.homEquiv_comp g _).symm.trans (Eq.trans ?_ (hP.homEquiv_comp g _))
  congr 1
  rw [← Category.assoc, ha, homEquiv_symm_toPicardFunctor_comp_picardTranslation_hom,
    MonObj.comp_mul, ha, ← Category.assoc, comp_toUnit, hb, ← Pic.map_comp, hfst, hPm]

/-- **The translation restricts to the translation between degree components.** Let `P`
represent `Pic_{X/k}`, let `j: P^d ⟶ P` and `j': P^{d'} ⟶ P` be the inclusions of schemes
representing `Pic^d_{X/k}` and `Pic^{d'}_{X/k}`, compatible with the representations, and let
`φ: P^d ≅ P^{d'}` act on points by tensoring with `pr_X^* M`, where `M ∈ Pic X` has degree
`e = d' - d` (`AlgebraicGeometry.exists_iso_representableBy_picardFunctorDegree`). Then the
translation `τ_M` of `P` restricts to `φ`: `j ≫ τ_M = φ ≫ j'`. -/
theorem comp_picardTranslation_hom {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) {P Pd Pd' : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P)
    (ed : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy Pd)
    (ed' : (picardFunctorDegree (X ↘ Spec (.of k)) d').obj.RepresentableBy Pd')
    (j : Pd ⟶ P) (j' : Pd' ⟶ P)
    (hj : ∀ {T : Over (Spec (.of k))} (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
      (hL : L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) d).obj (.op T)),
      ed.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) ⟨L, hL⟩) ≫ j =
        hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T) L))
    (hj' : ∀ {T : Over (Spec (.of k))} (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
      (hL : L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) d').obj (.op T)),
      ed'.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor).app (.op T) ⟨L, hL⟩) ≫ j' =
        hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T) L))
    (φ : Pd ≅ Pd')
    (hφ : ∀ {T : Over (Spec (.of k))}
      (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor.obj (.op T)),
      ed.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) L) ≫ φ.hom =
        ed'.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor).app (.op T)
            ((picardSubfunctorDegreeMulMapFst M hM h).app (.op T) L))) :
    j ≫ (picardTranslation hP M).hom = φ.hom ≫ j' := by
  apply hP.homEquiv.injective
  refine SheafifyGrp.ext (J := fppfTopology.over (Spec (.of k)))
    (P := picardPresheaf (X ↘ Spec (.of k))) _
    (SheafifyGrp.imageSieve_mem (J := fppfTopology.over (Spec (.of k)))
      (P := (picardSubfunctorDegree _ d).toFunctor) (ed.homEquiv (𝟙 Pd))) fun Z g ⟨L, hL⟩ ↦ ?_
  have hg : g = ed.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
      (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op Z) L) := by
    refine ed.homEquiv.eq_symm_apply.2 ?_
    have h' := ed.homEquiv_comp g (𝟙 Pd)
    rw [Category.comp_id] at h'
    exact h'.trans hL.symm
  have h₁ : g ≫ j = hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op Z) L.1) :=
    (congrArg (· ≫ j) hg).trans (hj L.1 L.2)
  have h₂ : (g ≫ φ.hom) ≫ j' = hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app
      (.op Z) ((picardSubfunctorDegreeMulMapFst M hM h).app (.op Z) L).1) :=
    (congrArg (· ≫ j') ((congrArg (· ≫ φ.hom) hg).trans (hφ L))).trans
      (hj' _ ((picardSubfunctorDegreeMulMapFst M hM h).app (.op Z) L).2)
  refine (hP.homEquiv_comp g _).symm.trans (Eq.trans ?_ (hP.homEquiv_comp g _))
  congr 1
  rw [← Category.assoc, h₁, homEquiv_symm_toPicardFunctor_comp_picardTranslation_hom,
    ← Category.assoc, h₂]
  rfl

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **The inverse translation restricts to the inverse.** In the situation of
`comp_picardTranslation_hom`, the translation `τ_{M⁻¹} = τ_M⁻¹` of `P` restricts to `φ⁻¹`:
`j' ≫ τ_{M⁻¹} = φ⁻¹ ≫ j`. -/
theorem comp_picardTranslation_inv_hom {P Pd Pd' : Over (Spec (.of k))}
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) (M : X.Pic)
    (j : Pd ⟶ P) (j' : Pd' ⟶ P) (φ : Pd ≅ Pd')
    (hφ : j ≫ (picardTranslation hP M).hom = φ.hom ≫ j') :
    j' ≫ (picardTranslation hP M⁻¹).hom = φ.inv ≫ j := by
  rw [← picardTranslation_inv, eq_comm, Iso.inv_comp_eq, ← Category.assoc, ← hφ,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **`Pic^0 ≅ Pic^d` by tensoring with `𝒪_X(dx)`.** Let `X` be a smooth projective curve over a
field `k` and let `x` be a rational point of `X`. There is an isomorphism between
schemes `P₀`, `P_d` representing `Pic^0_{X/k}` and `Pic^d_{X/k}` whose functor of points is
`ℒ ↦ ℒ ⊗ pr_X^* 𝒪_X(dx)`. Here `𝒪_X(dx)` is the class `M` of `𝒪_X(-x)^{⊗(-d)}`, `𝒪_X(-x)` the
ideal sheaf of `x`, and the inverse isomorphism is tensoring with `pr_X^* 𝒪_X(-dx)`. -/
theorem exists_iso_representableBy_picardFunctorDegree_zero (d : ℤ)
    (x : (X ↘ Spec (.of k)).fieldPoints k) (P₀ Pd : Over (Spec (.of k)))
    (hP₀ : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy P₀)
    (hPd : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy Pd) :
    ∃ (M : X.Pic) (hM : picDegreeHom k X M = .ofAdd d),
      (letI := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules;
        M = Pic.ofIsInvertible x.1.ker.toModules ^ (-d)) ∧
      ∃ φ : P₀ ≅ Pd, ∀ {T : Over (Spec (.of k))}
        (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor.obj (.op T)),
        hP₀.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor).app (.op T) L) ≫ φ.hom =
          hPd.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T)
              ((picardSubfunctorDegreeMulMapFst M hM (zero_add d).symm).app (.op T) L)) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
  have hM : picDegreeHom k X (Pic.ofIsInvertible x.1.ker.toModules ^ (-d)) = .ofAdd d := by
    rw [map_zpow, picDegreeHom_ofIsInvertible, degree_toModules_ker_fieldPoints, ← ofAdd_zsmul,
      smul_eq_mul, neg_mul_neg, _root_.mul_one]
  exact ⟨_, hM, rfl, exists_iso_representableBy_picardFunctorDegree _ hM _ P₀ Pd hP₀ hPd⟩


/-- **Translation by `𝒪_X(dx)` on the Picard scheme, restricted to the degree components.** Let
`X` be a smooth projective curve over a separably closed field `k`, `x` a rational point, and
`P` a scheme representing `Pic_{X/k}`, with its decomposition into the open and closed
subschemes `P^d` representing `Pic^d_{X/k}` (`exists_decomposition_picardFunctor_representableBy`).
Let `M = 𝒪_X(dx)` and let `τ_d = picardTranslation hP M` be the translation of `P` by the
`k`-point `[𝒪_X(dx)]`, whose inverse is `τ_{-d} = picardTranslation hP M⁻¹`
(`picardTranslation_inv`). Then `τ_d` restricts to an isomorphism `φ: P^0 ≅ P^d` which on
points is tensoring with `pr_X^* 𝒪_X(dx)`, i.e. `j_0 ≫ τ_d = φ ≫ j_d`, and `τ_{-d}` restricts to
its inverse, `j_d ≫ τ_{-d} = φ⁻¹ ≫ j_0`. -/
theorem exists_decomposition_picardTranslation [IsSepClosed k] (d : ℤ)
    (x : (X ↘ Spec (.of k)).fieldPoints k) (P : Over (Spec (.of k)))
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) :
    ∃ (M : X.Pic) (hM : picDegreeHom k X M = .ofAdd d),
      (letI := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules;
        M = Pic.ofIsInvertible x.1.ker.toModules ^ (-d)) ∧
      ∃ (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P)
        (e : ∀ d, (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d)),
        (∀ d, IsOpenImmersion (j d).left) ∧
        (∀ d, IsClopen (Set.range (j d).left.base)) ∧
        (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
        (⋃ d, Set.range (j d).left.base) = Set.univ ∧
        (∀ d {T : Over (Spec (.of k))} (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
          (hL : L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) d).obj (.op T)),
          (e d).homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
              (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) ⟨L, hL⟩) ≫
            j d = hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T) L)) ∧
        ∃ φ : Pd 0 ≅ Pd d,
          (∀ {T : Over (Spec (.of k))}
            (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor.obj (.op T)),
            (e 0).homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
                (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor).app (.op T) L) ≫
              φ.hom = (e d).homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
                (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T)
                  ((picardSubfunctorDegreeMulMapFst M hM (zero_add d).symm).app (.op T) L))) ∧
          j 0 ≫ (picardTranslation hP M).hom = φ.hom ≫ j d ∧
          j d ≫ (picardTranslation hP M⁻¹).hom = φ.inv ≫ j 0 := by
  obtain ⟨Pd, j, e, h₁, -, h₂, h₃, h₄, hj⟩ :=
    exists_decomposition_picardFunctor_representableBy P hP
  obtain ⟨M, hM, hMx, φ, hφ⟩ :=
    exists_iso_representableBy_picardFunctorDegree_zero d x (Pd 0) (Pd d) (e 0) (e d)
  have hτ := comp_picardTranslation_hom M hM (zero_add d).symm hP (e 0) (e d) (j 0) (j d)
    (hj 0) (hj d) φ hφ
  exact ⟨M, hM, hMx, Pd, j, e, h₁, h₂, h₃, h₄, hj, φ, hφ, hτ,
    comp_picardTranslation_inv_hom hP M (j 0) (j d) φ hτ⟩

end Translation

end AlgebraicGeometry
