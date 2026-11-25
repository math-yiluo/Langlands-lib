/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.DegreeDecomposition
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# The rational points of `Pic^d`

Let `X` be a smooth projective geometrically integral curve over a separably closed field `k`.
For every `d ∈ ℤ`, the `k`-points of the degree-`d` part `Pic^d_{X/k}` of the relative Picard
functor are the invertible modules of degree `d` on `X`. For `d = 0` this is
`AlgebraicGeometry.exists_picardZero_equiv_picardFunctorDegree_zero`.

## Main statements

- `AlgebraicGeometry.exists_picardDegree_equiv_picardFunctorDegree`: the bijection between the
  classes of degree `d` in `Pic X` and `Pic^d_{X/k}(k)`.
- `AlgebraicGeometry.theorem_of_the_base`: all clauses of the theorem of the base bundled in one
  statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The `k`-points of `Pic^d_{X/k}` are the invertible modules of degree `d`.** For a smooth
projective geometrically integral curve `X` over a separably closed field `k` and `d ∈ ℤ`, the
map sending a class `ℒ ∈ Pic X` of degree `d` to the image of its pullback to `X ×_k k` is a
bijection onto `Pic^d_{X/k}(k)`. -/
theorem exists_picardDegree_equiv_picardFunctorDegree [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (d : ℤ) :
    ∃ Φ : {L : X.Pic // picDegreeHom k X L = .ofAdd d} ≃
      (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.obj (.op (𝟙_ (Over (Spec (.of k))))),
      ∀ L, ∃ h, Φ L = (toSheafify (fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app _
          ⟨Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) L.1, h⟩ := by
  set f := X ↘ Spec (.of k)
  let T₀ := 𝟙_ (Over (Spec (.of k)))
  let J := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f d
  -- a class of degree `d` on `X` pulls back to a class of fibrewise degree `d` on `X_k`
  have hmem (L : {L : X.Pic // picDegreeHom k X L = .ofAdd d}) :
      Pic.map (pullback.fst f T₀.hom) L.1 ∈ S.obj (.op T₀) := by
    intro K _ _ t
    rw [picardFibreDegree_map_fst]
    have h := L.2
    rw [picDegreeHom_apply, Hom.picDegree_eq] at h
    exact Multiplicative.ofAdd.injective h
  -- the split exact sequence at `T₀ = Spec k`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨pt⟩ := Hom.nonempty_fieldPoints (k := k) f
  have hσ : pt.1 ≫ f = 𝟙 _ := by
    rw [pt.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsplit := bijective_pic_split f pt.1 hσ
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T₀
  -- `X_k ⟶ X` is an isomorphism
  have : IsIso (pullback.fst f T₀.hom) := inferInstanceAs (IsIso (pullback.fst f (𝟙 _)))
  have hinv (L : X.Pic) :
      Pic.map (inv (pullback.fst f T₀.hom)) (Pic.map (pullback.fst f T₀.hom) L) = L := by
    rw [← Pic.map_comp, IsIso.inv_hom_id, Pic.map_id]
  have hinv' (M : (pullback f T₀.hom).Pic) :
      Pic.map (pullback.fst f T₀.hom) (Pic.map (inv (pullback.fst f T₀.hom)) M) = M := by
    rw [← Pic.map_comp, IsIso.hom_inv_id, Pic.map_id]
  let φ (L : {L : X.Pic // picDegreeHom k X L = .ofAdd d}) :
      (picardFunctorDegree f d).obj.obj (.op T₀) :=
    (toSheafify J S.toFunctor).app _ ⟨_, hmem L⟩
  refine ⟨Equiv.ofBijective φ ⟨fun L₁ L₂ h ↦ ?_, fun s ↦ ?_⟩, fun L ↦ ⟨hmem L, rfl⟩⟩
  · have h' := congrArg ((picardFunctorDegreeι f d).hom.app _) h
    simp only [φ] at h'
    rw [picardFunctorDegreeι_app_toSheafify, picardFunctorDegreeι_app_toSheafify] at h'
    have hM := hsplit.1 (a₁ := Pic.map (pullback.fst f T₀.hom) L₁.1)
      (a₂ := Pic.map (pullback.fst f T₀.hom) L₂.1)
      (Prod.ext (Subsingleton.elim (h := Pic.subsingleton_spec_field k) _ _) h')
    exact Subtype.ext (by rw [← hinv L₁.1, hM, hinv])
  · -- the image of `s` in `Pic_{X/k}(k)` comes from a class `M` on `X_k` of degree `d`
    obtain ⟨M, hM⟩ := hsplit.2 (1, (picardFunctorDegreeι f d).hom.app _ s)
    have hM₂ : (toPicardFunctor f).app _ M = (picardFunctorDegreeι f d).hom.app _ s :=
      congrArg Prod.snd hM
    have hMS : M ∈ S.obj (.op T₀) := (mem_picardSubfunctorDegree_iff f d M).2 fun t ↦ by
      rw [← picardDegree_toPicardFunctor, hM₂]
      exact picardDegree_picardFunctorDegreeι f d s t
    have hL₀ : picDegreeHom k X (Pic.map (inv (pullback.fst f T₀.hom)) M) = .ofAdd d := by
      have h := hMS k (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (Category.comp_id _))
      rw [← hinv' M, picardFibreDegree_map_fst] at h
      rw [picDegreeHom_apply, Hom.picDegree_eq, h]
    refine ⟨⟨_, hL₀⟩, injective_picardFunctorDegreeι_app f d T₀ ?_⟩
    simp only [φ]
    rw [picardFunctorDegreeι_app_toSheafify]
    dsimp only
    rw [hinv' M]
    exact hM₂

/-- **The theorem of the base.** Let `X` be a smooth projective geometrically integral curve of
genus `g = dim_k H¹(X, 𝒪_X)` over a separably closed field `k`. Then the Picard functor
`Pic_{X/k}` is represented by a commutative group scheme `P` (with group law the tensor product)
which is the disjoint union of open and closed subschemes `P^d`, `d ∈ ℤ`, such that:
* `P^d` represents `Pic^d_{X/k}`, and is proper, smooth of relative dimension `g` and
  geometrically integral over `k` (a `g`-dimensional smooth proper `k`-variety);
* the `k`-points of `P^d` are the invertible modules of degree `d` on `X`, via the class of their
  pullback to `X ×_k k`;
* `P^d` represents `Pic^d_{X/k}` through `e d`, compatibly with the inclusion `j d: P^d ⟶ P`
  and the inclusion `Pic^d_{X/k} ⊆ Pic_{X/k}`: the point of `P^d` classifying a class `ℒ` of
  fibrewise degree `d` is mapped by `j d` to the point of `P` classifying `ℒ`;
* `P^0` is a commutative group scheme representing `Pic^0_{X/k}` compatibly with the group laws,
  and the open and closed immersion `P^0 ⟶ P` is a morphism of group schemes. -/
theorem theorem_of_the_base [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ (P : Over (Spec (.of k))) (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P)
      (_ : CommGrpObj P) (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P)
      (e : ∀ d, (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d))
      (_ : CommGrpObj (Pd 0)),
      IsPicardMul (X ↘ Spec (.of k)) hP ∧ IsPicardZeroMul (X ↘ Spec (.of k)) (e 0) ∧
      IsMonHom (j 0) ∧
      (∀ d, IsOpenImmersion (j d).left) ∧
      (∀ d, IsClopen (Set.range (j d).left.base)) ∧
      (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
      (⋃ d, Set.range (j d).left.base) = Set.univ ∧
      (∀ d {T : Over (Spec (.of k))} (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
        (hL : L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) d).obj (.op T)),
        (e d).homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) ⟨L, hL⟩) ≫
          j d = hP.homEquiv.symm ((toPicardFunctor (X ↘ Spec (.of k))).app (.op T) L)) ∧
      (∀ d, IsProper (Pd d).hom ∧ SmoothOfRelativeDimension (arithmeticGenus k X) (Pd d).hom ∧
        GeometricallyIntegral (Pd d).hom) ∧
      ∀ d, ∃ Φ : {L : X.Pic // picDegreeHom k X L = .ofAdd d} ≃
        (𝟙_ (Over (Spec (.of k))) ⟶ Pd d),
        ∀ L, ∃ h, (e d).homEquiv (Φ L) = (toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app _
            ⟨Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) L.1,
              h⟩ := by
  obtain ⟨P, -, hP, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, j, e, h₁, -, h₂, h₃, h₄, hj⟩ :=
    exists_decomposition_picardFunctor_representableBy P hP
  obtain ⟨_, hPm⟩ := exists_commGrpObj_isPicardMul (X ↘ Spec (.of k)) hP
  obtain ⟨_, he⟩ := exists_commGrpObj_isPicardZeroMul (X ↘ Spec (.of k)) (e 0)
  have hj₀ : IsMonHom (j 0) :=
    isMonHom_of_isPicardMul _ hP hPm (e 0) he (fun L M hL hM ↦ by
      simpa using mul_mem_picardSubfunctorDegree (X ↘ Spec (.of k)) hL hM) (j 0) (hj 0)
  refine ⟨P, hP, inferInstance, Pd, j, e, inferInstance, hPm, he, hj₀, h₁, h₂, h₃, h₄, hj,
    fun d ↦ ⟨isProper_of_representableBy_picardFunctorDegree d _ (e d),
      smoothOfRelativeDimension_of_representableBy_picardFunctorDegree d _ (e d),
      geometricallyIntegral_of_representableBy_picardFunctorDegree d _ (e d)⟩, fun d ↦ ?_⟩
  obtain ⟨Φ, hΦ⟩ := exists_picardDegree_equiv_picardFunctorDegree (k := k) (X := X) d
  refine ⟨Φ.trans (e d).homEquiv.symm, fun L ↦ ?_⟩
  obtain ⟨h, hL⟩ := hΦ L
  exact ⟨h, by rw [Equiv.trans_apply, Equiv.apply_symm_apply, hL]⟩

end AlgebraicGeometry
