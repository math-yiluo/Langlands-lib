/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Étale cohomology over a clopen decomposition

Let `X = U₁ ⊔ ⋯ ⊔ Uᵣ` be a decomposition of a scheme into finitely many pairwise disjoint
clopen subsets. An abelian étale sheaf `F` on `X` is the direct sum of the direct images
`ιᵢ_* ιᵢ^* F` of its restrictions, and the direct image along the closed immersion `ιᵢ` does
not change cohomology, so `Hⁿ(X, F)` is the product of the `Hⁿ(Uᵢ, ιᵢ^* F)`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`: for a finite morphism `f : X ⟶ Y`
  the edge map `Hⁿ(Y, f_* G) ⟶ Hⁿ(X, G)` is bijective in every degree.
- `AlgebraicGeometry.Etale.nonempty_equiv_pi_H_of_isClopen`: `Hⁿ(X, F) ≅ ∏ᵢ Hⁿ(Uᵢ, F|_{Uᵢ})`.
- `AlgebraicGeometry.Etale.subsingleton_H_of_isClopen`: `Hⁿ(X, F)` vanishes if its
  restrictions to the pieces of a finite clopen decomposition do.
-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y : Scheme.{u}}

/-- **The edge map of a finite morphism is bijective.** For a finite morphism `f : X ⟶ Y` the
direct image `f_*` is exact, so the Leray spectral sequence degenerates and the edge map
`Hⁿ(Y, f_* G) ⟶ Hⁿ(X, G)` is bijective in every degree. -/
theorem bijective_edgeMap_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) n ↦
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) n
        (cohomologyMap f _ n x) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  convert (Ext.precompAddEquiv ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
    (AddCommGrpCat.of (ULift ℤ))) G n).bijective.comp
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).mapExtCounit_bijective _ G n) using 1
  funext x
  exact map_counit_cohomologyMap f G n x

/-- **Étale cohomology over a clopen decomposition.** Let `U : ι → X.Opens` be a finite
family of pairwise disjoint closed opens covering `X`, and let `F` be an abelian étale sheaf
on `X`. Then the restriction maps `Hⁿ(X, F) ⟶ Hⁿ(Uᵢ, F|_{Uᵢ})` assemble to a bijection
`Hⁿ(X, F) ⟶ ∏ᵢ Hⁿ(Uᵢ, F|_{Uᵢ})`. -/
theorem bijective_pi_cohomologyMap_of_isClopen {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X)) (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) :
    Function.Bijective fun (x : Sheaf.H F n) (i : ι) ↦ cohomologyMap (U i).ι F n x := by
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (i : ι) : IsClosedImmersion (U i).ι :=
    .of_isOpenImmersion _ (by simpa using hU i)
  let adj (i : ι) := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (U i).ι
  let G (i : ι) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    ((U i).ι)_*[AddCommGrpCat.{u + 1}].obj (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F)
  let φ : F ⟶ ⨁ G := biproduct.lift fun i ↦ (adj i).unit.app F
  -- `φ` is an isomorphism, as it is one after restricting to every `U j`
  have hφ : IsIso φ := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun i ↦ (U i).ι) (fun x ↦ ?_) φ fun j ↦ ?_
    · obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    let P := ((U j).ι)^*[AddCommGrpCat.{u + 1}]
    have hz (i : ι) (hij : i ≠ j) : IsZero (P.obj (G i)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ (U j).ι (U i).ι
        (by simpa using (hdisj hij).symm) _
    have hπ : IsIso (P.map (biproduct.π G j)) := by
      refine ⟨P.map (biproduct.ι G j), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G), P.map_sum,
          Finset.sum_eq_single j (fun i _ hij ↦ ?_) (by simp)]
        rw [P.map_comp, (hz i hij).eq_zero_of_tgt (P.map (biproduct.π G i)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have hunit : IsIso (P.map ((adj j).unit.app F)) := by
      have : IsIso (P.map ((adj j).unit.app F) ≫ (adj j).counit.app (P.obj F)) := by
        rw [(adj j).left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ ((adj j).counit.app (P.obj F))
    have : IsIso (P.map φ ≫ P.map (biproduct.π G j)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact IsIso.of_isIso_comp_right _ (P.map (biproduct.π G j))
  let e₁ : Sheaf.H F n ≃ Sheaf.H (⨁ G) n :=
    { toFun := Sheaf.H.map φ n
      invFun := Sheaf.H.map (inv φ) n
      left_inv x := by rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv x := by rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply] }
  let e : Sheaf.H F n ≃ ∀ i, Sheaf.H (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n :=
    e₁.trans ((Ext.addEquivBiproduct _ (biproduct.isBilimit G) n).toEquiv.trans
      (Equiv.piCongrRight fun i ↦ Equiv.ofBijective _
        (bijective_edgeMap_of_isFinite (U i).ι _ n)))
  convert e.bijective using 1
  funext x i
  change _ = Sheaf.H.map ((adj i).counit.app _) n (cohomologyMap (U i).ι _ n
    ((Sheaf.H.map φ n x).comp (Ext.mk₀ (biproduct.π G i)) (add_zero n)))
  rw [← Sheaf.H.map_apply, ← Sheaf.H.map_comp_apply, biproduct.lift_π, cohomologyMap_map]
  refine (Sheaf.H.map_id_apply _).symm.trans ?_
  rw [← (adj i).left_triangle_components F, Sheaf.H.map_comp_apply]
  rfl

/-- **Étale cohomology over a clopen decomposition.** Let `U : ι → X.Opens` be a finite
family of pairwise disjoint closed opens covering `X`, and let `F` be an abelian étale sheaf
on `X`. Then `Hⁿ(X, F) ≅ ∏ᵢ Hⁿ(Uᵢ, F|_{Uᵢ})` (as sets), by
`AlgebraicGeometry.Etale.bijective_pi_cohomologyMap_of_isClopen`. -/
theorem nonempty_equiv_pi_H_of_isClopen {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X)) (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) :
    Nonempty (Sheaf.H F n ≃ ∀ i, Sheaf.H (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n) :=
  ⟨Equiv.ofBijective _ (bijective_pi_cohomologyMap_of_isClopen U hU hdisj hcov F n)⟩

/-- **Vanishing over a clopen decomposition.** Let `U : ι → X.Opens` be a finite family of
pairwise disjoint closed opens covering `X`, and let `F` be an abelian étale sheaf on `X`. If
`Hⁿ(Uᵢ, F|_{Uᵢ}) = 0` for every `i`, then `Hⁿ(X, F) = 0`
(`AlgebraicGeometry.Etale.nonempty_equiv_pi_H_of_isClopen`). -/
theorem subsingleton_H_of_isClopen {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X)) (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (hF : ∀ i, Subsingleton (Sheaf.H (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n)) :
    Subsingleton (Sheaf.H F n) :=
  (nonempty_equiv_pi_H_of_isClopen U hU hdisj hcov F n).some.subsingleton

/-- Two factorisations `f ≫ g = f' ≫ g'` of the same morphism give pullback maps on cohomology
which agree up to a bijection
(`AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_of_comp_eq`). -/
lemma exists_bijective_cohomologyMap_cohomologyMap_eq {Z Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z) (h : f ≫ g = f' ≫ g')
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∃ A : Sheaf.H ((f')^*[AddCommGrpCat.{u + 1}].obj ((g')^*[AddCommGrpCat.{u + 1}].obj F)) n →
      Sheaf.H ((f)^*[AddCommGrpCat.{u + 1}].obj ((g)^*[AddCommGrpCat.{u + 1}].obj F)) n,
      Function.Bijective A ∧ ∀ x, cohomologyMap f _ n (cohomologyMap g F n x) =
        A (cohomologyMap f' _ n (cohomologyMap g' F n x)) := by
  have hb := bijective_mk₀_comp_comp_mk₀ (cohomologyMapCompIso f g (f ≫ g) rfl).hom
    ((upperStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl).hom.app F) n
  have hb' := bijective_mk₀_comp_comp_mk₀ (cohomologyMapCompIso f' g' (f ≫ g) h.symm).hom
    ((upperStarComp AddCommGrpCat.{u + 1} f' g' (f ≫ g) h).hom.app F) n
  refine ⟨_ ∘ (Equiv.ofBijective _ hb').symm, hb.comp (Equiv.bijective _), fun x ↦ ?_⟩
  rw [cohomologyMap_cohomologyMap_of_comp_eq f g _ rfl,
    cohomologyMap_cohomologyMap_of_comp_eq f' g' (f ≫ g) h.symm]
  simp only [Function.comp_apply]
  congr 2
  exact ((Equiv.ofBijective _ hb').symm_apply_apply _).symm


variable {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsClosed (U i : Set X))
  (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j)) (hcov : ∀ x : X, ∃ i, x ∈ U i)
include hU hdisj hcov

/-- The pullback map along `g : Y ⟶ X` and the restriction maps to the pieces of a finite
clopen decomposition of `X` and of its preimage in `Y` commute, up to bijections. -/
lemma exists_bijective_pi_cohomologyMap_eq (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∃ A : ∀ i, Sheaf.H ((g ∣_ U i)^*[AddCommGrpCat.{u + 1}].obj
        (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F)) n →
      Sheaf.H (((g ⁻¹ᵁ U i).ι)^*[AddCommGrpCat.{u + 1}].obj
        ((g)^*[AddCommGrpCat.{u + 1}].obj F)) n,
      (∀ i, Function.Bijective (A i)) ∧
      Function.Bijective (fun (y : Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj F) n) (i : ι) ↦
        cohomologyMap (g ⁻¹ᵁ U i).ι _ n y) ∧
      Function.Bijective (fun (x : Sheaf.H F n) (i : ι) ↦ cohomologyMap (U i).ι F n x) ∧
      ∀ x i, cohomologyMap (g ⁻¹ᵁ U i).ι _ n (cohomologyMap g F n x) =
        A i (cohomologyMap (g ∣_ U i) _ n (cohomologyMap (U i).ι F n x)) := by
  choose A hA hAx using fun i ↦ exists_bijective_cohomologyMap_cohomologyMap_eq
    ((g ⁻¹ᵁ U i).ι) g (g ∣_ U i) (U i).ι (morphismRestrict_ι g (U i)).symm F n
  refine ⟨A, hA, bijective_pi_cohomologyMap_of_isClopen (fun i ↦ g ⁻¹ᵁ U i)
    (fun i ↦ (hU i).preimage g.continuous) (fun i j hij ↦ (hdisj hij).preimage g)
    (fun y ↦ hcov (g y)) _ n, bijective_pi_cohomologyMap_of_isClopen U hU hdisj hcov F n,
    fun x i ↦ hAx i x⟩

/-- **Bijectivity of pullback maps over a clopen decomposition.** Let `U` be a finite clopen
decomposition of `X` and `g : Y ⟶ X`. If the pullback maps along the restrictions
`g⁻¹(Uᵢ) ⟶ Uᵢ` are bijective in degree `n`, then so is the pullback map along `g`. -/
theorem bijective_cohomologyMap_of_isClopen (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ i, Function.Bijective
      (cohomologyMap (g ∣_ U i) (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n)) :
    Function.Bijective (cohomologyMap g F n) := by
  obtain ⟨A, hA, hR', hR, hAx⟩ := exists_bijective_pi_cohomologyMap_eq U hU hdisj hcov g F n
  have hP : Function.Bijective fun (y : ∀ i, Sheaf.H (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n)
      (i : ι) ↦ A i (cohomologyMap (g ∣_ U i) _ n (y i)) := by
    refine ⟨fun y y' hy ↦ funext fun i ↦ (h i).1 ((hA i).1 (congr_fun hy i)), fun z ↦ ?_⟩
    choose y hy using fun i ↦ ((hA i).comp (h i)).2 (z i)
    exact ⟨y, funext hy⟩
  rw [← Function.Bijective.of_comp_iff' hR']
  convert hP.comp hR using 1
  funext x
  exact funext (hAx x)

/-- **Surjectivity of pullback maps over a clopen decomposition.** Let `U` be a finite clopen
decomposition of `X` and `g : Y ⟶ X`. If the pullback maps along the restrictions
`g⁻¹(Uᵢ) ⟶ Uᵢ` are surjective in degree `n`, then so is the pullback map along `g`. -/
theorem surjective_cohomologyMap_of_isClopen (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ i, Function.Surjective
      (cohomologyMap (g ∣_ U i) (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n)) :
    Function.Surjective (cohomologyMap g F n) := by
  obtain ⟨A, hA, hR', hR, hAx⟩ := exists_bijective_pi_cohomologyMap_eq U hU hdisj hcov g F n
  intro z
  choose y hy using fun i ↦ ((hA i).2.comp (h i)) (cohomologyMap (g ⁻¹ᵁ U i).ι _ n z)
  obtain ⟨x, hx⟩ := hR.2 y
  refine ⟨x, hR'.1 (funext fun i ↦ ?_)⟩
  have hxi : cohomologyMap (U i).ι F n x = y i := congr_fun hx i
  dsimp only
  rw [hAx, hxi]
  exact hy i


end AlgebraicGeometry.Etale
