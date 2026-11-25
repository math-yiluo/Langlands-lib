/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion

/-!
# Geometric points of an abelian variety over an arbitrary field

Let `A` be an abelian variety over a field `K`. Its group `A(K̄)` of geometric points, the
morphisms `Spec K̄ ⟶ A` over `K`, is the group of `K̄`-points of the base change `A_{K̄}`
(`AlgebraicGeometry.Scheme.geometricPointsAddEquivBaseChangePoints`, which holds for any group
scheme). Hence the results over algebraically closed fields apply: for `ℓ ≠ char K`, the group
`A(K̄)` is `ℓ`-divisible and its `ℓ ^ n`-torsion is finite.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.exists_zsmul_eq_geometricPoints`: `A(K̄)` is divisible.
- `AlgebraicGeometry.IsAbelianVariety.finite_torsionBy_geometricPoints`: `A(K̄)[ℓ ^ n]` is
  finite.
- `AlgebraicGeometry.IsAbelianVariety.exists_overIso_sigma_torsionSubgroupScheme`: for `n` prime
  to `char K`, `A[n]` becomes a disjoint union of `n ^ (2 * g)` points over a separably closed
  extension.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_addEquiv_torsionBy_points`: for `n` prime to
  `char K` and `K'` an algebraically closed extension, `A(K')[n] ≅ (ℤ/nℤ) ^ (2 * g)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A]

section Points

variable {L : Type u} [Field L] (g : Spec (.of L) ⟶ Spec (.of K))

noncomputable instance : GrpObj ((Over.pullback g).obj A) := Functor.grpObjObj

/-- The section of `Spec L ×_K Spec L ⟶ Spec L` through the diagonal, as an `L`-point of the
base change of `Spec L` to `L`. -/
noncomputable def pullbackDiagonalSection :
    𝟙_ (Over (Spec (.of L))) ⟶ (Over.pullback g).obj (Over.mk g) :=
  Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _)

omit [GrpObj A] in
variable {A g} in
lemma pullbackDiagonalSection_comp_map_left (a : Over.mk g ⟶ A) :
    (pullbackDiagonalSection g ≫ (Over.pullback g).map a).left =
      pullback.lift a.left (𝟙 _) (by simp) := by
  apply pullback.hom_ext
  · simp only [pullbackDiagonalSection, Over.comp_left, Over.homMk_left, Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact Category.id_comp _
  · simp [pullbackDiagonalSection, Over.pullback_map_left]

/-- The `L`-valued points of a group scheme `A` over `K`, i.e. the morphisms `Spec L ⟶ A` over
`K`, are the `L`-points of the base change `A_L`, as groups. -/
noncomputable def pointsAddEquivBaseChangePoints :
    Additive (Over.mk g ⟶ A) ≃+ Additive (𝟙_ (Over (Spec (.of L))) ⟶ (Over.pullback g).obj A)
    where
  toFun a := .ofMul (pullbackDiagonalSection g ≫ (Over.pullback g).map a.toMul)
  invFun b := .ofMul (Over.homMk (b.toMul.left ≫ pullback.fst _ _) (by
    have h : b.toMul.left ≫ pullback.snd A.hom g = 𝟙 _ := by simpa using Over.w b.toMul
    simp only [Over.mk_hom, Category.assoc, pullback.condition, reassoc_of% h]))
  left_inv a := by
    refine Additive.toMul.injective (Over.OverMorphism.ext ?_)
    change (pullbackDiagonalSection g ≫ (Over.pullback g).map a.toMul).left ≫ pullback.fst _ _ = _
    rw [pullbackDiagonalSection_comp_map_left, pullback.lift_fst]
  right_inv b := by
    refine Additive.toMul.injective (Over.OverMorphism.ext ?_)
    have h : b.toMul.left ≫ pullback.snd A.hom g = 𝟙 _ := by simpa using Over.w b.toMul
    simp only [toMul_ofMul, pullbackDiagonalSection_comp_map_left]
    apply pullback.hom_ext
    · simp
    · simp [h]
  map_add' a b := by
    refine congrArg Additive.ofMul ?_
    simp only [toMul_add, toMul_ofMul]
    rw [Functor.map_mul]
    exact MonObj.comp_mul _ _ _

end Points

/-- The base change `A_{K̄}` of a group scheme `A` over `K` to the algebraic closure. -/
noncomputable abbrev baseChangeAlgebraicClosure : Over (Spec (.of (AlgebraicClosure K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj A

/-- The geometric points `A(K̄)` of a group scheme `A` over `K` are the `K̄`-points of its base
change `A_{K̄}`, as groups. -/
noncomputable def geometricPointsAddEquivBaseChangePoints :
    Additive (Scheme.specAlgebraicClosure K ⟶ A) ≃+
      Additive (𝟙_ (Over (Spec (.of (AlgebraicClosure K)))) ⟶ baseChangeAlgebraicClosure A) :=
  pointsAddEquivBaseChangePoints A _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IsAbelianVariety

open Scheme

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]

/-- The geometric points `A(K̄)` of an abelian variety over any field form a divisible group. -/
theorem exists_zsmul_eq_geometricPoints (n : ℕ) (hn : 0 < n)
    (x : Additive (Scheme.specAlgebraicClosure K ⟶ A)) : ∃ y, (n : ℤ) • y = x := by
  let e := geometricPointsAddEquivBaseChangePoints A
  obtain ⟨a, ha⟩ := surjective_npow_points (A := baseChangeAlgebraicClosure A) n hn (e x).toMul
  refine ⟨e.symm (.ofMul a), ?_⟩
  rw [natCast_zsmul, ← map_nsmul, e.symm_apply_eq]
  exact congrArg Additive.ofMul ha

/-- For `ℓ ≠ char K`, the `ℓ ^ n`-torsion of the geometric points `A(K̄)` of an abelian variety
over `K` is finite. -/
theorem finite_torsionBy_geometricPoints (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar K ≠ ℓ)]
    (n : ℕ) :
    Finite (AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A))
      ((ℓ : ℤ) ^ n)) := by
  have hℓ : ℓ.Prime := Fact.out
  set p := ringChar K
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hp : ¬ p ∣ ℓ ^ n := by
    intro h
    rcases CharP.char_is_prime_or_zero K p with hp | hp
    · exact (Fact.out : p ≠ ℓ) ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
    · rw [hp, zero_dvd_iff] at h
      exact pow_ne_zero n hℓ.ne_zero h
  obtain ⟨f⟩ := nonempty_addEquiv_torsionBy p (baseChangeAlgebraicClosure A) (ℓ ^ n)
    (pow_pos hℓ.pos n) hp
  let e := geometricPointsAddEquivBaseChangePoints A
  refine Finite.of_injective (fun x ↦ f ⟨e x, ?_⟩) fun x y h ↦ ?_
  · rw [Nat.cast_pow]
    exact AddSubgroup.apply_mem_torsionBy e x.2
  · exact Subtype.ext (e.injective (congrArg Subtype.val (f.injective h)))


section BaseChange

variable {K' : Type u} [Field K'] [Algebra K K']

/-- Blueprint `proposition-multiplication-n--2`: Multiplication by `d` prime to the characteristic
is étale (the geometric fibre of `A[n]`).

Let `A` be an abelian variety of dimension `g` over a field `K` of characteristic `p`, let `n` be
prime to `p` and let `K'` be a separably closed field extension of `K`. Then the base change
`A[n]_{K'}` is, as a scheme over `K'`, the disjoint union of `n ^ (2 * g)` copies of `Spec K'`:
it is the constant scheme on a set with `n ^ (2 * g)` elements.

`A[n]` is finite étale of order `n ^ (2 * g)` (`AlgebraicGeometry.etale_torsionSubgroupScheme`,
`AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`), the order is invariant under base change,
and a finite étale scheme over a separably closed field is a disjoint union of copies of the
base (`AlgebraicGeometry.Scheme.Hom.exists_overIso_sigma_of_isSepClosed`). -/
theorem exists_overIso_sigma_torsionSubgroupScheme [IsSepClosed K'] (p : ℕ) [CharP K p] (n : ℕ)
    (hn : 0 < n) (hnp : ¬ p ∣ n) :
    ∃ (S : Type u) (_ : Finite S), Nat.card S = n ^ (2 * IsAbelianVariety.dim A) ∧
      Nonempty (Over.mk (pullback.snd (torsionSubgroupScheme A n).hom
          (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≅
        Over.mk (Sigma.desc fun _ : S ↦ 𝟙 (Spec (.of K')))) := by
  have := isFinite_torsionSubgroupScheme A n hn
  have := etale_torsionSubgroupScheme p A n hn hnp
  obtain ⟨S, hS, hcard, e⟩ := (torsionSubgroupScheme A n).hom.exists_overIso_sigma_of_isSepClosed
    (Spec.map (CommRingCat.ofHom (algebraMap K K')))
  refine ⟨S, hS, ?_, e⟩
  rw [hcard, Scheme.Hom.finrankΓ_pullback_snd, finrankΓ_torsionSubgroupScheme n hn]

/-- Blueprint `proposition-multiplication-n--2`: Multiplication by `d` prime to the characteristic
is étale (the geometric points of `A[n]`).

Let `A` be an abelian variety of dimension `g` over a field `K` of characteristic `p`, let `n` be
prime to `p` and let `K'` be an algebraically closed field extension of `K`. Then the
`n`-torsion of the group `A(K')` of `K'`-valued points of `A` (the morphisms `Spec K' ⟶ A` over
`K`) is `(ℤ/nℤ) ^ (2 * g)`.

`A(K')` is the group of `K'`-points of the abelian variety `A_{K'}`
(`AlgebraicGeometry.Scheme.pointsAddEquivBaseChangePoints`), hence divisible. For a prime
`ℓ ∣ n`, the `ℓ`-torsion of `A(K')` is the set of `K'`-points of `A[ℓ]`
(`AlgebraicGeometry.torsionByPointsEquiv`), that is of the finite étale `A[ℓ]_{K'}`, which has
`ℓ ^ (2 * g)` of them (`AlgebraicGeometry.card_points_eq_finrankΓ`); then
`AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime` concludes. -/
theorem nonempty_addEquiv_torsionBy_points [IsAlgClosed K'] (p : ℕ) [CharP K p] (n : ℕ)
    (hn : 0 < n) (hnp : ¬ p ∣ n) :
    Nonempty (AddSubgroup.torsionBy
        (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * IsAbelianVariety.dim A) → ZMod n)) := by
  set y := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  let e := pointsAddEquivBaseChangePoints A y
  let _ : DivisibleBy (Additive (Over.mk y ⟶ A)) ℤ :=
    divisibleByOfSMulRightSurj _ _ fun {m} hm x ↦ by
      obtain ⟨a, ha⟩ := surjective_npow_points (A := (Over.pullback y).obj A) m.natAbs
        (Int.natAbs_pos.2 hm) (e x).toMul
      refine ⟨m.sign • e.symm (.ofMul a), show m • (m.sign • _) = x from ?_⟩
      rw [smul_smul, Int.mul_sign_self, natCast_zsmul, ← map_nsmul, e.symm_apply_eq]
      exact congrArg Additive.ofMul ha
  refine AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime _ _ hn.ne' fun ℓ hℓ hℓn ↦ ?_
  have hℓp : ¬ p ∣ ℓ := fun h ↦ hnp (h.trans hℓn)
  have := isFinite_torsionSubgroupScheme A ℓ hℓ.pos
  have := etale_torsionSubgroupScheme p A ℓ hℓ.pos hℓp
  have : IsFinite ((Over.pullback y).obj (torsionSubgroupScheme A ℓ)).hom :=
    inferInstanceAs (IsFinite (pullback.snd _ _))
  have : Etale ((Over.pullback y).obj (torsionSubgroupScheme A ℓ)).hom :=
    inferInstanceAs (Etale (pullback.snd _ _))
  rw [Nat.card_congr (torsionByPointsEquiv A ℓ (Over.mk y))]
  calc Nat.card (Over.mk y ⟶ torsionSubgroupScheme A ℓ)
      = Nat.card (𝟙_ (Over (Spec (.of K'))) ⟶ (Over.pullback y).obj (torsionSubgroupScheme A ℓ)) :=
        Nat.card_congr (pointsAddEquivBaseChangePoints _ y).toEquiv
    _ = ((Over.pullback y).obj (torsionSubgroupScheme A ℓ)).hom.finrankΓ :=
        card_points_eq_finrankΓ _
    _ = ℓ ^ (2 * IsAbelianVariety.dim A) :=
      (Scheme.Hom.finrankΓ_pullback_snd _ y).trans (finrankΓ_torsionSubgroupScheme ℓ hℓ.pos)

end BaseChange

end AlgebraicGeometry.IsAbelianVariety
