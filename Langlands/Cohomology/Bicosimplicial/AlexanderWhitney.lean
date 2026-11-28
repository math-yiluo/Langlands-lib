import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.BigOperators.Fin
import Langlands.Cohomology.ModuleComplex.TensorSignsUpNat

/-!
# The Alexander–Whitney comparison for bicosimplicial modules

Let `F : SimplexCategory × SimplexCategory ⥤ ModuleCat R` be a bicosimplicial module. This
file constructs

* `diagonalComplex F`, the alternating-coface cochain complex of the diagonal
  `[n] ↦ F([n], [n])`;
* `bicomplex F`, the double complex whose rows and columns are the alternating-coface
  complexes in the two simplicial directions (the first factor is the horizontal, outer
  index `p`), and `totalComplex F`, its total complex, whose differential on the
  summand of bidegree `(p, q)` is `d₁ + (-1) ^ p • d₂`;
* `alexanderWhitney F : totalComplex F ⟶ diagonalComplex F`, the cochain map which on the
  summand `F([p], [q])` of degree `n = p + q` is `F` applied to the pair of the front face
  `[p] → [n]`, `i ↦ i`, and the back face `[q] → [n]`, `i ↦ i + p`;
* `alexanderWhitneyNatTrans`, the comparison as a natural transformation between the
  functors `totalComplexFunctor R` and `diagonalComplexFunctor R`.

Eilenberg and Zilber, *On Products of Complexes*, Amer. J. Math. 75 (1953), 200–204,
§§1–3, establish the chain comparison for products of simplicial sets. The cochain
formula used here is given by Grunenfelder and Mastnak, *Cohomology of abelian
matched pairs and the Kac sequence*, J. Algebra 276 (2004), 706–736, Appendix A.2–A.3.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Prod AlgebraicTopology
open scoped Simplicial

namespace Langlands.Cohomology.Bicosimplicial

/-! ### Front and back faces -/

section Faces

open SimplexCategory

/-- The face `subinterval j l` sends `i` to `i + j`. -/
lemma subinterval_toOrderHom_val {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ((subinterval j l hjl).toOrderHom i : ℕ) = (i : ℕ) + j := rfl

/-- The coface `δ i` skips the value `i`. -/
lemma δ_toOrderHom_val {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    (((δ i).toOrderHom k : Fin (n + 2)) : ℕ) =
      if (k : ℕ) < (i : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  change ((i.succAbove k : Fin (n + 2)) : ℕ) = _
  by_cases hk : (k : ℕ) < (i : ℕ)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hk),
      Fin.succAbove_of_castSucc_lt _ _ (by rwa [Fin.lt_def])]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hk),
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.val_castSucc]; omega)]
    rfl

/-- Two morphisms of `SimplexCategory` agree when their values agree as natural numbers. -/
lemma hom_ext_of_val {m n : ℕ} {f g : ⦋m⦌ ⟶ ⦋n⦌}
    (h : ∀ x : Fin (m + 1), ((f.toOrderHom x : Fin (n + 1)) : ℕ) = (g.toOrderHom x : ℕ)) :
    f = g := by
  ext x : 3
  exact Fin.val_injective (h x)

/-- A coface `δ k` with `k ≤ p` composed after the front face `[p] → [n]` is the
front face `[p + 1] → [n + 1]` composed after `δ k`. -/
lemma subinterval_zero_comp_δ {n p : ℕ} (h : 0 + p ≤ n) (k : Fin (n + 2)) (j : Fin (p + 2))
    (hkj : (k : ℕ) = j) :
    subinterval 0 p h ≫ δ k = δ j ≫ subinterval 0 (p + 1) (by omega) := by
  refine hom_ext_of_val fun x => ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val, Nat.add_zero, hkj]

/-- A coface `δ k` with `p < k` composed after the front face `[p] → [n]` is the front
face `[p] → [n + 1]`. -/
lemma subinterval_zero_comp_δ_of_lt {n p : ℕ} (h : 0 + p ≤ n) (k : Fin (n + 2))
    (hk : p < (k : ℕ)) :
    subinterval 0 p h ≫ δ k = subinterval 0 p (by omega) := by
  refine hom_ext_of_val fun x => ?_
  have hx : (x : ℕ) ≤ p := Nat.lt_succ_iff.mp x.isLt
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val, Nat.add_zero]
  by_cases h₁ : (x : ℕ) < k
  · simp only [h₁, ite_true]
  · simp only [h₁, ite_false]
    omega

/-- A coface `δ k` with `k ≤ p` composed after the back face `[q] → [n]`, `i ↦ i + p`, is
the back face `[q] → [n + 1]`, `i ↦ i + (p + 1)`. -/
lemma subinterval_comp_δ_of_le {n p q : ℕ} (h : p + q ≤ n) (k : Fin (n + 2))
    (hk : (k : ℕ) ≤ p) :
    subinterval p q h ≫ δ k = subinterval (p + 1) q (by omega) := by
  refine hom_ext_of_val fun x => ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val]
  by_cases h₁ : (x : ℕ) + p < k <;> simp only [h₁, ite_true, ite_false] <;> omega

/-- A coface `δ k` with `k = j + p` composed after the back face `[q] → [n]` is the back
face `[q + 1] → [n + 1]` composed after `δ j`. -/
lemma subinterval_comp_δ {n p q : ℕ} (h : p + q ≤ n) (k : Fin (n + 2)) (j : Fin (q + 2))
    (hkj : (k : ℕ) = j + p) :
    subinterval p q h ≫ δ k = δ j ≫ subinterval p (q + 1) (by omega) := by
  refine hom_ext_of_val fun x => ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val]
  by_cases h₁ : (x : ℕ) + p < k <;> by_cases h₂ : (x : ℕ) < j <;>
    simp only [h₁, h₂, ite_true, ite_false] <;> omega

/-- The last coface of `[p + 1]` followed by the front face `[p + 1] → [n]` is the front
face `[p] → [n]`. -/
lemma δ_last_comp_subinterval_zero {n p : ℕ} (h : 0 + (p + 1) ≤ n) :
    δ (Fin.last (p + 1)) ≫ subinterval 0 (p + 1) h = subinterval 0 p (by omega) := by
  refine hom_ext_of_val fun x => ?_
  have hx : (x : ℕ) ≤ p := Nat.lt_succ_iff.mp x.isLt
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val, Fin.val_last, Nat.add_zero]
  by_cases h₁ : (x : ℕ) < p + 1
  · simp only [h₁, ite_true]
  · simp only [h₁, ite_false]
    omega

/-- The first coface of `[q + 1]` followed by the back face `[q + 1] → [n]`, `i ↦ i + p`,
is the back face `[q] → [n]`, `i ↦ i + (p + 1)`. -/
lemma δ_zero_comp_subinterval {n p q : ℕ} (h : p + (q + 1) ≤ n) :
    δ (0 : Fin (q + 2)) ≫ subinterval p (q + 1) h = subinterval (p + 1) q (by omega) := by
  refine hom_ext_of_val fun x => ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    subinterval_toOrderHom_val, δ_toOrderHom_val, Fin.val_zero, Nat.not_lt_zero, ite_false]
  omega

end Faces

/-! ### The combinatorial identity -/

section Identity

private lemma add_eq_add_add_smul {M : Type*} [AddCommGroup M] {a a' b b' x y : M} {c : ℤ}
    (ha : a = a') (hb : b = c • b') (hxy : x + c • y = 0) :
    a + b = (a' + x) + c • (y + b') := by
  rw [ha, hb, smul_add, ← add_assoc, add_assoc a' x, hxy, add_zero]

private lemma map_mkHom_congr {C : Type*} [Category* C]
    (F : SimplexCategory × SimplexCategory ⥤ C) {X₁ X₂ Y₁ Y₂ : SimplexCategory}
    {f f' : X₁ ⟶ X₂} {g g' : Y₁ ⟶ Y₂} (h₁ : f = f') (h₂ : g = g') :
    F.map (f ×ₘ g) = F.map (f' ×ₘ g') := by
  rw [h₁, h₂]

variable {C : Type*} [Category* C] [Preadditive C] (F : SimplexCategory × SimplexCategory ⥤ C)

/-- The identity behind the cochain map property of the Alexander–Whitney map: for
`p + q = n`, the alternating sum over the cofaces `δ k`, `k ≤ n + 1`, applied to both the
front face `[p] → [n]` and the back face `[q] → [n]`, equals the alternating sum over the
cofaces of `[p + 1]` followed by the front and back faces in bidegree `(p + 1, q)`, plus
`(-1) ^ p` times the alternating sum over the cofaces of `[q + 1]` followed by the front
and back faces in bidegree `(p, q + 1)`. The terms `k ≤ p` give the first sum without its
last term, the terms `k = p + 1 + m` give the second sum without its first term, and the
two omitted terms cancel. -/
lemma sum_front_back (p q n : ℕ) (h : p + q = n) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.map ((SimplexCategory.subinterval 0 p (by omega) ≫ SimplexCategory.δ k) ×ₘ
          (SimplexCategory.subinterval p q (by omega) ≫ SimplexCategory.δ k)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          F.map ((SimplexCategory.δ i ≫ SimplexCategory.subinterval (n := n + 1) 0 (p + 1)
              (by omega)) ×ₘ SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega)) +
        (-1 : ℤ) ^ p • ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
          F.map (SimplexCategory.subinterval (n := n + 1) 0 p (by omega) ×ₘ
            (SimplexCategory.δ j ≫ SimplexCategory.subinterval (n := n + 1) p (q + 1)
              (by omega))) := by
  rw [← Fin.sum_congr' _ (show p + 1 + (q + 1) = n + 2 by omega),
    Fin.sum_univ_add (a := p + 1) (b := q + 1), Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1)]
  refine add_eq_add_add_smul ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact map_mkHom_congr F
      (subinterval_zero_comp_δ _ _ _
        (by simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]))
      (subinterval_comp_δ_of_le _ _ (by simp only [Fin.val_cast, Fin.val_castAdd]; omega))
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← pow_add]
    congr 1
    · congr 1
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    · exact map_mkHom_congr F
        (subinterval_zero_comp_δ_of_lt _ _
          (by simp only [Fin.val_cast, Fin.val_natAdd]; omega))
        (subinterval_comp_δ _ _ _
          (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega))
  · rw [δ_last_comp_subinterval_zero, δ_zero_comp_subinterval]
    simp only [Fin.val_last, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg, mul_one,
      neg_smul, neg_add_cancel]

/-- The identity `sum_front_back`, written with the coface differentials composed after the
front and back faces. -/
lemma front_back_comp_sum (p q n : ℕ) (h : p + q = n) :
    F.map (SimplexCategory.subinterval 0 p (by omega) ×ₘ
          SimplexCategory.subinterval p q (by omega)) ≫
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          F.map (SimplexCategory.δ k ×ₘ SimplexCategory.δ k) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • F.map (SimplexCategory.δ i ×ₘ 𝟙 ⦋q⦌)) ≫
          F.map (SimplexCategory.subinterval (n := n + 1) 0 (p + 1) (by omega) ×ₘ
            SimplexCategory.subinterval (n := n + 1) (p + 1) q (by omega)) +
        (-1 : ℤ) ^ p •
          ((∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • F.map (𝟙 ⦋p⦌ ×ₘ SimplexCategory.δ j)) ≫
            F.map (SimplexCategory.subinterval (n := n + 1) 0 p (by omega) ×ₘ
              SimplexCategory.subinterval (n := n + 1) p (q + 1) (by omega))) := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, ← Functor.map_comp, prod_comp, Category.id_comp]
  exact sum_front_back F p q n h

end Identity

/-! ### The diagonal and total cochain complexes -/

section Complexes

variable {R : Type u} [CommRing R] (F : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R)

/-- The alternating-coface cochain complex of the diagonal `[n] ↦ F([n], [n])` of a
bicosimplicial module `F`. -/
abbrev diagonalComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (Functor.diag SimplexCategory ⋙ F)

/-- The double complex of a bicosimplicial module `F`: its term of bidegree `(p, q)` is
`F([p], [q])`, its column of index `p` is the alternating-coface complex of
`[q] ↦ F([p], [q])`, and its horizontal differential is the alternating sum of the cofaces in
the first factor. -/
abbrev bicomplex :
    HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{v} R) ℕ)).obj
    (Functor.curry.obj F ⋙ alternatingCofaceMapComplex (ModuleCat.{v} R))

/-- The total cochain complex of the double complex of a bicosimplicial module `F`. Its
differential on the summand `F([p], [q])` is `d₁ + (-1) ^ p • d₂`, the signs being those of
the instance `Langlands.Cohomology.ModuleComplex.tensorSignsUpNat`. -/
abbrev totalComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  (bicomplex F).total (ComplexShape.up ℕ)

lemma diagonalComplex_X (n : ℕ) : (diagonalComplex F).X n = F.obj (⦋n⦌, ⦋n⦌) := rfl

lemma bicomplex_X_X (p q : ℕ) : ((bicomplex F).X p).X q = F.obj (⦋p⦌, ⦋q⦌) := rfl

/-- The differential of the diagonal complex is the alternating sum of the diagonal cofaces
`F(δ k, δ k)`. -/
lemma diagonalComplex_d (n : ℕ) :
    (diagonalComplex F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.map (SimplexCategory.δ k ×ₘ SimplexCategory.δ k) :=
  CochainComplex.of_d (fun n => (Functor.diag SimplexCategory ⋙ F).obj ⦋n⦌)
    (AlternatingCofaceMapComplex.objD (Functor.diag SimplexCategory ⋙ F)) n

/-- The horizontal differential of the double complex is the alternating sum of the cofaces
`F(δ i, 𝟙)` in the first factor. -/
lemma bicomplex_d_f (p q : ℕ) :
    ((bicomplex F).d p (p + 1)).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • F.map (SimplexCategory.δ i ×ₘ 𝟙 ⦋q⦌) := by
  have hd : (bicomplex F).d p (p + 1) = AlternatingCofaceMapComplex.objD
      (Functor.curry.obj F ⋙ alternatingCofaceMapComplex (ModuleCat.{v} R)) p :=
    CochainComplex.of_d (fun n => (Functor.curry.obj F ⋙
        alternatingCofaceMapComplex (ModuleCat.{v} R)).obj ⦋n⦌)
      (AlternatingCofaceMapComplex.objD
        (Functor.curry.obj F ⋙ alternatingCofaceMapComplex (ModuleCat.{v} R))) p
  rw [hd, ← HomologicalComplex.Hom.fAddMonoidHom_apply, AlternatingCofaceMapComplex.objD,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

/-- The vertical differential of the double complex is the alternating sum of the cofaces
`F(𝟙, δ j)` in the second factor. -/
lemma bicomplex_X_d (p q : ℕ) :
    ((bicomplex F).X p).d q (q + 1) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • F.map (𝟙 ⦋p⦌ ×ₘ SimplexCategory.δ j) :=
  CochainComplex.of_d (fun n => ((Functor.curry.obj F).obj ⦋p⦌).obj ⦋n⦌)
    (AlternatingCofaceMapComplex.objD ((Functor.curry.obj F).obj ⦋p⦌)) q

/-- The sign `ε₁` of the total complex is `1`. -/
lemma ε₁_up_ℕ (p q : ℕ) :
    ((ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) :
      ℤˣ) : ℤ) = 1 := rfl

/-- The sign `ε₂` of the total complex in bidegree `(p, q)` is `(-1) ^ p`. -/
lemma ε₂_up_ℕ (p q : ℕ) :
    ((ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) :
      ℤˣ) : ℤ) = (-1) ^ p := by
  change (((ComplexShape.up ℕ).ε p : ℤˣ) : ℤ) = _
  rw [Langlands.Cohomology.ModuleComplex.ε_up_ℕ, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]

variable {F} in
/-- The map of diagonal complexes induced by a morphism of bicosimplicial modules. -/
abbrev diagonalComplexMap {G : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R}
    (φ : F ⟶ G) : diagonalComplex F ⟶ diagonalComplex G :=
  (alternatingCofaceMapComplex (ModuleCat.{v} R)).map
    (Functor.whiskerLeft (Functor.diag SimplexCategory) φ)

variable {F} in
/-- The map of double complexes induced by a morphism of bicosimplicial modules. -/
abbrev bicomplexMap {G : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R}
    (φ : F ⟶ G) : bicomplex F ⟶ bicomplex G :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{v} R) ℕ)).map
    (Functor.whiskerRight (Functor.curry.map φ) (alternatingCofaceMapComplex (ModuleCat.{v} R)))

variable {F} in
/-- The map of total complexes induced by a morphism of bicosimplicial modules. -/
abbrev totalComplexMap {G : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R}
    (φ : F ⟶ G) : totalComplex F ⟶ totalComplex G :=
  HomologicalComplex₂.total.map (bicomplexMap φ) (ComplexShape.up ℕ)

variable (R)

/-- The diagonal complex as a functor of the bicosimplicial module. -/
def diagonalComplexFunctor :
    (SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R) ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategory) ⋙
    alternatingCofaceMapComplex _

/-- The double complex as a functor of the bicosimplicial module. -/
def bicomplexFunctor :
    (SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R) ⥤
      HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  Functor.curry ⋙ (Functor.whiskeringRight _ _ _).obj (alternatingCofaceMapComplex _) ⋙
    alternatingCofaceMapComplex _

/-- The total complex as a functor of the bicosimplicial module. -/
def totalComplexFunctor :
    (SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R) ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  bicomplexFunctor R ⋙ HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℕ)

variable {R}

lemma diagonalComplexFunctor_obj : (diagonalComplexFunctor R).obj F = diagonalComplex F := rfl

lemma bicomplexFunctor_obj : (bicomplexFunctor R).obj F = bicomplex F := rfl

lemma totalComplexFunctor_obj : (totalComplexFunctor R).obj F = totalComplex F := rfl

variable {F} {G : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R} (φ : F ⟶ G)

lemma diagonalComplexFunctor_map : (diagonalComplexFunctor R).map φ = diagonalComplexMap φ :=
  rfl

lemma bicomplexFunctor_map : (bicomplexFunctor R).map φ = bicomplexMap φ := rfl

lemma totalComplexFunctor_map : (totalComplexFunctor R).map φ = totalComplexMap φ := rfl

lemma diagonalComplexMap_f (n : ℕ) : (diagonalComplexMap φ).f n = φ.app (⦋n⦌, ⦋n⦌) := rfl

lemma bicomplexMap_f_f (p q : ℕ) : ((bicomplexMap φ).f p).f q = φ.app (⦋p⦌, ⦋q⦌) := rfl

end Complexes

/-! ### The Alexander–Whitney map -/

section AlexanderWhitney

variable {R : Type u} [CommRing R] (F : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R)

/-- The component of the Alexander–Whitney map on the summand `F([p], [q])` of degree
`n = p + q`: `F` applied to the pair of the front face `[p] → [n]`, `i ↦ i`, and the back
face `[q] → [n]`, `i ↦ i + p`. -/
def awComponent (p q n : ℕ) (h : p + q = n) :
    ((bicomplex F).X p).X q ⟶ (diagonalComplex F).X n :=
  F.map (SimplexCategory.subinterval 0 p (by omega) ×ₘ
    SimplexCategory.subinterval p q (by omega))

/-- The component of the Alexander–Whitney map followed by the diagonal differential equals
the horizontal differential followed by the component in bidegree `(p + 1, q)` plus
`(-1) ^ p` times the vertical differential followed by the component in bidegree
`(p, q + 1)`. -/
lemma awComponent_comp_d (p q n : ℕ) (h : p + q = n) :
    awComponent F p q n h ≫ (diagonalComplex F).d n (n + 1) =
      ((bicomplex F).d p (p + 1)).f q ≫ awComponent F (p + 1) q (n + 1) (by omega) +
        (-1 : ℤ) ^ p •
          (((bicomplex F).X p).d q (q + 1) ≫ awComponent F p (q + 1) (n + 1) (by omega)) := by
  rw [diagonalComplex_d, bicomplex_d_f, bicomplex_X_d]
  exact front_back_comp_sum F p q n h

/-- The Alexander–Whitney map from the total complex of a bicosimplicial module to the
alternating-coface complex of its diagonal. In degree `n` it is `awComponent F p q n` on the
summand `F([p], [q])` with `p + q = n`. -/
def alexanderWhitney : totalComplex F ⟶ diagonalComplex F where
  f n := (bicomplex F).totalDesc (A := (diagonalComplex F).X n)
    (fun p q h => awComponent F p q n h)
  comm' := by
    rintro n _ rfl
    refine HomologicalComplex₂.total.hom_ext _ fun p q h => ?_
    have h₀ : p + q = n := h
    rw [HomologicalComplex₂.ι_totalDesc_assoc, HomologicalComplex₂.total_d,
      Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc,
      HomologicalComplex₂.ι_D₂_assoc,
      HomologicalComplex₂.d₁_eq _ (ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q (n + 1)
        (show p + 1 + q = n + 1 by omega),
      HomologicalComplex₂.d₂_eq _ (ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) (n + 1)
        (show p + (q + 1) = n + 1 by omega),
      Units.smul_def, Units.smul_def, Preadditive.zsmul_comp, Preadditive.zsmul_comp,
      Category.assoc, Category.assoc, HomologicalComplex₂.ι_totalDesc,
      HomologicalComplex₂.ι_totalDesc, ε₁_up_ℕ, ε₂_up_ℕ, one_smul]
    exact awComponent_comp_d F p q n h₀

lemma alexanderWhitney_f (n : ℕ) :
    (alexanderWhitney F).f n = (bicomplex F).totalDesc (A := (diagonalComplex F).X n)
      (fun p q h => awComponent F p q n h) := rfl

/-- On the summand `F([p], [q])` of the total complex in degree `n = p + q`, the
Alexander–Whitney map is `F` applied to the front face `[p] → [n]` and the back face
`[q] → [n]`. -/
@[reassoc]
lemma ιTotal_alexanderWhitney_f (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    (bicomplex F).ιTotal (ComplexShape.up ℕ) p q n h ≫ (alexanderWhitney F).f n =
      awComponent F p q n h := by
  rw [alexanderWhitney_f, HomologicalComplex₂.ι_totalDesc]

variable {F} in
/-- The Alexander–Whitney map is natural in the bicosimplicial module. -/
@[reassoc]
lemma alexanderWhitney_naturality {G : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R}
    (φ : F ⟶ G) :
    totalComplexMap φ ≫ alexanderWhitney G = alexanderWhitney F ≫ diagonalComplexMap φ := by
  ext n : 1
  refine HomologicalComplex₂.total.hom_ext _ fun p q h => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc,
    ιTotal_alexanderWhitney_f, ιTotal_alexanderWhitney_f_assoc]
  exact (φ.naturality _).symm

variable (R) in
/-- The Alexander–Whitney map as a natural transformation from the total complex functor to
the diagonal complex functor. -/
def alexanderWhitneyNatTrans : totalComplexFunctor R ⟶ diagonalComplexFunctor R where
  app F := alexanderWhitney F
  naturality _ _ φ := alexanderWhitney_naturality φ

end AlexanderWhitney

end Langlands.Cohomology.Bicosimplicial
