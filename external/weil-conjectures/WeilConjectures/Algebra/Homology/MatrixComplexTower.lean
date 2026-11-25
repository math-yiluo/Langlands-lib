/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MatrixComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-!
# Towers of matrix complexes over an adic ring

Let `R` be a commutative ring with a tower of quotients `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n` with `π n = ρ n ∘ π (n + 1)`, and assume that `R` is complete and
separated for the tower: every compatible family `(xₙ)` comes from a unique `x ∈ R`.

A family of matrix complexes `M n` over `A n` with fixed ranks whose matrices are compatible
under the transitions defines a tower `n ↦ Res (M n)` of complexes of `R`-modules
(`MatrixComplex.towerFunctor`). A matrix complex `M` over `R` reducing to the `M n` gives a cone
over this tower (`MatrixComplex.towerCone`), which is a limit cone
(`MatrixComplex.isLimitTowerCone`). Its image in the derived category is therefore a homotopy
limit cone (`MatrixComplex.isHomotopyLimit_towerCone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

/-- If `g ∘ f` has kernel `(a)` and `f` is surjective, then `g` has kernel `(f a)`. -/
lemma RingHom.ker_eq_span_singleton_of_comp {R A' A : Type*} [CommRing R] [CommRing A']
    [CommRing A] {f : R →+* A'} (hf : Function.Surjective f) (g : A' →+* A) {a : R}
    (h : RingHom.ker (g.comp f) = Ideal.span {a}) : RingHom.ker g = Ideal.span {f a} := by
  rw [← Ideal.map_comap_of_surjective f hf (RingHom.ker g), RingHom.comap_ker, h, Ideal.map_span,
    Set.image_singleton]

namespace MatrixComplex

variable {R : Type u} [CommRing R] {A : ℕ → Type u} [∀ n, CommRing (A n)]
  {π : ∀ n, R →+* A n} {ρ : ∀ n, A (n + 1) →+* A n}

section Elements

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)

/-- The element of `R` defined by a compatible family of elements of the `A n`, when `R` is
complete for the tower. -/
noncomputable def limElem (x : ∀ n, A n) (hx : ∀ n, ρ n (x (n + 1)) = x n) : R :=
  (hcomplete x hx).choose

/-- The defining property of `MatrixComplex.limElem`. -/
lemma π_limElem (x : ∀ n, A n) (hx : ∀ n, ρ n (x (n + 1)) = x n) (n : ℕ) :
    π n (limElem hcomplete x hx) = x n :=
  (hcomplete x hx).choose_spec n

omit [∀ n, CommRing (A n)] in
/-- Elements of a ring which is separated for a tower of quotients are determined by their
images in the quotients. -/
lemma eq_of_forall_π {A : ℕ → Type u} [∀ n, CommRing (A n)] {π : ∀ n, R →+* A n}
    (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0) {a b : R} (h : ∀ n, π n a = π n b) : a = b :=
  sub_eq_zero.1 (hsep _ fun n ↦ by rw [map_sub, h, sub_self])

end Elements

variable (hρ : ∀ n, π n = (ρ n).comp (π (n + 1))) {r : ℤ → ℕ} (M : ∀ n, MatrixComplex r (A n))
  (hM : ∀ n i, ((M (n + 1)).d i).map (ρ n) = (M n).d i)

section Lim

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)

/-- The entrywise limit of compatible matrices. -/
noncomputable def limMatrix {k l : ℕ} (a : ∀ n, Matrix (Fin k) (Fin l) (A n))
    (ha : ∀ n, (a (n + 1)).map (ρ n) = a n) : Matrix (Fin k) (Fin l) R :=
  Matrix.of fun j m ↦ limElem hcomplete (fun n ↦ a n j m) fun n ↦ congrFun (congrFun (ha n) j) m

/-- The reductions of `MatrixComplex.limMatrix` are the given matrices. -/
lemma map_limMatrix {k l : ℕ} (a : ∀ n, Matrix (Fin k) (Fin l) (A n))
    (ha : ∀ n, (a (n + 1)).map (ρ n) = a n) (n : ℕ) :
    (limMatrix hcomplete a ha).map (π n) = a n :=
  Matrix.ext fun j m ↦ π_limElem hcomplete _ (fun n ↦ congrFun (congrFun (ha n) j) m) n

/-- The matrix complex over `R` whose matrices are the entrywise limits of the matrices of a
compatible family of matrix complexes over the `A n`. -/
noncomputable def towerLim : MatrixComplex r R where
  d i := limMatrix hcomplete (fun n ↦ (M n).d i) fun n ↦ hM n i
  d_mul_d i := Matrix.ext fun j k ↦ eq_of_forall_π hsep fun n ↦ by
    rw [RingHom.map_matrix_mul, map_limMatrix, map_limMatrix, (M n).d_mul_d]
    simp

/-- The matrix complex `MatrixComplex.towerLim` reduces to the given matrix complexes. -/
lemma map_towerLim_d (n : ℕ) (i : ℤ) :
    ((towerLim M hM hcomplete hsep).d i).map (π n) = (M n).d i :=
  map_limMatrix hcomplete _ (fun n ↦ hM n i) n

variable {M} in
/-- The chain endomorphism of a matrix complex `L` over `R` reducing to the `M n` whose matrices
are the entrywise limits of those of compatible chain endomorphisms of the `M n`. -/
noncomputable def towerLimHom (L : MatrixComplex r R)
    (hL : ∀ n i, (L.d i).map (π n) = (M n).d i) (E : ∀ n, (M n).complex ⟶ (M n).complex)
    (hE : ∀ n i, (toMatrix (E (n + 1)) i).map (ρ n) = toMatrix (E n) i) :
    L.complex ⟶ L.complex :=
  homMk (fun i ↦ limMatrix hcomplete (fun n ↦ toMatrix (E n) i) fun n ↦ hE n i) fun i ↦
    Matrix.ext fun j k ↦ eq_of_forall_π hsep fun n ↦ by
      rw [RingHom.map_matrix_mul, RingHom.map_matrix_mul, map_limMatrix, map_limMatrix, hL,
        toMatrix_comm]

variable {M} in
/-- The chain map `MatrixComplex.towerLimHom` reduces to the given chain maps. -/
lemma map_toMatrix_towerLimHom (L : MatrixComplex r R)
    (hL : ∀ n i, (L.d i).map (π n) = (M n).d i) (E : ∀ n, (M n).complex ⟶ (M n).complex)
    (hE : ∀ n i, (toMatrix (E (n + 1)) i).map (ρ n) = toMatrix (E n) i) (n : ℕ) (i : ℤ) :
    (toMatrix (towerLimHom hcomplete hsep L hL E hE) i).map (π n) = toMatrix (E n) i := by
  rw [towerLimHom, toMatrix_homMk]
  exact map_limMatrix hcomplete _ (fun n ↦ hE n i) n

end Lim

/-- The tower `n ↦ Res (M n)` of complexes of `R`-modules attached to a compatible family of
matrix complexes `M n` over the `A n`; the transitions are the reductions. -/
noncomputable def towerFunctor : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ ((ModuleCat.restrictScalars.{u} (π n)).mapHomologicalComplex _).obj
      (M n).complex) fun n ↦
    ((ModuleCat.restrictScalars.{u} (π (n + 1))).mapHomologicalComplex _).map
      ((M (n + 1)).reduction (ρ n) (M n) (hM n)) ≫
      ModuleCat.restrictScalarsCompComplexMap (hρ n) _

/-- The transitions of `MatrixComplex.towerFunctor`. -/
lemma towerFunctor_map_succ (n : ℕ) :
    (towerFunctor hρ M hM).map (homOfLE n.le_succ).op =
      ((ModuleCat.restrictScalars.{u} (π (n + 1))).mapHomologicalComplex _).map
        ((M (n + 1)).reduction (ρ n) (M n) (hM n)) ≫
        ModuleCat.restrictScalarsCompComplexMap (hρ n) _ :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The transitions of `MatrixComplex.towerFunctor` are the reductions of the coordinates. -/
lemma towerFunctor_map_succ_f_apply (n : ℕ) (i : ℤ) (v : Fin (r i) → A (n + 1)) :
    (((towerFunctor hρ M hM).map (homOfLE n.le_succ).op).f i).hom v = fun j ↦ ρ n (v j) := by
  rw [towerFunctor_map_succ]
  rfl

variable {M} (M' : MatrixComplex r R) (hM' : ∀ n i, (M'.d i).map (π n) = (M n).d i)

/-- The reductions of a matrix complex over `R` along the `π n` are compatible with the
transitions of `MatrixComplex.towerFunctor`. -/
lemma reduction_comp_towerFunctor_map (n : ℕ) :
    M'.reduction (π (n + 1)) (M (n + 1)) (hM' (n + 1)) ≫
        (towerFunctor hρ M hM).map (homOfLE n.le_succ).op =
      M'.reduction (π n) (M n) (hM' n) := by
  rw [towerFunctor_map_succ]
  ext i v
  funext j
  exact (RingHom.congr_fun (hρ n) (v j)).symm

/-- The cone over `MatrixComplex.towerFunctor` given by a matrix complex over `R` reducing to
the `M n`; its legs are the reductions. -/
noncomputable def towerCone : Cone (towerFunctor hρ M hM) where
  pt := M'.complex
  π := NatTrans.ofOpSequence (fun n ↦ M'.reduction (π n) (M n) (hM' n)) fun n ↦ by
    exact (Category.id_comp _).trans (reduction_comp_towerFunctor_map hρ hM M' hM' n).symm

/-- The legs of `MatrixComplex.towerCone` are the reductions. -/
lemma towerCone_π_app (n : ℕ) :
    (towerCone hρ hM M' hM').π.app (op n) = M'.reduction (π n) (M n) (hM' n) :=
  rfl

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)

section Limit

variable {i : ℤ} (s : Cone (towerFunctor hρ M hM ⋙ HomologicalComplex.eval _ _ i))

/-- The components of an element under the legs of a cone over a degree of the tower. -/
noncomputable def coneVec (n : ℕ) (x : s.pt) : Fin (r i) → A n := (s.π.app (op n)).hom x

/-- The components of an element under the legs of a cone are compatible. -/
lemma coneVec_compat (x : s.pt) (j : Fin (r i)) (n : ℕ) :
    ρ n (coneVec hρ hM s (n + 1) x j) = coneVec hρ hM s n x j := by
  refine (congrFun (towerFunctor_map_succ_f_apply hρ M hM n i
    (coneVec hρ hM s (n + 1) x)) j).symm.trans ?_
  exact congrFun (ConcreteCategory.congr_hom (s.w (homOfLE n.le_succ).op) x) j

/-- The lift of a cone over a degree of the tower, defined by taking limits of the
components. -/
noncomputable def coneLift : s.pt →ₗ[R] (Fin (r i) → R) where
  toFun x j := limElem hcomplete (fun n ↦ coneVec hρ hM s n x j) (coneVec_compat hρ hM s x j)
  map_add' x y := funext fun j ↦ eq_of_forall_π hsep fun n ↦ by
    rw [Pi.add_apply, map_add, π_limElem, π_limElem, π_limElem, coneVec, map_add]
    rfl
  map_smul' c x := funext fun j ↦ eq_of_forall_π hsep fun n ↦ by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, π_limElem, π_limElem, coneVec, map_smul]
    rfl

/-- The defining property of `MatrixComplex.coneLift`. -/
lemma π_coneLift (x : s.pt) (j : Fin (r i)) (n : ℕ) :
    π n (coneLift hρ hM hcomplete hsep s x j) = coneVec hρ hM s n x j :=
  π_limElem hcomplete _ (coneVec_compat hρ hM s x j) n

end Limit

/-- The cone `MatrixComplex.towerCone` is a limit cone when `R` is complete and separated for
the tower: in each degree, `Rʳ` is the limit of the `A nʳ`. -/
noncomputable def isLimitTowerCone : IsLimit (towerCone hρ hM M' hM') :=
  HomologicalComplex.isLimitOfEval _ _ fun i ↦
    { lift s := ModuleCat.ofHom (Y := M'.complex.X i) (coneLift hρ hM hcomplete hsep s)
      fac s := by
        rintro ⟨n⟩
        ext x
        funext j
        exact π_coneLift hρ hM hcomplete hsep s x j n
      uniq s m hm := by
        ext x
        funext j
        refine eq_of_forall_π hsep fun n ↦ (?_ : _ = coneVec hρ hM s n x j).trans
          (π_coneLift hρ hM hcomplete hsep s x j n).symm
        exact congrFun (ConcreteCategory.congr_hom (hm (op n)) x) j }

include hcomplete hsep in
/-- The image in the derived category of `MatrixComplex.towerCone` is a homotopy limit cone,
when `R` is complete and separated for the tower and the transitions are surjective. -/
theorem isHomotopyLimit_towerCone [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (hρs : ∀ n, Function.Surjective (ρ n)) :
    IsHomotopyLimit (DerivedCategory.Q.mapCone (towerCone hρ hM M' hM')) :=
  DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi (fun n i ↦ by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    refine ⟨fun j ↦ (hρs n (y j)).choose, ?_⟩
    rw [towerFunctor_map_succ_f_apply]
    exact funext fun j ↦ (hρs n (y j)).choose_spec)
    (isLimitTowerCone hρ hM M' hM' hcomplete hsep)

end MatrixComplex
