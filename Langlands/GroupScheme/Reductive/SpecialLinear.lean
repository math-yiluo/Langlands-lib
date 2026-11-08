import Langlands.GroupScheme.SpecialLinearGeometry
import Langlands.GroupScheme.SpecialLinearBaseChange

/-! # Reductivity of the actual special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

section LinearAlgebra

variable {K : Type*} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- A nonzero subspace of `Kⁿ` stable under `SL_n(K)` is everything. -/
theorem eq_top_of_forall_SL_mulVec_mem (W : Submodule K (n → K))
    (hW : ∀ g : Matrix.SpecialLinearGroup n K, ∀ w ∈ W, (g : Matrix n n K) *ᵥ w ∈ W) (h0 : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have htv : ∀ q r : n, q ≠ r → ∀ x ∈ W, Pi.single q (x r) ∈ W := by
    intro q r hqr x hx
    have h := W.sub_mem (hW (Matrix.SpecialLinearGroup.transvection hqr 1) x hx) hx
    convert h using 1
    show _ = Matrix.transvection q r (1 : K) *ᵥ x - x
    rw [Matrix.transvection, Matrix.add_mulVec,
      Matrix.one_mulVec, add_sub_cancel_left]
    ext i
    rw [Matrix.mulVec, dotProduct]
    by_cases hi : i = q
    · subst hi
      simp [Matrix.single_apply]
    · have hqi : ¬q = i := fun h => hi h.symm
      simp [hi, hqi]
  have hne : ∀ q, q ≠ p → Pi.single q (1 : K) ∈ W := by
    intro q hq
    have h := W.smul_mem (v p)⁻¹ (htv q p hq v hvW)
    rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hp] at h
  have hall : ∀ q, Pi.single q (1 : K) ∈ W := by
    intro q
    by_cases hq : q = p
    · subst hq
      by_cases hr : ∃ r, r ≠ q
      · obtain ⟨r, hr⟩ := hr
        have h := htv q r hr.symm _ (hne r hr)
        rwa [Pi.single_eq_same] at h
      · push Not at hr
        have hv : v = Pi.single q (v q) := by
          funext r
          rw [hr r, Pi.single_eq_same]
        have hvW' : Pi.single q (v q) ∈ W := by
          rw [← hv]
          exact hvW
        have h := W.smul_mem (v q)⁻¹ hvW'
        rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hp] at h
    · exact hne q hq
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end LinearAlgebra

namespace SpecialLinear

section Radical

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- The special-linear point obtained from a matrix over the base field. -/
def constantMatrixPoint (T : Over (Spec (CommRingCat.of K)))
    (g : Matrix.SpecialLinearGroup n K) :
    T ⟶ (groupScheme n (CommRingCat.of K)).X :=
  (pointsEquiv n _ T).symm (Matrix.SpecialLinearGroup.map (scalarMap T) g)

/-- Normality in the special linear group preserves the standard fixed subspace. -/
theorem mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ groupScheme n (CommRingCat.of K))
    (hN : (SubgroupFunctor.range i).IsNormal) (g : Matrix.SpecialLinearGroup n K)
    {v : n → K} (hv : v ∈ MatrixRepresentation.fixedSubmodule
      (i ≫ inclusion n (CommRingCat.of K))) :
    (g : Matrix n n K) *ᵥ v ∈ MatrixRepresentation.fixedSubmodule
      (i ≫ inclusion n (CommRingCat.of K)) := by
  intro T h
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
    (hN T (constantMatrixPoint T g)⁻¹ (h ≫ i.hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, hh'] at key
  simp only [map_mul, map_inv, inv_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion]
  have hg : (fun j => scalarMap T (((g : Matrix n n K) *ᵥ v) j)) =
      ((pointsEquiv n _ T (constantMatrixPoint T g) : Matrix.SpecialLinearGroup n Γ(T.left, ⊤)) :
        Matrix n n Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j)) := by
    funext j
    rw [RingHom.map_mulVec, constantMatrixPoint, MulEquiv.apply_symm_apply]
    rfl
  rw [hg]
  set G := Matrix.SpecialLinearGroup.toGL (pointsEquiv n _ T (constantMatrixPoint T g))
  set M := Matrix.SpecialLinearGroup.toGL (pointsEquiv n _ T (h ≫ i.hom.hom))
  have e1 : (M : Matrix n n Γ(T.left, ⊤)) *ᵥ ((G : Matrix n n Γ(T.left, ⊤)) *ᵥ
      (fun j => scalarMap T (v j))) = (G : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (((G⁻¹ * M * G : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun j => scalarMap T (v j))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  change (M : Matrix n n Γ(T.left, ⊤)) *ᵥ
    ((G : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))) =
      (G : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))
  rw [e1, key]

/-- Every unipotent normal closed subgroup of the actual special linear group is trivial. -/
theorem hasTrivialUnipotentRadical (K : Type u) [Field K]
    (n : Type) [Fintype n] [DecidableEq n] :
    HasTrivialUnipotentRadical (groupScheme n (CommRingCat.of K)) := by
  intro H i _ _ _ hU hN
  have hfix : ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X),
      pointsEquiv n _ T (h ≫ i.hom.hom) = 1 := by
    intro T h
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    rcases isEmpty_or_nonempty n with hn | hn
    · exact isEmptyElim a
    let ρ := i ≫ inclusion n (CommRingCat.of K)
    obtain ⟨v, hv0, hv⟩ := hU n ρ
    have htop := eq_top_of_forall_SL_mulVec_mem (MatrixRepresentation.fixedSubmodule ρ)
      (fun g w hw => mulVec_mem_fixedSubmodule i hN g hw)
      ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    have hb : Pi.single b (1 : K) ∈ MatrixRepresentation.fixedSubmodule ρ := by
      rw [htop]
      exact Submodule.mem_top
    have hb' := hb T h
    have hs : (fun j => scalarMap T ((Pi.single b (1 : K) : n → K) j)) = Pi.single b 1 := by
      funext j
      by_cases hj : j = b
      · subst hj
        simp
      · simp [hj]
    rw [hs, Matrix.mulVec_single_one, MatrixRepresentation.pointMatrix_apply] at hb'
    change _ = _ at hb'
    dsimp only [ρ] at hb'
    rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_inclusion] at hb'
    have := congrFun hb' a
    by_cases hab : a = b
    · subst hab
      simpa [Matrix.col] using this
    · simpa [Matrix.col, hab, Matrix.one_apply_ne hab] using this
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply (pointsEquiv n _ T).injective
    rw [hfix, map_one]
  · rintro rfl
    exact Subgroup.one_mem _

end Radical

section Geometry

variable (K : Type u) [Field K] (n : Type) [Fintype n] [DecidableEq n] (p : n)

include p in
/-- The actual special linear group over a field is pseudo-reductive. -/
theorem isPseudoReductive : IsPseudoReductive (groupScheme n (CommRingCat.of K)) where
  smooth := smooth_groupScheme n p _
  isAffineHom := isAffineHom_groupScheme (n := n) (R := CommRingCat.of K)
  connectedSpace := connectedSpace_groupScheme n p K
  hasTrivialUnipotentRadical := hasTrivialUnipotentRadical K n

include p in
/-- The actual special linear group over a field is connected reductive. -/
theorem isConnectedReductive : IsConnectedReductive (groupScheme n (CommRingCat.of K)) where
  smooth := smooth_groupScheme n p _
  isAffineHom := isAffineHom_groupScheme (n := n) (R := CommRingCat.of K)
  connectedSpace := connectedSpace_groupScheme n p K
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso (baseChangeModelIso n (toAlgebraicClosure K))
      (hasTrivialUnipotentRadical (AlgebraicClosure K) n)

include p in
/-- The actual special linear model over every commutative ring is reductive. -/
theorem isReductive (R : CommRingCat.{u}) : IsReductive (groupScheme n R) where
  smooth := smooth_groupScheme n p R
  isAffineHom := inferInstance
  geometricFiber s :=
    IsPseudoReductive.of_iso (baseChangeModelIso n (geometricPoint (Spec R) s))
      (isPseudoReductive _ n p)

end Geometry

end SpecialLinear

end Langlands.GroupScheme
