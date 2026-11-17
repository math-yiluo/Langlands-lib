import Langlands.Algebra.FiniteBialgebraHom
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Idempotents

/-! # Lifting Hopf points between group algebras along nilpotent thickenings -/

noncomputable section

universe u v w

open TensorProduct

namespace Langlands.FiniteBialgebraHom

section Grouplike

variable (R : Type u) [CommRing R] {P : Type u} [CommRing P] [Bialgebra R P]
  {C : Type v} [CommRing C] [Algebra R C]

/-- An element `g` of `C ⊗[R] P` is a grouplike point if `(id ⊗ Δ) g = g₁ g₂`, where `g₁` and
`g₂` are the images of `g` under the two factor inclusions `C ⊗ P → C ⊗ (P ⊗ P)`, and
`(id ⊗ ε) g = 1`. -/
def IsGrouplikePoint (g : C ⊗[R] P) : Prop :=
  Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.comulAlgHom R P) g =
      inclFirst R g * inclSecond R g ∧
    Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.counitAlgHom R P) g) = 1

variable {R}

theorem isGrouplikePoint_one : IsGrouplikePoint R (1 : C ⊗[R] P) := by
  refine ⟨?_, ?_⟩ <;> simp

theorem IsGrouplikePoint.mul {g h : C ⊗[R] P} (hg : IsGrouplikePoint R g)
    (hh : IsGrouplikePoint R h) : IsGrouplikePoint R (g * h) := by
  refine ⟨?_, ?_⟩
  · rw [map_mul, hg.1, hh.1, map_mul, map_mul]
    ring
  · rw [map_mul, map_mul, hg.2, hh.2, mul_one]

variable (R) in
theorem isHopfPoint_iff_forall {Λ : Type u} [AddCommGroup Λ]
    (f : AddMonoidAlgebra R Λ →ₐ[R] C ⊗[R] P) :
    IsHopfPoint R f ↔ ∀ γ : Λ, IsGrouplikePoint R (f (AddMonoidAlgebra.single γ 1)) := by
  constructor
  · intro hf γ
    refine ⟨?_, ?_⟩
    · have := congrArg (fun φ => φ (AddMonoidAlgebra.single γ 1)) hf.1
      simpa [comulLeft, comulRight] using this
    · have := congrArg (fun φ => φ (AddMonoidAlgebra.single γ 1)) hf.2
      simpa [counitMap] using this
  · intro h
    refine ⟨?_, ?_⟩
    · apply AddMonoidAlgebra.algHom_ext
      · intro γ
        simpa [comulLeft, comulRight] using (h γ).1
      · exact Subsingleton.elim _ _
    · apply AddMonoidAlgebra.algHom_ext
      · intro γ
        simpa [counitMap] using (h γ).2
      · exact Subsingleton.elim _ _

end Grouplike

section GroupAlgebraTarget

variable {R : Type u} [CommRing R] {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]
  {C : Type v} [CommRing C] [Algebra R C]

/-- The standard `C`-basis of `C ⊗[R] R[A]`. -/
abbrev stdBasis : Module.Basis A C (C ⊗[R] AddMonoidAlgebra R A) :=
  Algebra.TensorProduct.basis C (AddMonoidAlgebra.basis A R)

/-- The standard `C`-basis of `C ⊗[R] (R[A] ⊗[R] R[A])`, indexed by `A × A`. -/
abbrev stdBasis₂ : Module.Basis (A × A) C (C ⊗[R] (AddMonoidAlgebra R A ⊗[R] AddMonoidAlgebra R A)) :=
  Algebra.TensorProduct.basis C ((AddMonoidAlgebra.basis A R).tensorProduct
    (AddMonoidAlgebra.basis A R))

/-- The coordinates of an element of `C ⊗[R] R[A]` in the standard basis. -/
abbrev coord (g : C ⊗[R] AddMonoidAlgebra R A) (a : A) : C := (stdBasis (R := R)).repr g a

omit [AddCommGroup A] [DecidableEq A] in
theorem sum_coord_tmul (g : C ⊗[R] AddMonoidAlgebra R A) :
    ∑ a, coord g a ⊗ₜ[R] AddMonoidAlgebra.single a (1 : R) = g := by
  conv_rhs => rw [← (stdBasis (R := R) (C := C)).sum_repr g]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.TensorProduct.basis_repr_symm_apply', AddMonoidAlgebra.basis_apply]

omit [AddCommGroup A] [Fintype A] in
theorem stdBasis₂_repr_tmul (c : C) (a b : A) (x y : A) :
    (stdBasis₂ (R := R)).repr (c ⊗ₜ[R] (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R]
      AddMonoidAlgebra.single b (1 : R))) (x, y) = if a = x then if b = y then c else 0 else 0 := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  by_cases ha : a = x <;> by_cases hb : b = y <;>
    simp [Module.Basis.tensorProduct_repr_tmul_apply, ← AddMonoidAlgebra.basis_apply,
      ha, hb]

omit [DecidableEq A] in
theorem comul_map_eq (g : C ⊗[R] AddMonoidAlgebra R A) :
    Algebra.TensorProduct.map (AlgHom.id R C) (Bialgebra.comulAlgHom R (AddMonoidAlgebra R A)) g =
      ∑ a, coord g a ⊗ₜ[R] (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R]
        AddMonoidAlgebra.single a (1 : R)) := by
  conv_lhs => rw [← sum_coord_tmul g]
  simp [map_sum]

omit [DecidableEq A] in
theorem inclFirst_mul_inclSecond (g : C ⊗[R] AddMonoidAlgebra R A) :
    inclFirst R g * inclSecond R g =
      ∑ a, ∑ b, (coord g a * coord g b) ⊗ₜ[R] (AddMonoidAlgebra.single a (1 : R) ⊗ₜ[R]
        AddMonoidAlgebra.single b (1 : R)) := by
  conv_lhs => rw [← sum_coord_tmul g]
  simp [map_sum, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul]

omit [DecidableEq A] in
theorem counit_map_eq (g : C ⊗[R] AddMonoidAlgebra R A) :
    Algebra.TensorProduct.rid R R C (Algebra.TensorProduct.map (AlgHom.id R C)
      (Bialgebra.counitAlgHom R (AddMonoidAlgebra R A)) g) = ∑ a, coord g a := by
  conv_lhs => rw [← sum_coord_tmul g]
  simp [map_sum]

theorem repr_comul_map (g : C ⊗[R] AddMonoidAlgebra R A) (x y : A) :
    (stdBasis₂ (R := R)).repr (Algebra.TensorProduct.map (AlgHom.id R C)
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R A)) g) (x, y) =
      if x = y then coord g x else 0 := by
  rw [comul_map_eq, map_sum, Finsupp.finsetSum_apply]
  simp_rw [stdBasis₂_repr_tmul]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

theorem repr_inclFirst_mul_inclSecond (g : C ⊗[R] AddMonoidAlgebra R A) (x y : A) :
    (stdBasis₂ (R := R)).repr (inclFirst R g * inclSecond R g) (x, y) =
      coord g x * coord g y := by
  rw [inclFirst_mul_inclSecond, map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_sum, Finsupp.finsetSum_apply, stdBasis₂_repr_tmul]
  simp

theorem isGrouplikePoint_iff (g : C ⊗[R] AddMonoidAlgebra R A) :
    IsGrouplikePoint R g ↔ CompleteOrthogonalIdempotents (coord g) := by
  have key : Algebra.TensorProduct.map (AlgHom.id R C)
      (Bialgebra.comulAlgHom R (AddMonoidAlgebra R A)) g = inclFirst R g * inclSecond R g ↔
      ∀ x y, coord g x * coord g y = if x = y then coord g x else 0 := by
    constructor
    · intro h x y
      rw [← repr_inclFirst_mul_inclSecond, ← h, repr_comul_map]
    · intro h
      apply (stdBasis₂ (R := R)).repr.injective
      ext ⟨x, y⟩
      rw [repr_comul_map, repr_inclFirst_mul_inclSecond, h]
  rw [IsGrouplikePoint, key, counit_map_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨fun x => show _ * _ = _ by simpa using h₁ x x, fun x y hxy => by simpa [hxy] using h₁ x y⟩, h₂⟩
  · intro he
    refine ⟨fun x y => ?_, he.complete⟩
    by_cases hxy : x = y
    · subst hxy; simpa using (he.idem x).eq
    · simpa [hxy] using he.ortho hxy

omit [AddCommGroup A] [Fintype A] in
theorem coord_tmul (c : C) (a x : A) :
    coord (c ⊗ₜ[R] AddMonoidAlgebra.single a (1 : R)) x = if a = x then c else 0 := by
  rw [coord, Algebra.TensorProduct.basis_repr_tmul]
  by_cases h : a = x <;> simp [← AddMonoidAlgebra.basis_apply, h]

omit [AddCommGroup A] in
theorem coord_sum_tmul (e : A → C) :
    coord (∑ a, e a ⊗ₜ[R] AddMonoidAlgebra.single a (1 : R)) = e := by
  funext x
  show (stdBasis (R := R)).repr _ x = e x
  rw [map_sum, Finsupp.finsetSum_apply]
  refine (Finset.sum_congr rfl fun a _ => coord_tmul (e a) a x).trans ?_
  simp

end GroupAlgebraTarget

section Lift

variable {R : Type u} [CommRing R] {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]
  {C : Type v} [CommRing C] [Algebra R C] {D : Type w} [CommRing D] [Algebra R D]
  (π : C →ₐ[R] D)

omit [Fintype A] [DecidableEq A] in
theorem coord_map (g : C ⊗[R] AddMonoidAlgebra R A) (a : A) :
    coord (Algebra.TensorProduct.map π (AlgHom.id R _) g) a = π (coord g a) :=
  basis_repr_map R _ π g a

theorem IsGrouplikePoint.map {g : C ⊗[R] AddMonoidAlgebra R A} (hg : IsGrouplikePoint R g) :
    IsGrouplikePoint R (Algebra.TensorProduct.map π (AlgHom.id R _) g) := by
  rw [isGrouplikePoint_iff] at hg ⊢
  have : coord (Algebra.TensorProduct.map π (AlgHom.id R _) g) = (π : C →+* D) ∘ coord g :=
    funext (coord_map π g)
  rw [this]
  exact hg.map (π : C →+* D)

variable {π} (hnil : ∀ x ∈ RingHom.ker (π : C →+* D), IsNilpotent x)
include hnil

theorem IsGrouplikePoint.eq_of_map_eq {g₁ g₂ : C ⊗[R] AddMonoidAlgebra R A}
    (h₁ : IsGrouplikePoint R g₁) (h₂ : IsGrouplikePoint R g₂)
    (h : Algebra.TensorProduct.map π (AlgHom.id R _) g₁ =
      Algebra.TensorProduct.map π (AlgHom.id R _) g₂) : g₁ = g₂ := by
  rw [isGrouplikePoint_iff] at h₁ h₂
  apply (stdBasis (R := R) (C := C)).repr.injective
  ext a
  refine eq_of_isNilpotent_sub_of_isIdempotentElem (h₁.idem a) (h₂.idem a) (hnil _ ?_)
  have := congrArg (fun g => coord g a) h
  simp only [coord_map] at this
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  exact this

theorem IsGrouplikePoint.exists_map_eq (hπ : Function.Surjective π)
    {g' : D ⊗[R] AddMonoidAlgebra R A} (hg' : IsGrouplikePoint R g') :
    ∃ g : C ⊗[R] AddMonoidAlgebra R A, IsGrouplikePoint R g ∧
      Algebra.TensorProduct.map π (AlgHom.id R _) g = g' := by
  rw [isGrouplikePoint_iff] at hg'
  obtain ⟨e, he, hπe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (π : C →+* D) hnil hg' (fun a => RingHom.mem_range.2 (hπ _))
  refine ⟨∑ a, e a ⊗ₜ[R] AddMonoidAlgebra.single a (1 : R), ?_, ?_⟩
  · rw [isGrouplikePoint_iff, coord_sum_tmul]
    exact he
  · conv_rhs => rw [← sum_coord_tmul g']
    simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hπe]
    rfl

/-- **Lifting Hopf points along nilpotent thickenings.** If `π : C → D` is surjective with
nilpotent kernel, then pushing forward along `π` is a bijection from Hopf points
`R[Λ] → C ⊗[R] R[A]` to Hopf points `R[Λ] → D ⊗[R] R[A]`, for a finite abelian group `A`. -/
theorem bijective_pushPoint (hπ : Function.Surjective π) (Λ : Type u) [AddCommGroup Λ] :
    Function.Bijective (fun f : {f : AddMonoidAlgebra R Λ →ₐ[R] C ⊗[R] AddMonoidAlgebra R A //
        IsHopfPoint R f} =>
      (⟨pushPoint R π f.1, f.2.pushPoint R π⟩ :
        {f : AddMonoidAlgebra R Λ →ₐ[R] D ⊗[R] AddMonoidAlgebra R A // IsHopfPoint R f})) := by
  constructor
  · rintro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    rw [isHopfPoint_iff_forall] at hf₁ hf₂
    apply AddMonoidAlgebra.algHom_ext
    · intro γ
      exact (hf₁ γ).eq_of_map_eq hnil (hf₂ γ)
        (congrArg (fun φ => φ (AddMonoidAlgebra.single γ 1)) h)
    · exact Subsingleton.elim _ _
  · rintro ⟨f', hf'⟩
    rw [isHopfPoint_iff_forall] at hf'
    choose L hL hLπ using fun γ => (hf' γ).exists_map_eq hnil hπ
    let φ : Multiplicative Λ →* C ⊗[R] AddMonoidAlgebra R A :=
      { toFun := fun γ => L γ.toAdd
        map_one' := by
          show L 0 = 1
          refine (hL _).eq_of_map_eq hnil isGrouplikePoint_one ?_
          rw [hLπ, map_one, ← AddMonoidAlgebra.one_def, map_one]
        map_mul' := fun x y => by
          show L (x.toAdd + y.toAdd) = L x.toAdd * L y.toAdd
          refine (hL _).eq_of_map_eq hnil ((hL _).mul (hL _)) ?_
          rw [hLπ, map_mul, hLπ, hLπ, ← map_mul, AddMonoidAlgebra.single_mul_single,
            mul_one] }
    have hφ : ∀ γ : Λ, AddMonoidAlgebra.lift R (C ⊗[R] AddMonoidAlgebra R A) Λ φ
        (AddMonoidAlgebra.single γ 1) = L γ := fun γ => by
      rw [AddMonoidAlgebra.lift_single, one_smul]
      rfl
    refine ⟨⟨AddMonoidAlgebra.lift R _ Λ φ, (isHopfPoint_iff_forall R _).2 fun γ => ?_⟩, ?_⟩
    · rw [hφ]
      exact hL γ
    · simp only [Subtype.mk.injEq]
      apply AddMonoidAlgebra.algHom_ext
      · intro γ
        rw [AlgHom.comp_apply, hφ, hLπ]
      · exact Subsingleton.elim _ _

end Lift

end Langlands.FiniteBialgebraHom
