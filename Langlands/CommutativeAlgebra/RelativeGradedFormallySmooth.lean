import Langlands.CommutativeAlgebra.GradedFormallySmooth
import Mathlib.RingTheory.RingHom.Smooth

/-! # Relative square-zero lifting for graded algebras -/

noncomputable section

open Polynomial

namespace Langlands.CommutativeAlgebra.RelativeGradedFormallySmooth

open GradedFormallySmooth

variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra A B]

/-- Diagonal averaging preserves a graded base map. -/
theorem diag_preserves_base
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (hεA : ∀ a, ((cA a).coeff.sum fun _ d => d) = a)
    (hδA : ∀ a n, cA ((cA a).coeff n) =
      AddMonoidAlgebra.single n ((cA a).coeff n))
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a))
    (a : A →+* D) (L : B →+* LaurentPolynomial D)
    (hL : ∀ d, L (algebraMap A B d) =
      AddMonoidAlgebra.mapRingHom ℤ a (cA d)) (d : A) :
    diag L (cB (algebraMap A B d)) = a d := by
  classical
  rw [heq]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (cA d)]
  rw [map_finsuppSum, map_finsuppSum]
  simp only [AddMonoidAlgebra.mapRingHom_single, diag_single, hL]
  conv_rhs => rw [← hεA d, map_finsuppSum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [hδA, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same]

/-- A square-zero lift through the attracting coordinate quotient, retaining
the specified map from the graded base algebra. -/
theorem exists_lift_negIdeal [Algebra.FormallySmooth A B]
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (hεA : ∀ a, ((cA a).coeff.sum fun _ d => d) = a)
    (hδA : ∀ a n, cA ((cA a).coeff n) =
      AddMonoidAlgebra.single n ((cA a).coeff n))
    (hεB : ∀ b, ((cB b).coeff.sum fun _ d => d) = b)
    (hδB : ∀ b n, cB ((cB b).coeff n) =
      AddMonoidAlgebra.single n ((cB b).coeff n))
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a))
    (a : A →+* D) (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (x : B →+* D ⧸ J)
    (hx : ∀ d, x (algebraMap A B d) = Ideal.Quotient.mk J (a d))
    (ha : ∀ d ∈ negIdeal cA, a d = 0)
    (hxneg : ∀ d ∈ negIdeal cB, x d = 0) :
    ∃ z : B →+* D,
      (∀ d, z (algebraMap A B d) = a d) ∧
      (∀ b, Ideal.Quotient.mk J (z b) = x b) ∧
      (∀ d ∈ negIdeal cB, z d = 0) := by
  have hJ' := mul_eq_zero_of_sq_eq_bot hJ
  let gA : A →+* LaurentPolynomial D :=
    (AddMonoidAlgebra.mapRingHom ℤ a).comp cA
  have hgA : ∀ d, ∀ n < 0, (gA d).coeff n = 0 := by
    intro d n hn
    rw [RingHom.comp_apply, AddMonoidAlgebra.coeff_mapRingHom]
    exact ha _ (Ideal.subset_span ⟨d, n, hn, rfl⟩)
  let α : A →+* D[X] := polynomialLift gA hgA
  let : Algebra A D[X] := α.toAlgebra
  let πring : D[X] →+* (D ⧸ J)[X] := Polynomial.mapRingHom (Ideal.Quotient.mk J)
  let : Algebra A (D ⧸ J)[X] := (πring.comp α).toAlgebra
  let π : D[X] →ₐ[A] (D ⧸ J)[X] :=
    { πring with commutes' := fun _ => rfl }
  let gB : B →+* LaurentPolynomial (D ⧸ J) :=
    (AddMonoidAlgebra.mapRingHom ℤ x).comp cB
  have hgB : ∀ b, ∀ n < 0, (gB b).coeff n = 0 := by
    intro b n hn
    rw [RingHom.comp_apply, AddMonoidAlgebra.coeff_mapRingHom]
    exact hxneg _ (Ideal.subset_span ⟨b, n, hn, rfl⟩)
  let θ : B →ₐ[A] (D ⧸ J)[X] :=
    { polynomialLift gB hgB with
      commutes' := fun d => by
        apply toLaurent_injective
        change toLaurent (polynomialLift gB hgB (algebraMap A B d)) =
          toLaurent ((polynomialLift gA hgA d).map (Ideal.Quotient.mk J))
        rw [toLaurent_polynomialLift, ← mapRingHom_toLaurent,
          toLaurent_polynomialLift]
        change AddMonoidAlgebra.mapRingHom ℤ x (cB (algebraMap A B d)) =
          AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk J)
            (AddMonoidAlgebra.mapRingHom ℤ a (cA d))
        rw [heq]
        ext n
        simp only [AddMonoidAlgebra.coeff_mapRingHom]
        exact hx _ }
  have hθ : ∀ b, toLaurent (θ b) = gB b := toLaurent_polynomialLift gB hgB
  have hsurj : Function.Surjective π :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (RingHom.ker (π : D[X] →+* (D ⧸ J)[X])) := by
    refine ⟨2, ?_⟩
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk J)) ^ 2 = 0
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, ← Ideal.map_pow, hJ, Ideal.map_bot]
    rfl
  let Θ : B →ₐ[A] D[X] := Algebra.FormallySmooth.liftOfSurjective θ π hsurj hnil
  have hΘ : ∀ b, (Θ b).map (Ideal.Quotient.mk J) = θ b := fun b =>
    Algebra.FormallySmooth.liftOfSurjective_apply θ π hsurj hnil b
  let L : B →+* LaurentPolynomial D := toLaurent.comp (Θ : B →+* D[X])
  have hbase : ∀ d, L (algebraMap A B d) =
      AddMonoidAlgebra.mapRingHom ℤ a (cA d) := by
    intro d
    change toLaurent (Θ (algebraMap A B d)) = _
    rw [AlgHom.commutes]
    exact toLaurent_polynomialLift gA hgA d
  have hmk : ∀ b k, Ideal.Quotient.mk J ((L b).coeff k) = x ((cB b).coeff k) := by
    intro b k
    have hg : (gB b).coeff k = x ((cB b).coeff k) :=
      AddMonoidAlgebra.coeff_mapRingHom _ _ _
    rw [← hg, ← hθ, ← hΘ, ← mapRingHom_toLaurent,
      AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hL : ∀ b, IsDiagonalMod L J (cB b) := fun b i k hk => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hmk, hδB,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hk, map_zero]
  let z : B →+* D := diagRingHom cB L hJ' hL
  refine ⟨z, ?_, ?_, ?_⟩
  · exact diag_preserves_base cA cB hεA hδA heq a L hbase
  · intro b
    change Ideal.Quotient.mk J (diag L (cB b)) = x b
    rw [diag_apply, map_finsuppSum]
    conv_rhs => rw [← hεB b, map_finsuppSum]
    refine Finsupp.sum_congr fun n _ => ?_
    rw [hmk, hδB, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro d hd
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨b, n, hn, rfl⟩
      change diag L (cB ((cB b).coeff n)) = 0
      rw [hδB, diag_single]
      exact Langlands.GroupScheme.AffineLine.coeff_toLaurent_of_neg _ hn
    · exact map_zero z
    · intro b b' _ _ hb hb'
      rw [map_add, hb, hb', add_zero]
    · intro b b' _ hb'
      rw [smul_eq_mul, map_mul, hb', mul_zero]

/-- A square-zero lift through the fixed coordinate quotient, retaining the
specified map from the graded base algebra. -/
theorem exists_lift_offIdeal [Algebra.FormallySmooth A B]
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (hδB : ∀ b n, cB ((cB b).coeff n) =
      AddMonoidAlgebra.single n ((cB b).coeff n))
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a))
    (a : A →+* D) (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (x : B →+* D ⧸ J)
    (hx : ∀ d, x (algebraMap A B d) = Ideal.Quotient.mk J (a d))
    (ha : ∀ d ∈ offIdeal cA, a d = 0)
    (hxoff : ∀ d ∈ offIdeal cB, x d = 0) :
    ∃ z : B →+* D,
      (∀ d, z (algebraMap A B d) = a d) ∧
      (∀ b, Ideal.Quotient.mk J (z b) = x b) ∧
      (∀ d ∈ offIdeal cB, z d = 0) := by
  let : Algebra A D := a.toAlgebra
  let y : B →ₐ[A] D ⧸ J :=
    { x with commutes' := hx }
  have hJ' := mul_eq_zero_of_sq_eq_bot hJ
  have hyn : ∀ b n, n ≠ 0 → x ((cB b).coeff n) = 0 := by
    intro b n hn
    have h := hxoff _ (Ideal.subset_span ⟨b, n, rfl⟩)
    rwa [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      ite_eq_right hn, sub_zero] at h
  have hy0 : ∀ b, x ((cB b).coeff 0) = x b := by
    intro b
    have h := hxoff _ (Ideal.subset_span ⟨b, 0, rfl⟩)
    rwa [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      ite_eq_left rfl, map_sub, sub_eq_zero] at h
  have ha0 : ∀ d, a ((cA d).coeff 0) = a d := by
    intro d
    have h := ha _ (Ideal.subset_span ⟨d, 0, rfl⟩)
    rwa [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      ite_eq_left rfl, map_sub, sub_eq_zero] at h
  let Y : B →ₐ[A] D := Algebra.FormallySmooth.lift J ⟨2, hJ⟩ y
  have hY : ∀ b, Ideal.Quotient.mk J (Y b) = x b :=
    Algebra.FormallySmooth.mk_lift J ⟨2, hJ⟩ y
  let L : B →+* LaurentPolynomial D := LaurentPolynomial.C.comp (Y : B →+* D)
  have hL : ∀ b, IsDiagonalMod L J (cB b) := fun b i k hk => by
    change (LaurentPolynomial.C (Y ((cB b).coeff i))).coeff k ∈ J
    rw [LaurentPolynomial.C_apply]
    split_ifs with hk0
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hY]
      exact hyn b i (fun hi => hk (hk0.trans hi.symm))
    · exact J.zero_mem
  let z : B →+* D := diagRingHom cB L hJ' hL
  have hdiag : ∀ b, z b = Y ((cB b).coeff 0) := fun b =>
    diag_C_comp (Y : B →+* D) (cB b)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro d
    rw [hdiag, heq, AddMonoidAlgebra.coeff_mapRingHom, AlgHom.commutes]
    exact ha0 d
  · intro b
    rw [hdiag, hY, hy0]
  · intro d hd
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨b, n, rfl⟩
      rw [hdiag, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply]
      by_cases hn : n = 0
      · subst hn
        rw [ite_eq_left rfl, map_sub, hδB, AddMonoidAlgebra.coeff_sub,
          Finsupp.sub_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
          sub_self, map_zero]
      · rw [ite_eq_right hn, sub_zero, hδB, AddMonoidAlgebra.coeff_single,
          Finsupp.single_eq_of_ne (Ne.symm hn), map_zero]
    · exact map_zero z
    · intro b b' _ _ hb hb'
      rw [map_add, hb, hb', add_zero]
    · intro b b' _ hb'
      rw [smul_eq_mul, map_mul, hb', mul_zero]

/-- An equivariant algebra map takes the negative ideal to the negative ideal. -/
theorem map_mem_negIdeal
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a))
    {d : A} (hd : d ∈ negIdeal cA) :
    algebraMap A B d ∈ negIdeal cB := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨a, n, hn, rfl⟩
    have h : algebraMap A B ((cA a).coeff n) =
        (cB (algebraMap A B a)).coeff n := by
      rw [heq, AddMonoidAlgebra.coeff_mapRingHom]
    rw [h]
    exact Ideal.subset_span ⟨algebraMap A B a, n, hn, rfl⟩
  · rw [map_zero]
    exact Ideal.zero_mem _
  · intro a a' _ _ ha ha'
    rw [map_add]
    exact Ideal.add_mem _ ha ha'
  · intro a a' _ ha'
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _ ha'

/-- The actual map of attracting coordinate quotients. -/
def negQuotientMap
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) :
    A ⧸ negIdeal cA →+* B ⧸ negIdeal cB :=
  Ideal.Quotient.lift (negIdeal cA)
    ((Ideal.Quotient.mk (negIdeal cB)).comp (algebraMap A B))
    (fun _ hd => Ideal.Quotient.eq_zero_iff_mem.2 (map_mem_negIdeal cA cB heq hd))

theorem negQuotientMap_mk
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) (d : A) :
    negQuotientMap cA cB heq (Ideal.Quotient.mk (negIdeal cA) d) =
      Ideal.Quotient.mk (negIdeal cB) (algebraMap A B d) := rfl

/-- Relative formal smoothness passes to the attracting coordinate quotients. -/
theorem formallySmooth_negQuotientMap [Algebra.FormallySmooth A B]
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (hεA : ∀ a, ((cA a).coeff.sum fun _ d => d) = a)
    (hδA : ∀ a n, cA ((cA a).coeff n) =
      AddMonoidAlgebra.single n ((cA a).coeff n))
    (hεB : ∀ b, ((cB b).coeff.sum fun _ d => d) = b)
    (hδB : ∀ b n, cB ((cB b).coeff n) =
      AddMonoidAlgebra.single n ((cB b).coeff n))
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) :
    (negQuotientMap cA cB heq).FormallySmooth := by
  let : Algebra (A ⧸ negIdeal cA) (B ⧸ negIdeal cB) :=
    (negQuotientMap cA cB heq).toAlgebra
  apply Algebra.FormallySmooth.of_comp_surjective
  intro D _ _ J hJ x
  let a : A →+* D := (algebraMap (A ⧸ negIdeal cA) D).comp
    (Ideal.Quotient.mk (negIdeal cA))
  let y : B →+* D ⧸ J := (x : B ⧸ negIdeal cB →+* D ⧸ J).comp
    (Ideal.Quotient.mk (negIdeal cB))
  have hy : ∀ d, y (algebraMap A B d) = Ideal.Quotient.mk J (a d) := by
    intro d
    exact x.commutes (Ideal.Quotient.mk (negIdeal cA) d)
  have ha : ∀ d ∈ negIdeal cA, a d = 0 := by
    intro d hd
    change algebraMap (A ⧸ negIdeal cA) D (Ideal.Quotient.mk (negIdeal cA) d) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hd, map_zero]
  have hyneg : ∀ d ∈ negIdeal cB, y d = 0 := by
    intro d hd
    change x (Ideal.Quotient.mk (negIdeal cB) d) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hd, map_zero]
  obtain ⟨z, hzbase, hzx, hzneg⟩ :=
    exists_lift_negIdeal cA cB hεA hδA hεB hδB heq a J hJ y hy ha hyneg
  let zq : B ⧸ negIdeal cB →+* D := Ideal.Quotient.lift (negIdeal cB) z hzneg
  let zₐ : B ⧸ negIdeal cB →ₐ[A ⧸ negIdeal cA] D :=
    { zq with
      commutes' := fun d => by
        exact Quotient.inductionOn' d hzbase }
  refine ⟨zₐ, ?_⟩
  apply AlgHom.ext
  intro b
  exact Quotient.inductionOn' b hzx

/-- An equivariant algebra map takes the fixed ideal to the fixed ideal. -/
theorem map_mem_offIdeal
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a))
    {d : A} (hd : d ∈ offIdeal cA) :
    algebraMap A B d ∈ offIdeal cB := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨a, n, rfl⟩
    have he : AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B)
        (cA a - LaurentPolynomial.C a) =
        cB (algebraMap A B a) - LaurentPolynomial.C (algebraMap A B a) := by
      rw [map_sub, heq, ← LaurentPolynomial.single_eq_C,
        AddMonoidAlgebra.mapRingHom_single, LaurentPolynomial.single_eq_C]
    have h := congrArg (fun q : LaurentPolynomial B => q.coeff n) he
    rw [AddMonoidAlgebra.coeff_mapRingHom] at h
    rw [h]
    exact Ideal.subset_span ⟨algebraMap A B a, n, rfl⟩
  · rw [map_zero]
    exact Ideal.zero_mem _
  · intro a a' _ _ ha ha'
    rw [map_add]
    exact Ideal.add_mem _ ha ha'
  · intro a a' _ ha'
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _ ha'

/-- The actual map of fixed coordinate quotients. -/
def offQuotientMap
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) :
    A ⧸ offIdeal cA →+* B ⧸ offIdeal cB :=
  Ideal.Quotient.lift (offIdeal cA)
    ((Ideal.Quotient.mk (offIdeal cB)).comp (algebraMap A B))
    (fun _ hd => Ideal.Quotient.eq_zero_iff_mem.2 (map_mem_offIdeal cA cB heq hd))

theorem offQuotientMap_mk
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) (d : A) :
    offQuotientMap cA cB heq (Ideal.Quotient.mk (offIdeal cA) d) =
      Ideal.Quotient.mk (offIdeal cB) (algebraMap A B d) := rfl

/-- Relative formal smoothness passes to the fixed coordinate quotients. -/
theorem formallySmooth_offQuotientMap [Algebra.FormallySmooth A B]
    (cA : A →+* LaurentPolynomial A) (cB : B →+* LaurentPolynomial B)
    (hδB : ∀ b n, cB ((cB b).coeff n) =
      AddMonoidAlgebra.single n ((cB b).coeff n))
    (heq : ∀ a, cB (algebraMap A B a) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap A B) (cA a)) :
    (offQuotientMap cA cB heq).FormallySmooth := by
  let : Algebra (A ⧸ offIdeal cA) (B ⧸ offIdeal cB) :=
    (offQuotientMap cA cB heq).toAlgebra
  apply Algebra.FormallySmooth.of_comp_surjective
  intro D _ _ J hJ x
  let a : A →+* D := (algebraMap (A ⧸ offIdeal cA) D).comp
    (Ideal.Quotient.mk (offIdeal cA))
  let y : B →+* D ⧸ J := (x : B ⧸ offIdeal cB →+* D ⧸ J).comp
    (Ideal.Quotient.mk (offIdeal cB))
  have hy : ∀ d, y (algebraMap A B d) = Ideal.Quotient.mk J (a d) := by
    intro d
    exact x.commutes (Ideal.Quotient.mk (offIdeal cA) d)
  have ha : ∀ d ∈ offIdeal cA, a d = 0 := by
    intro d hd
    change algebraMap (A ⧸ offIdeal cA) D (Ideal.Quotient.mk (offIdeal cA) d) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hd, map_zero]
  have hyoff : ∀ d ∈ offIdeal cB, y d = 0 := by
    intro d hd
    change x (Ideal.Quotient.mk (offIdeal cB) d) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hd, map_zero]
  obtain ⟨z, hzbase, hzx, hzoff⟩ :=
    exists_lift_offIdeal cA cB hδB heq a J hJ y hy ha hyoff
  let zq : B ⧸ offIdeal cB →+* D := Ideal.Quotient.lift (offIdeal cB) z hzoff
  let zₐ : B ⧸ offIdeal cB →ₐ[A ⧸ offIdeal cA] D :=
    { zq with
      commutes' := fun d => by
        exact Quotient.inductionOn' d hzbase }
  refine ⟨zₐ, ?_⟩
  apply AlgHom.ext
  intro b
  exact Quotient.inductionOn' b hzx

end Langlands.CommutativeAlgebra.RelativeGradedFormallySmooth
