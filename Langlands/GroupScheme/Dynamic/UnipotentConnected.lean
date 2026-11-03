import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.CoactionGrading
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Connectedness of the unipotent dynamic subgroup of an affine group over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicConnected

section Idempotents

open Polynomial

variable {D : Type*} [CommRing D]

/-- Multiplication by `X` is injective on polynomials. -/
theorem X_mul_injective {p q : D[X]} (h : X * p = X * q) : p = q := by
  ext n
  have h' := congrArg (fun r : D[X] => r.coeff (n + 1)) h
  simpa only [coeff_X_mul] using h'

/-- A polynomial `q` with `q = X * q ^ 2` is zero: it is divisible by every power of `X`. -/
theorem eq_zero_of_eq_X_mul_sq {q : D[X]} (h : q = X * q ^ 2) : q = 0 := by
  have hdvd : ∀ n : ℕ, X ^ n ∣ q := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact one_dvd q
    | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q, ?_⟩
      calc q = X * q * q := by rw [mul_assoc, ← sq]; exact h
        _ = X * (X ^ n * r) * q := by rw [← hr]
        _ = X ^ (n + 1) * (r * q) := by ring
  ext n
  rw [coeff_zero]
  exact X_pow_dvd_iff.1 (hdvd (n + 1)) n (Nat.lt_succ_self n)

/-- An idempotent polynomial vanishing at `0` is zero. -/
theorem eq_zero_of_isIdempotentElem_of_eval_zero {p : D[X]} (hp : IsIdempotentElem p)
    (h0 : p.eval 0 = 0) : p = 0 := by
  obtain ⟨q, rfl⟩ : X ∣ p := X_dvd_iff.2 (by rwa [coeff_zero_eq_eval_zero])
  have hq : q = X * q ^ 2 := by
    apply X_mul_injective
    calc X * q = X * q * (X * q) := hp.eq.symm
      _ = X * (X * q ^ 2) := by ring
  rw [eq_zero_of_eq_X_mul_sq hq, mul_zero]

/-- **Contraction criterion.** Let `E : D →+* D[X]` be a ring map whose value at `X = 1` is the
identity and whose value at `X = 0` sends every idempotent to `0` or `1`. If `Spec D` is
nonempty, it is connected: every idempotent of `D` is `0` or `1`. -/
theorem connectedSpace_of_contraction [Nonempty (PrimeSpectrum D)] (E : D →+* D[X])
    (h1 : ∀ d, (E d).eval 1 = d)
    (h0 : ∀ d, IsIdempotentElem d → (E d).eval 0 = 0 ∨ (E d).eval 0 = 1) :
    ConnectedSpace (PrimeSpectrum D) := by
  have key : ∀ e : D, IsIdempotentElem e → (E e).eval 0 = 0 → e = 0 := by
    intro e he hz
    rw [← h1 e, eq_zero_of_isIdempotentElem_of_eval_zero (he.map E) hz, eval_zero]
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hs
  rcases h0 e he with h | h
  · left
    rw [key e he h, PrimeSpectrum.basicOpen_zero]
    rfl
  · right
    have h' : (E (1 - e)).eval 0 = 0 := by
      rw [map_sub, map_one, eval_sub, eval_one, h, sub_self]
    have he1 := key (1 - e) he.one_sub h'
    rw [sub_eq_zero] at he1
    rw [← he1, PrimeSpectrum.basicOpen_one]
    rfl

end Idempotents

section Topology

/-- Connectedness of the underlying space is invariant under isomorphisms of group schemes. -/
theorem connectedSpace_of_iso {S : Scheme.{u}} {H H' : GroupScheme S} (e : H ≅ H')
    [ConnectedSpace H'.X.left] : ConnectedSpace H.X.left :=
  (Scheme.homeoOfIso ((Grp.forget (Over S) ⋙ Over.forget S).mapIso e)).connectedSpace_iff.2
    ‹ConnectedSpace H'.X.left›

end Topology

section GradedContraction

open Polynomial LaurentPolynomial

variable {B D : Type u} [CommRing B] [CommRing D]

/-- A ring map into Laurent polynomials without terms of negative degree, as a ring map into
polynomials (pointwise truncation). -/
def truncHom (g : B →+* LaurentPolynomial D) (hg : ∀ b, ∀ n < 0, (g b).coeff n = 0) :
    B →+* D[X] where
  toFun b := trunc (g b)
  map_one' := toLaurent_injective (by rw [AffineLine.toLaurent_trunc (hg 1), map_one, map_one])
  map_mul' b b' := toLaurent_injective (by
    rw [AffineLine.toLaurent_trunc (hg _), map_mul, map_mul, AffineLine.toLaurent_trunc (hg b),
      AffineLine.toLaurent_trunc (hg b')])
  map_zero' := by rw [map_zero, map_zero]
  map_add' b b' := by rw [map_add, map_add]

theorem truncHom_apply (g : B →+* LaurentPolynomial D) (hg : ∀ b, ∀ n < 0, (g b).coeff n = 0)
    (b : B) : truncHom g hg b = trunc (g b) :=
  rfl

theorem coeff_mapRingHom (π : B →+* D) (q : LaurentPolynomial B) (n : ℤ) :
    (AddMonoidAlgebra.mapRingHom ℤ π q).coeff n = π (q.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

/-- Evaluation at `T = 1` commutes with a coefficient map. -/
theorem eval₂_one_mapRingHom (π : B →+* D) (q : LaurentPolynomial B) :
    eval₂ (RingHom.id D) 1 (AddMonoidAlgebra.mapRingHom ℤ π q) =
      π (eval₂ (RingHom.id B) 1 q) := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | C_mul_T n a =>
    rw [← single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single, single_eq_C_mul_T,
      single_eq_C_mul_T, eval₂_C_mul_T, eval₂_C_mul_T]
    simp

variable (K : Type u) [CommRing K] [Algebra K B] (c : B →+* LaurentPolynomial B) (ε : B →+* K)

/-- The ideal generated by the coefficients of negative degree of `c` and by the differences
between the constant coefficient of `c(b)` and `ε(b)`. -/
def contractionIdeal : Ideal B :=
  Ideal.span ({x | ∃ b, ∃ n < 0, (c b).coeff n = x} ∪
    {x | ∃ b, (c b).coeff 0 - algebraMap K B (ε b) = x})

variable {K c ε}

theorem coeff_mem_contractionIdeal (b : B) {n : ℤ} (hn : n < 0) :
    (c b).coeff n ∈ contractionIdeal K c ε :=
  Ideal.subset_span (Or.inl ⟨b, n, hn, rfl⟩)

theorem coeff_zero_sub_mem_contractionIdeal (b : B) :
    (c b).coeff 0 - algebraMap K B (ε b) ∈ contractionIdeal K c ε :=
  Ideal.subset_span (Or.inr ⟨b, rfl⟩)

/-- The polynomial `∑_{n ≥ 0} π(c(b)_n) X^n` over `B ⧸ I`. -/
def contractionAux : B →+* (B ⧸ contractionIdeal K c ε)[X] :=
  truncHom ((AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk _)).comp c) fun b n hn => by
    rw [RingHom.comp_apply, coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem]
    exact coeff_mem_contractionIdeal b hn

theorem contractionAux_eq_zero {x : B} (hx : ∀ m, (c x).coeff m ∈ contractionIdeal K c ε) :
    contractionAux (K := K) (c := c) (ε := ε) x = 0 := by
  have h : (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk (contractionIdeal K c ε))) (c x) =
      0 := by
    ext m
    rw [coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem.2 (hx m)]
    rfl
  rw [contractionAux, truncHom_apply, RingHom.comp_apply, h, map_zero]

theorem coeff_C_mul_T_mem {I : Ideal B} {x : B} (hx : x ∈ I) (n m : ℤ) :
    (LaurentPolynomial.C x * T n : LaurentPolynomial B).coeff m ∈ I := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · exact hx
  · exact I.zero_mem

variable (hH : ∀ b n, c ((c b).coeff n) = LaurentPolynomial.C ((c b).coeff n) * T n)
  (hA : ∀ r : K, c (algebraMap K B r) = LaurentPolynomial.C (algebraMap K B r))

include hH hA in
theorem contractionIdeal_le_ker : contractionIdeal K c ε ≤ RingHom.ker (contractionAux (K := K)
    (c := c) (ε := ε)) := by
  refine Ideal.span_le.2 ?_
  rintro x (⟨b, n, hn, rfl⟩ | ⟨b, rfl⟩)
  · refine RingHom.mem_ker.2 (contractionAux_eq_zero fun m => ?_)
    rw [hH]
    exact coeff_C_mul_T_mem (coeff_mem_contractionIdeal b hn) n m
  · refine RingHom.mem_ker.2 (contractionAux_eq_zero fun m => ?_)
    have hc : c ((c b).coeff 0 - algebraMap K B (ε b)) =
        LaurentPolynomial.C ((c b).coeff 0 - algebraMap K B (ε b)) * T 0 := by
      rw [map_sub, hH, hA, T_zero, mul_one, mul_one, map_sub]
    rw [hc]
    exact coeff_C_mul_T_mem (coeff_zero_sub_mem_contractionIdeal b) 0 m

/-- The contraction `B ⧸ I → (B ⧸ I)[X]`, `[b] ↦ ∑_{n ≥ 0} [c(b)_n] X^n`. -/
def contraction : (B ⧸ contractionIdeal K c ε) →+* (B ⧸ contractionIdeal K c ε)[X] :=
  Ideal.Quotient.lift _ contractionAux fun _ hx => contractionIdeal_le_ker hH hA hx

theorem contraction_mk (b : B) :
    contraction hH hA (Ideal.Quotient.mk (contractionIdeal K c ε) b) =
      contractionAux (K := K) (c := c) (ε := ε) b :=
  Ideal.Quotient.lift_mk _ _ _

theorem eval_zero_contraction (b : B) :
    (contraction hH hA (Ideal.Quotient.mk (contractionIdeal K c ε) b)).eval 0 =
      Ideal.Quotient.mk (contractionIdeal K c ε) (algebraMap K B (ε b)) := by
  rw [contraction_mk, ← coeff_zero_eq_eval_zero, contractionAux, truncHom_apply,
    AffineLine.coeff_trunc, Nat.cast_zero, RingHom.comp_apply, coeff_mapRingHom,
    Ideal.Quotient.eq]
  exact coeff_zero_sub_mem_contractionIdeal b

theorem eval_one_contraction (hE : ∀ b, eval₂ (RingHom.id B) 1 (c b) = b) (b : B) :
    (contraction (ε := ε) hH hA (Ideal.Quotient.mk (contractionIdeal K c ε) b)).eval 1 =
      Ideal.Quotient.mk (contractionIdeal K c ε) b := by
  rw [contraction_mk, contractionAux, truncHom_apply, Polynomial.eval, ← Units.val_one,
    ← eval₂_toLaurent, AffineLine.toLaurent_trunc, RingHom.comp_apply, eval₂_one_mapRingHom, hE]
  intro n hn
  rw [RingHom.comp_apply, coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem]
  exact coeff_mem_contractionIdeal b hn

include hH hA in
/-- **Connectedness from a graded contraction.** Let `c : B →+* B[T, T⁻¹]` be a ring map whose
coefficients are homogeneous (`c(c(b)_n) = c(b)_n T^n`), whose value at `T = 1` is the identity
and which fixes the image of `K`. Let `ε : B →+* K` kill the ideal `I` generated by the negative
coefficients and the differences `c(b)_0 - ε(b)`. If the idempotents of the nontrivial ring `K`
are `0` and `1`, then `Spec (B ⧸ I)` is connected. -/
theorem connectedSpace_contractionIdeal [Nontrivial K]
    (hK : ∀ x : K, IsIdempotentElem x → x = 0 ∨ x = 1)
    (hE : ∀ b, eval₂ (RingHom.id B) 1 (c b) = b)
    (hε : ∀ x ∈ contractionIdeal K c ε, ε x = 0) :
    ConnectedSpace (PrimeSpectrum (B ⧸ contractionIdeal K c ε)) := by
  let ε' : B ⧸ contractionIdeal K c ε →+* K := Ideal.Quotient.lift _ ε hε
  have : Nontrivial (B ⧸ contractionIdeal K c ε) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg ε' h
    rw [map_zero, map_one] at this
    exact zero_ne_one this
  refine connectedSpace_of_contraction (contraction hH hA) (fun d => ?_) (fun d hd => ?_)
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
    exact eval_one_contraction hH hA hE b
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [eval_zero_contraction]
    have hb : ε' (Ideal.Quotient.mk _ b) = ε b := Ideal.Quotient.lift_mk _ _ _
    rcases hK _ (hb ▸ hd.map ε') with h | h
    · left; rw [h, map_zero, map_zero]
    · right; rw [h, map_one, map_one]

end GradedContraction

section Unipotent

open LaurentPolynomial

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Corepresented.groupScheme F e)

theorem unipotentIdeal_eq_contractionIdeal :
    Corepresented.unipotentIdeal χ =
      contractionIdeal (CommRingCat.of k) (Corepresented.coaction χ).hom
        (Corepresented.counit e).hom :=
  rfl

/-- The counit kills the ideal of the unipotent subgroup: the identity point lies in
`U_G(χ)`. -/
theorem counit_eq_zero_of_mem_unipotentIdeal {x : B} (hx : x ∈ Corepresented.unipotentIdeal χ) :
    Corepresented.counit e x = 0 :=
  (Corepresented.isAffineCutOutBy_unipotent χ (CommRingCat.of k) (𝟙 _) 1).1
    (Subgroup.one_mem _) x hx

/-- The explicit representative `Spec (B ⧸ I)` of `U_G(χ)` has connected underlying space. -/
theorem connectedSpace_unipotentScheme :
    ConnectedSpace (Corepresented.unipotentScheme χ).X.left := by
  have : Nontrivial (CommRingCat.of k) := inferInstanceAs (Nontrivial k)
  refine connectedSpace_contractionIdeal (K := CommRingCat.of k) (fun b n => ?_)
    (Corepresented.coaction_algebraMap χ)
    (fun (x : k) hx => IsIdempotentElem.iff_eq_zero_or_one.1 hx) (fun b => ?_)
    (fun x hx => counit_eq_zero_of_mem_unipotentIdeal χ hx)
  · rw [Corepresented.coaction_coeff_coaction, single_eq_C_mul_T]
  · exact congrArg (fun φ => φ.hom b) (Corepresented.coaction_comp_laurentEvalOne χ)

end Unipotent

section Representatives

variable {k : Type u} [Field k]

/-- Every representative of `U_G(χ)` has connected underlying space. -/
theorem connectedSpace_of_isRepresentedBy_unipotent (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (Dynamic.unipotent χ).IsRepresentedBy j) : ConnectedSpace H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : ConnectedSpace (Dynamic.Affine.unipotentScheme χ).X.left :=
    connectedSpace_unipotentScheme (Dynamic.Affine.cocharacter χ)
  exact connectedSpace_of_iso
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ))

end Representatives

end DynamicConnected

end Langlands.GroupScheme
