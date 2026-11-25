import Langlands.BaseChange.PseudoCoefficient

/-!
# Exact norm representatives in a regular block Levi

At a norm-associated pair with regular semisimple base point in the actual block Levi,
the twisted point can be moved into that same Levi with norm equality on every block.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands Matrix
open _root_.Polynomial

universe u v

section Algebra

variable {R : Type u} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- The characteristic polynomial of a block-diagonal general linear element is the product
of the characteristic polynomials of its diagonal blocks. -/
theorem charpoly_leviEmbedding (m : B.Levi R) :
    (B.leviEmbedding R m : Matrix (Fin n) (Fin n) R).charpoly =
      ∏ i, (m i : Matrix (Fin (B.size i)) (Fin (B.size i)) R).charpoly := by
  let X : Matrix B.Index B.Index R := Matrix.blockDiagonal' (fun i => (m i).val)
  change (Matrix.reindex B.indexEquiv B.indexEquiv X).charpoly = _
  rw [Matrix.charpoly_reindex]
  have ht : X.BlockTriangular (fun a : B.Index => a.1) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    exact Matrix.blockDiagonal'_apply_ne (fun k => (m k).val) a b (show i ≠ j from ne_of_gt hij)
  rw [ht.charpoly]
  have hs : Function.Surjective (fun a : B.Index => a.1) :=
    fun i => ⟨⟨i, ⟨0, B.positive i⟩⟩, rfl⟩
  rw [Finset.image_univ_of_surjective hs]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e : Fin (B.size i) ≃ {x : B.Index // x.1 = i} :=
    Equiv.ofBijective (fun a => ⟨⟨i, a⟩, rfl⟩) ⟨fun a b h => by
      injection h with h
      exact eq_of_heq (Sigma.mk.inj_iff.1 h).2,
      fun y => by
        obtain ⟨⟨j, b⟩, h⟩ := y
        change j = i at h
        subst j
        exact ⟨b, rfl⟩⟩
  rw [← Matrix.charpoly_reindex e.symm]
  congr 1
  ext a b
  change X ⟨i, a⟩ ⟨i, b⟩ = _
  exact Matrix.blockDiagonal'_apply_eq (fun k : Fin B.length => (m k).val) i a b

private def leviCoordinateAlgebra :
    (∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R) →ₐ[R]
      Matrix B.Index B.Index R :=
  { Matrix.blockDiagonal'RingHom (fun i : Fin B.length => Fin (B.size i)) R with
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      exact (Matrix.blockDiagonal'_smul r _).trans (by rw [Matrix.blockDiagonal'_one]) }

private theorem offDiagonal_eq_zero_of_commute
    (m : B.Levi R) (Y : Matrix B.Index B.Index R)
    (hY : Commute Y (Matrix.blockDiagonal' (fun i => (m i).val)))
    (hm : (∏ i, (m i).val.charpoly).Separable)
    {i j : Fin B.length} (hij : i ≠ j) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    Y ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  classical
  let p : Fin B.length → R[X] := fun k => (m k).val.charpoly
  let q : R[X] := ∏ k ∈ Finset.univ.erase i, p k
  have hprod : p i * q = ∏ k, p k := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hsep : (p i * q).Separable := hprod.symm ▸ hm
  obtain ⟨c, d, hcd⟩ := hsep.isCoprime
  let X : Matrix B.Index B.Index R := Matrix.blockDiagonal' (fun k => (m k).val)
  let D := Matrix.diagonal (fun a : B.Index => if a.1 = i then (1 : R) else 0)
  have hD : aeval X (d * q) = D := by
    change aeval (leviCoordinateAlgebra (R := R) B (fun k => (m k).val)) (d * q) = D
    rw [Polynomial.aeval_algHom_apply]
    simp only [Polynomial.aeval_pi_apply]
    have hcomponents : (fun k => aeval (m k).val (d * q)) =
        fun k => Matrix.diagonal (fun _ : Fin (B.size k) => if k = i then (1 : R) else 0) := by
      funext k
      by_cases hki : k = i
      · subst k
        have he := congrArg (aeval (m i).val) hcd
        simp only [map_add, map_mul, map_one, show p i = (m i).val.charpoly from rfl,
          Matrix.aeval_self_charpoly, mul_zero, zero_add] at he
        simpa using he
      · have hdiv : p k ∣ q := Finset.dvd_prod_of_mem p (Finset.mem_erase.2 ⟨hki, Finset.mem_univ _⟩)
        obtain ⟨r, hr⟩ := hdiv
        rw [hr, map_mul, map_mul]
        simp [p, hki, Matrix.aeval_self_charpoly]
    rw [hcomponents]
    exact Matrix.blockDiagonal'_diagonal
      (fun k (a : Fin (B.size k)) => if k = i then (1 : R) else 0)
  have hcomm (f : R[X]) : Commute Y (aeval X f) := by
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      rw [map_add]
      exact hf.add_right hg
    | monomial k c =>
      rw [Polynomial.aeval_monomial]
      have hcY : Commute Y (algebraMap R (Matrix B.Index B.Index R) c) :=
        (Algebra.commutes c Y).symm
      exact hcY.mul_right (hY.pow_right k)
  have hentry := congrArg (fun M : Matrix B.Index B.Index R => M ⟨i, a⟩ ⟨j, b⟩)
    ((hD ▸ hcomm (d * q) : Commute Y D).eq)
  simpa [D, Matrix.mul_diagonal, Matrix.diagonal_mul, hij, hij.symm] using hentry.symm

end Algebra

section Regular

variable {R : Type u} [Field R] {n : ℕ} (B : BlockShape n)

/-- A matrix commuting with a regular semisimple element of a block Levi lies in that Levi.
The off-diagonal blocks vanish because the block projectors are polynomials in the element. -/
theorem mem_leviSubgroup_of_commute_regular {m : B.Levi R} {g : GeneralLinear n R}
    (hm : IsRegularSemisimple (B.leviEmbedding R m))
    (hg : Commute g (B.leviEmbedding R m)) : g ∈ B.leviSubgroup R := by
  rw [IsRegularSemisimple, charpoly_leviEmbedding] at hm
  let e := reindex (R := R) B.indexEquiv
  have hreindex : e.symm (B.leviEmbedding R m) = B.sigmaLeviEmbedding R m :=
    e.symm_apply_apply _
  have hc := hg.map e.symm.toMonoidHom
  change Commute (e.symm g) (e.symm (B.leviEmbedding R m)) at hc
  rw [hreindex] at hc
  have hc' : Commute (e.symm g).val (Matrix.blockDiagonal' fun i => (m i).val) :=
    congrArg Units.val hc.eq
  have hz (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)) (hij : i ≠ j) :
      g (B.index i a) (B.index j b) = 0 :=
    offDiagonal_eq_zero_of_commute B m (e.symm g).val hc' hm hij a b
  have hp : g ∈ B.parabolic R := (B.mem_parabolic_iff R g).mpr
    (fun i j a b hij => hz i j a b (ne_of_gt hij))
  refine ⟨B.leviProjection R ⟨g, hp⟩, ?_⟩
  apply Units.ext
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change B.leviEmbedding R (B.leviProjection R ⟨g, hp⟩) (B.index i a) (B.index j b) =
    g (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviProjection_apply]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, hz i j a b hij]

end Regular

section Norm

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}

/-- Choose a twisted conjugate with exact norm equal to the base-changed representative.
That conjugate commutes with its norm. -/
theorem IsNormAssociated.exists_cyclicNorm_eq_and_commute
    {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (h : IsNormAssociated σ l δ γ) (hσ : σ ^ l = 1) :
    ∃ x : GeneralLinear n E,
      let d := x⁻¹ * δ * entrywiseAut σ n x
      cyclicNorm σ l d = baseChange F E n γ ∧ Commute d (baseChange F E n γ) := by
  obtain ⟨x, hx⟩ := h
  let d := x⁻¹ * δ * entrywiseAut σ n x
  have hd : cyclicNorm σ l d = baseChange F E n γ := by
    exact (by simpa only [d, cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply] using hx)
  refine ⟨x, hd, ?_⟩
  change Commute d (baseChange F E n γ)
  have he := entrywiseAut_cyclicNorm σ l d
  rw [hd, entrywiseAut_baseChange, hσ, entrywiseAut_one_apply] at he
  show d * baseChange F E n γ = baseChange F E n γ * d
  calc
    _ = d * (d⁻¹ * baseChange F E n γ * d) := congrArg (d * ·) he
    _ = _ := by group

/-- Base change and the block diagonal inclusion commute. -/
theorem baseChange_leviEmbedding (B : BlockShape n) (m : B.Levi F) :
    baseChange F E n (B.leviEmbedding F m) =
      B.leviEmbedding E (fun i => baseChange F E (B.size i) (m i)) := by
  apply Units.ext
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change baseChange F E n (B.leviEmbedding F m) (B.index i a) (B.index j b) =
    B.leviEmbedding E (fun k => baseChange F E (B.size k) (m k)) (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    simp only [baseChange_apply_apply, BlockShape.leviEmbedding_apply_same]
  · simp only [baseChange_apply_apply, BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, map_zero]

/-- The cyclic norm of a block diagonal element is the block diagonal inclusion of its
block norms. -/
theorem cyclicNorm_leviEmbedding (σ : E ≃ₐ[F] E) (l : ℕ) (B : BlockShape n) (d : B.Levi E) :
    cyclicNorm σ l (B.leviEmbedding E d) =
      B.leviEmbedding E (fun i => cyclicNorm σ l (d i)) := by
  induction l with
  | zero => simp only [cyclicNorm_zero, ← Pi.one_def, map_one]
  | succ l ih =>
    rw [cyclicNorm_succ, ih, entrywiseAut_leviEmbedding, ← map_mul]
    congr 1
    funext i
    rw [cyclicNorm_succ]
    rfl

/-- The twisted centralizer of an element with exact regular norm in the base-field Levi
lies in the extension-field Levi. This is the centralizer-containment input for descent
at this representative. -/
theorem sigmaCentralizer_le_leviSubgroup_of_regularNorm (B : BlockShape n)
    {δ : GeneralLinear n E} {m : B.Levi F} (hσ : σ ^ l = 1)
    (hN : cyclicNorm σ l δ = baseChange F E n (B.leviEmbedding F m))
    (hm : IsRegularSemisimple (B.leviEmbedding F m)) :
    sigmaCentralizer σ n δ ≤ B.leviSubgroup E := by
  intro z hz
  have hfix := (mem_sigmaCentralizer σ n δ z).mp hz
  have hc := cyclicNorm_twistedConj σ l z δ
  rw [hfix, hσ, entrywiseAut_one_apply, hN, baseChange_leviEmbedding] at hc
  have hreg := isRegularSemisimple_baseChange (E := E) hm
  rw [baseChange_leviEmbedding] at hreg
  apply mem_leviSubgroup_of_commute_regular B hreg
  change z * _ = _ * z
  calc
    _ = z * (z⁻¹ * _ * z) := congrArg (z * ·) hc
    _ = _ := by group

end Norm

/-- At an associated pair with a regular semisimple base point already in a block Levi,
there is a twisted conjugate in the Levi having exact norm equality in each block. -/
def RegularLeviNormRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), σ ^ l = 1 →
    ∀ (B : BlockShape n) (m : B.Levi F) (δ : GeneralLinear n E),
      IsNormAssociated σ l δ (B.leviEmbedding F m) →
      IsRegularSemisimple (B.leviEmbedding F m) →
      ∃ (x : GeneralLinear n E) (d : B.Levi E),
        x⁻¹ * δ * entrywiseAut σ n x = B.leviEmbedding E d ∧
        ∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i) ∧
          IsRegularSemisimple (m i)

/-- The regular Levi norm representative via descent of the cyclic norm and its centralizer. -/
theorem regularLeviNormRepresentative : RegularLeviNormRepresentativeStatement.{u, v} := by
  intro F _ E _ _ σ l n hσ B m δ ha hr
  let mE : B.Levi E := fun i => baseChange F E (B.size i) (m i)
  have hbc : baseChange F E n (B.leviEmbedding F m) = B.leviEmbedding E mE :=
    baseChange_leviEmbedding B m
  obtain ⟨x, hn, hc⟩ := ha.exists_cyclicNorm_eq_and_commute hσ
  let δ' := x⁻¹ * δ * entrywiseAut σ n x
  change cyclicNorm σ l δ' = _ at hn
  change Commute δ' _ at hc
  have hrE := isRegularSemisimple_baseChange (E := E) hr
  have hLevi : δ' ∈ B.leviSubgroup E :=
    mem_leviSubgroup_of_commute_regular B (hbc ▸ hrE) (hbc ▸ hc)
  obtain ⟨d, hd⟩ := hLevi
  have hExact : (fun i => cyclicNorm σ l (d i)) = mE := B.leviEmbedding_injective E (by
    rw [← cyclicNorm_leviEmbedding, hd, hn, hbc])
  rw [IsRegularSemisimple, charpoly_leviEmbedding] at hr
  exact ⟨x, d, hd.symm, fun i => ⟨congrFun hExact i,
    hr.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))⟩⟩

end Langlands.BaseChange
