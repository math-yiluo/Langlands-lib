import Langlands.Algebra.PolynomialBoxQuotient
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Rectangular field jets and kernel dimension bounds -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.RationalHeightJets

open CategoryTheory FiniteKernelComposition MvPolynomial

variable {k : Type v} [Field k] {σ τ : Type}

/-- The image of the variable ideal in a rectangular jet. -/
def augmentation (k : Type v) [Field k] (σ : Type) (n : ℕ) :
    Ideal (truncAlg k σ n) :=
  (idealOfVars σ k).map (truncProj k σ n).toRingHom

theorem augmentation_eq_span (n : ℕ) :
    augmentation k σ n = Ideal.span (Set.range fun i => truncProj k σ n (X i)) := by
  rw [augmentation, idealOfVars, Ideal.map_span, ← Set.range_comp]
  rfl

theorem truncProj_X_mem_augmentation (n : ℕ) (i : σ) :
    truncProj k σ n (X i) ∈ augmentation k σ n := by
  rw [augmentation_eq_span]
  exact Ideal.subset_span ⟨i, rfl⟩

theorem augmentation_le_nilradical (n : ℕ) :
    augmentation k σ n ≤ nilradical (truncAlg k σ n) := by
  rw [augmentation_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.mpr ⟨n, truncProj_X_pow n i⟩

theorem augmentation_isNilpotent [Finite σ] (n : ℕ) : IsNilpotent (augmentation k σ n) := by
  have h : (augmentation k σ n).FG := by
    rw [augmentation_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  exact h.isNilpotent_iff_le_nilradical.mpr (augmentation_le_nilradical n)

theorem truncIdeal_le_idealOfVars {n : ℕ} (hn : 0 < n) :
    truncIdeal k σ n ≤ idealOfVars σ k := by
  rw [truncIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact (idealOfVars σ k).pow_mem_of_mem (Ideal.subset_span ⟨i, rfl⟩) _ hn

/-- Evaluation at the origin. -/
def origin {n : ℕ} (hn : 0 < n) : truncAlg k σ n →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : σ => (0 : k))) (by
    have h : truncIdeal k σ n ≤ RingHom.ker (aeval (fun _ : σ => (0 : k))).toRingHom := by
      rw [truncIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change aeval (fun _ : σ => (0 : k)) (X i ^ n) = 0
      rw [map_pow, aeval_X, zero_pow hn.ne']
    exact fun _ hz => h hz)

@[simp]
theorem origin_truncProj {n : ℕ} (hn : 0 < n) (P : MvPolynomial σ k) :
    origin hn (truncProj k σ n P) = P.coeff 0 := by
  change aeval (fun _ : σ => (0 : k)) P = P.coeff 0
  rw [aeval_zero', Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq]

theorem mem_augmentation_of_nilpotent {n : ℕ} (hn : 0 < n) {x : truncAlg k σ n}
    (hx : IsNilpotent x) : x ∈ augmentation k σ n := by
  obtain ⟨P, rfl⟩ := truncProj_surjective n x
  have h0 : P.coeff 0 = 0 := by
    simpa only [origin_truncProj] using (hx.map (origin hn)).eq_zero
  apply Ideal.mem_map_of_mem
  rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff']
  intro a ha
  rwa [(Finsupp.degree_eq_zero_iff a).mp (Nat.lt_one_iff.mp ha)]

/-- At a characteristic-power width, the Frobenius power of every nilpotent
element vanishes. -/
theorem nilpotent_pow_eq_zero [Finite σ] {p : ℕ} [ExpChar k p] (e : ℕ)
    {x : truncAlg k σ (p ^ e)} (hx : IsNilpotent x) : x ^ (p ^ e) = 0 := by
  have hn : 0 < p ^ e := expChar_pow_pos k p e
  have hinj : Function.Injective (algebraMap k (truncAlg k σ (p ^ e))) :=
    Function.LeftInverse.injective (origin hn).commutes
  let := expChar_of_injective_algebraMap hinj p
  have h := mem_augmentation_of_nilpotent hn hx
  rw [augmentation_eq_span] at h
  let := Fintype.ofFinite σ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  change iterateFrobenius (truncAlg k σ (p ^ e)) p e
    (∑ i, r i * truncProj k σ (p ^ e) (X i)) = 0
  simp only [map_sum, iterateFrobenius_def, mul_pow, truncProj_X_pow, mul_zero,
    Finset.sum_const_zero]

theorem truncAlg_hom_ext {n : ℕ} {A : Type*} [CommRing A] [Algebra k A]
    {g h : truncAlg k σ n →ₐ[k] A}
    (he : ∀ i, g (truncProj k σ n (X i)) = h (truncProj k σ n (X i))) : g = h :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext he)

theorem truncIdeal_antitone {n m : ℕ} (hnm : n ≤ m) :
    truncIdeal k σ m ≤ truncIdeal k σ n := by
  rw [truncIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.pow_mem_of_pow_mem _ (Ideal.subset_span ⟨i, rfl⟩) hnm

/-- The map from a deeper to a shallower rectangular jet. -/
def restrictJet {n m : ℕ} (hnm : n ≤ m) : truncAlg k σ m →ₐ[k] truncAlg k σ n :=
  Ideal.Quotient.factorₐ k (truncIdeal_antitone hnm)

@[simp]
theorem restrictJet_truncProj {n m : ℕ} (hnm : n ≤ m) (P : MvPolynomial σ k) :
    restrictJet hnm (truncProj k σ m P) = truncProj k σ n P := rfl

theorem restrictJet_surjective {n m : ℕ} (hnm : n ≤ m) :
    Function.Surjective (restrictJet (k := k) (σ := σ) hnm) := by
  intro y
  obtain ⟨P, rfl⟩ := truncProj_surjective n y
  exact ⟨truncProj k σ m P, rfl⟩

theorem truncIdeal_eq_boxIdeal [Finite σ] (n : ℕ) (hn : 0 < n) :
    truncIdeal k σ n =
      Langlands.Algebra.PolynomialBoxQuotient.boxIdeal
        (Finsupp.equivFunOnFinite.symm fun _ : σ => n - 1) := by
  rw [Langlands.Algebra.PolynomialBoxQuotient.boxIdeal_eq_span]
  simp only [Finsupp.coe_equivFunOnFinite_symm, Nat.sub_add_cancel hn]

instance truncAlg_finite [Finite σ] (n : ℕ) [NeZero n] : Module.Finite k (truncAlg k σ n) := by
  change Module.Finite k (MvPolynomial σ k ⧸ truncIdeal k σ n)
  rw [truncIdeal_eq_boxIdeal n (NeZero.pos n)]
  infer_instance

theorem finrank_truncAlg [Finite σ] (n : ℕ) (hn : 0 < n) :
    Module.finrank k (truncAlg k σ n) = n ^ Nat.card σ := by
  classical
  let := Fintype.ofFinite σ
  change Module.finrank k (MvPolynomial σ k ⧸ truncIdeal k σ n) = _
  rw [truncIdeal_eq_boxIdeal n hn, Langlands.Algebra.PolynomialBoxQuotient.finrank_boxAlgebra]
  by_cases h : n = 1
  · simp [h]
  · have hs : (Finsupp.equivFunOnFinite.symm fun _ : σ => n - 1).support = Finset.univ := by
      ext i
      simp [Nat.sub_ne_zero_iff_lt, show 1 < n by omega]
    simp [hs, Nat.sub_add_cancel hn]

section Maps

variable {O : Type u} [CommRing O] [Algebra O k]
variable [Finite σ] [Finite τ]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ} {υ : Type} [Finite υ]
variable {P : ModuleLaw O k υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The algebra map induced by a formal homomorphism at characteristic-power
width. -/
def mapJet {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) :
    truncAlg k τ (p ^ e) →ₐ[k] truncAlg k σ (p ^ e) :=
  truncLift (f.onAlgebraPoints (truncPoint M (p ^ e))) fun i =>
    nilpotent_pow_eq_zero e (coord_isNilpotent _ i)

@[simp]
theorem mapJet_X {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) (i : τ) :
    mapJet e f (truncProj k τ (p ^ e) (X i)) =
      coord N (f.onAlgebraPoints (truncPoint M (p ^ e))) i :=
  truncLift_X _ _ i

theorem mapJet_point {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) :
    N.algebraMapPoints (mapJet e f) (truncPoint N (p ^ e)) =
      f.onAlgebraPoints (truncPoint M (p ^ e)) :=
  truncLift_point _ _

theorem restrictJet_point {n m : ℕ} (hnm : n ≤ m) :
    M.algebraMapPoints (restrictJet hnm) (truncPoint M m) = truncPoint M n := by
  apply ext_coord
  intro i
  simp only [coord_algebraMapPoints, coord_truncPoint, restrictJet_truncProj]

theorem restrictJet_mapJet {p : ℕ} [ExpChar k p] {e e' : ℕ}
    (h : p ^ e ≤ p ^ e') (f : Hom M N) :
    (restrictJet h).comp (mapJet (p := p) e' f) =
      (mapJet (p := p) e f).comp (restrictJet h) := by
  apply truncAlg_hom_ext
  intro i
  simp only [AlgHom.comp_apply, restrictJet_truncProj, mapJet_X,
    ← coord_algebraMapPoints, Hom.onAlgebraPoints_natural, restrictJet_point]

theorem mapJet_comp {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) (g : Hom N P) :
    mapJet (p := p) e (g.comp f) = (mapJet (p := p) e f).comp (mapJet (p := p) e g) := by
  apply truncAlg_hom_ext
  intro i
  simp only [mapJet_X, AlgHom.comp_apply, Hom.onAlgebraPoints_comp,
    ← coord_algebraMapPoints, Hom.onAlgebraPoints_natural, mapJet_point]

theorem map_augmentation_eq_kerIdeal {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) :
    (augmentation k τ (p ^ e)).map (mapJet e f).toRingHom = kerIdeal M f (p ^ e) := by
  rw [augmentation_eq_span, Ideal.map_span, kerIdeal, ← Set.range_comp]
  exact congrArg (Ideal.span ∘ Set.range) (funext (mapJet_X e f))

theorem finrank_kerAlg_eq {f : Hom M N} (K : Hom.FiniteKernelModel f) {n : ℕ}
    (hn : ∀ (A : CommAlgCat.{v} k) (x : M.AlgebraPoint A), f.onAlgebraPoints x = 0 →
      ∀ i, coord M x i ^ n = 0) :
    Module.finrank k (kerAlg f n) = Module.finrank k K.coordinateAlgebra :=
  (CommAlgCat.algEquivOfIso ((kerRepresents hn).uniqueUpToIso K.represents)).toLinearEquiv.finrank_eq

/-- A kernel of bounded width bounds the relative dimension of jets. Lift a
basis of the kernel algebra and apply Nakayama over the target jet. -/
private theorem finrank_truncAlg_le {p : ℕ} [ExpChar k p] (e : ℕ) (f : Hom M N) :
    Module.finrank k (truncAlg k σ (p ^ e)) ≤
      Module.finrank k (kerAlg f (p ^ e)) * Module.finrank k (truncAlg k τ (p ^ e)) := by
  classical
  let n := p ^ e
  let S := truncAlg k σ n
  let T := truncAlg k τ n
  let φ : T →ₐ[k] S := mapJet (p := p) e f
  let : Algebra T S := φ.toRingHom.toAlgebra
  let : IsScalarTower k T S := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : NeZero n := ⟨(expChar_pow_pos k p e).ne'⟩
  let : Module.Finite k S := truncAlg_finite n
  let : Module.Finite k T := truncAlg_finite n
  let : Module.Finite T S := .of_restrictScalars_finite k T S
  let I := augmentation k τ n
  let J := kerIdeal M f n
  have hIJ : I.map (algebraMap T S) = J := map_augmentation_eq_kerIdeal e f
  have hI : I ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson_bot]
    exact (augmentation_le_nilradical n).trans (nilradical_le_jacobson T)
  let b := Module.finBasis k (S ⧸ J)
  let ρ := Ideal.Quotient.mkₐ k J
  choose z hz using fun i => Ideal.Quotient.mkₐ_surjective k J (b i)
  have hρ (i : Fin (Module.finrank k (S ⧸ J))) : ρ (z i) = b i := hz i
  let W := Submodule.span T (Set.range z)
  have hW : (⊤ : Submodule T S) ≤ W ⊔ I • (⊤ : Submodule T S) := by
    intro x _
    have hw : ∑ i, b.repr (ρ x) i • z i ∈ W :=
      Submodule.sum_mem W fun i _ => Submodule.smul_of_tower_mem W _
        (Submodule.subset_span ⟨i, rfl⟩)
    have hf : ρ (∑ i, b.repr (ρ x) i • z i) = ρ x := by
      change ρ.toLinearMap (∑ i, b.repr (ρ x) i • z i) = ρ x
      simp only [map_sum, map_smul, AlgHom.toLinearMap_apply, hρ, Module.Basis.sum_repr]
    refine Submodule.mem_sup.mpr ⟨_, hw, x - _, ?_, add_sub_cancel _ _⟩
    rw [Ideal.smul_top_eq_map, hIJ]
    change x - _ ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ρ (x - _) = 0
    rw [map_sub, hf, sub_self]
  have htop : W = ⊤ := top_unique <|
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hW
  have hsur : Function.Surjective (Fintype.linearCombination T z) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact htop
  have hr := LinearMap.finrank_le_finrank_of_surjective
    (f := (Fintype.linearCombination T z).restrictScalars k) hsur
  rw [Module.finrank_pi_fintype,
    Finset.sum_const_nat (m := Module.finrank k T) (fun _ _ => rfl),
    Finset.card_univ, Fintype.card_fin] at hr
  exact hr

theorem card_le_of_finiteKernel {p : ℕ} [ExpChar k p] (hp : 1 < p)
    {f : Hom M N} (K : Hom.FiniteKernelModel f) : Nat.card σ ≤ Nat.card τ := by
  let D := Module.finrank k K.coordinateAlgebra
  obtain ⟨a, ha⟩ := exists_kernel_bound K.represents
  let e := max a D
  have he : max a D < p ^ e := Nat.lt_pow_self hp
  have hae : a < p ^ e := (le_max_left a D).trans_lt he
  have hDe : D < p ^ e := (le_max_right a D).trans_lt he
  have hn := expChar_pow_pos k p e
  have hbound := finrank_truncAlg_le (p := p) e f
  rw [finrank_truncAlg _ hn, finrank_truncAlg _ hn,
    finrank_kerAlg_eq K (fun A x hx i => pow_eq_zero_of_le hae (ha A x hx i))] at hbound
  by_contra! h
  have hpw := Nat.pow_le_pow_right hn (Nat.succ_le_of_lt h)
  rw [pow_succ, mul_comm] at hpw
  exact (not_lt_of_ge (hpw.trans hbound)) (Nat.mul_lt_mul_of_pos_right hDe (pow_pos hn _))

end Maps

end Langlands.FormalGroup.ModuleLaw.RationalHeightJets
