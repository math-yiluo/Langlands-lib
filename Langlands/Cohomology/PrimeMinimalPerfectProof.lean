import Langlands.Cohomology.PrimeMinimalPerfectStatement
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.LocalRing.Module

/-! # Minimal finite free homotopy models at a prime -/

universe u

open CategoryTheory Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

namespace PrimeMinimal

variable {A : Type u} [CommRing A]

/-- Over a local ring, a vector of a finite free module outside `𝔪 • M` takes the value one
under some linear functional. -/
lemma exists_functional_eq_one [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M] (w : M)
    (hw : w ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    ∃ f : M →ₗ[A] A, f w = 1 := by
  let b := Module.Free.chooseBasis A M
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (b.repr w j) := by
    by_contra h
    push Not at h
    apply hw
    rw [← b.sum_repr w]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).2 (h j)) Submodule.mem_top
  refine ⟨(↑hj.unit⁻¹ : A) • b.coord j, ?_⟩
  simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  exact hj.val_inv_mul

section Kernel

variable {L : CochainComplex (ModuleCat.{u} A) ℤ} (e : L ⟶ L)

/-- The degreewise kernel subcomplex of an endomorphism of a complex of modules. -/
def kerComplex : CochainComplex (ModuleCat.{u} A) ℤ where
  X k := ModuleCat.of A (LinearMap.ker (e.f k).hom)
  d k l := ModuleCat.ofHom ((L.d k l).hom.restrict fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← e.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply, hx, map_zero])
  shape k l h := by
    ext x
    simp [L.shape k l h]
  d_comp_d' k l m _ _ := by
    ext x
    change (L.d k l ≫ L.d l m).hom x.1 = 0
    simp

/-- The inclusion of the kernel subcomplex. -/
def kerComplexι : kerComplex e ⟶ L where
  f k := ModuleCat.ofHom (LinearMap.ker (e.f k).hom).subtype
  comm' _ _ _ := rfl

variable {e}

/-- The retraction `1 - e` onto the kernel subcomplex of an idempotent endomorphism. -/
def kerComplexRetr (he : ∀ k (x : L.X k), (e.f k).hom ((e.f k).hom x) = (e.f k).hom x) :
    L ⟶ kerComplex e where
  f k := ModuleCat.ofHom (LinearMap.codRestrict _ (LinearMap.id - (e.f k).hom) fun x ↦ by
    simp [he])
  comm' k l _ := by
    ext x
    apply Subtype.ext
    change (L.d k l).hom (x - (e.f k).hom x) =
      (L.d k l).hom x - (e.f l).hom ((L.d k l).hom x)
    rw [map_sub, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, e.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply]

variable (he : ∀ k (x : L.X k), (e.f k).hom ((e.f k).hom x) = (e.f k).hom x)
include he

lemma kerComplexι_retr : kerComplexι e ≫ kerComplexRetr he = 𝟙 _ := by
  ext k x
  apply Subtype.ext
  change x.1 - (e.f k).hom x.1 = x.1
  rw [LinearMap.mem_ker.1 x.2, sub_zero]

lemma kerComplexRetr_ι : kerComplexRetr he ≫ kerComplexι e = 𝟙 L - e := by
  ext k x
  rfl

/-- A null-homotopic idempotent endomorphism splits off a contractible summand: its kernel
subcomplex is homotopy equivalent to the whole complex. -/
def kerComplexHomotopyEquiv (H : Homotopy e 0) : HomotopyEquiv (kerComplex e) L where
  hom := kerComplexι e
  inv := kerComplexRetr he
  homotopyHomInvId := Homotopy.ofEq (kerComplexι_retr he)
  homotopyInvHomId := (Homotopy.ofEq (kerComplexRetr_ι he)).trans
    (Homotopy.equivSubZero.symm ((Homotopy.ofEq (sub_sub_cancel _ _)).trans H)).symm

/-- The terms of the kernel subcomplex of an idempotent are direct summands. -/
lemma kerComplex_finite_projective (k : ℤ) [Module.Finite A (L.X k)]
    [Module.Projective A (L.X k)] :
    Module.Finite A ((kerComplex e).X k) ∧ Module.Projective A ((kerComplex e).X k) := by
  have H : ((kerComplexRetr he).f k).hom ∘ₗ ((kerComplexι e).f k).hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, kerComplexι_retr he]
    rfl
  refine ⟨Module.Finite.of_surjective ((kerComplexRetr he).f k).hom fun x ↦
    ⟨((kerComplexι e).f k).hom x, LinearMap.congr_fun H x⟩,
    Module.Projective.of_split _ _ H⟩

omit he in
/-- Complementary submodules of a finite projective module are finite projective. -/
lemma finite_projective_of_isCompl {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {p q : Submodule A M} (h : IsCompl p q) :
    (Module.Finite A p ∧ Module.Projective A p) ∧ (Module.Finite A q ∧ Module.Projective A q) := by
  let E := Submodule.prodEquivOfIsCompl p q h
  have : Module.Finite A (p × q) := Module.Finite.equiv E.symm
  have : Module.Projective A (p × q) := Module.Projective.of_equiv' E.symm
  exact ⟨⟨Module.Finite.of_surjective (LinearMap.fst A p q) LinearMap.fst_surjective,
      Module.Projective.of_split _ _ (LinearMap.fst_comp_inl A p q)⟩,
    ⟨Module.Finite.of_surjective (LinearMap.snd A p q) LinearMap.snd_surjective,
      Module.Projective.of_split _ _ (LinearMap.snd_comp_inr A p q)⟩⟩

omit he in
/-- Over a local ring, the ranks of complementary summands of a finite projective module add
up to its rank. -/
lemma finrank_add_of_isCompl [IsLocalRing A] {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {p q : Submodule A M} (h : IsCompl p q) :
    Module.finrank A p + Module.finrank A q = Module.finrank A M := by
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := finite_projective_of_isCompl h
  have : Module.Free A p := Module.free_of_flat_of_isLocalRing
  have : Module.Free A q := Module.free_of_flat_of_isLocalRing
  rw [← Module.finrank_prod, (Submodule.prodEquivOfIsCompl p q h).finrank_eq]

/-- Over a local ring, passing to the kernel subcomplex of an idempotent does not increase
term ranks, and strictly decreases the rank where the idempotent is nonzero. -/
lemma finrank_kerComplex [IsLocalRing A] (k : ℤ) [Module.Finite A (L.X k)]
    [Module.Projective A (L.X k)] :
    Module.finrank A ((kerComplex e).X k) ≤ Module.finrank A (L.X k) ∧
      ((e.f k).hom ≠ 0 → Module.finrank A ((kerComplex e).X k) < Module.finrank A (L.X k)) := by
  let s : L.X k →ₗ[A] LinearMap.ker (e.f k).hom := ((kerComplexRetr he).f k).hom
  have hs : ∀ x : LinearMap.ker (e.f k).hom, s x = x := fun x ↦
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.congr_hom (kerComplexι_retr he) k)) x
  have hc := LinearMap.isCompl_of_proj hs
  have hrank := finrank_add_of_isCompl hc
  change Module.finrank A (LinearMap.ker (e.f k).hom) ≤ _ ∧
    (_ → Module.finrank A (LinearMap.ker (e.f k).hom) < _)
  refine ⟨hrank ▸ Nat.le_add_right _ _, fun hne ↦ ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, (e.f k).hom x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  have hmem : (e.f k).hom x ∈ LinearMap.ker s := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (e.f k).hom x - (e.f k).hom ((e.f k).hom x) = 0
    rw [he, sub_self]
  have : Nontrivial (LinearMap.ker s) := ⟨⟨⟨_, hmem⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨-, ⟨_, _⟩⟩ := finite_projective_of_isCompl hc
  have : Module.Free A (LinearMap.ker s) := Module.free_of_flat_of_isLocalRing
  have := (Module.finrank_pos_iff_of_free A (LinearMap.ker s)).2 inferInstance
  omega

end Kernel

section Elementary

variable (L : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) (f : L.X (i + 1) →ₗ[A] A) (y : L.X i)

/-- The family of functionals equal to `f` in degree `i + 1` and zero elsewhere. -/
def funFamily : ∀ k, L.X k →ₗ[A] A := Pi.single (i + 1) f

/-- The family of vectors equal to `y` in degree `i` and zero elsewhere. -/
def vecFamily : ∀ k, (L.X k : Type u) := Pi.single i y

/-- The elementary homotopy `z ↦ φ_k(z) • v_{k-1}`, nonzero only from degree `i + 1` to `i`. -/
def elemHomotopy (k l : ℤ) (_ : (ComplexShape.up ℤ).Rel l k) : L.X k ⟶ L.X l :=
  ModuleCat.ofHom ((funFamily L i f k).smulRight (vecFamily L i y l))

/-- The null-homotopic endomorphism `d h + h d` defined by the elementary homotopy. -/
def elemEndo : L ⟶ L :=
  Homotopy.nullHomotopicMap' (elemHomotopy L i f y)

lemma elemEndo_apply (k : ℤ) (z : L.X k) :
    ((elemEndo L i f y).f k).hom z =
      funFamily L i f (k + 1) ((L.d k (k + 1)).hom z) • vecFamily L i y k +
        funFamily L i f k z • (L.d (k - 1) k).hom (vecFamily L i y (k - 1)) := by
  rw [elemEndo, Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℤ) (k₂ := k - 1)
    (k₀ := k + 1) (by simp) (by simp)]
  simp [elemHomotopy]

variable {L i f y} (hf : f ((L.d i (i + 1)).hom y) = 1)
include hf

lemma funFamily_vecFamily (k : ℤ) : funFamily L i f k (vecFamily L i y k) = 0 := by
  by_cases hk : k = i
  · subst hk
    rw [funFamily, Pi.single_eq_of_ne (by omega)]
    rfl
  · rw [vecFamily, Pi.single_eq_of_ne hk, map_zero]

lemma funFamily_d_vecFamily_smul (k : ℤ) :
    funFamily L i f (k + 1) ((L.d k (k + 1)).hom (vecFamily L i y k)) • vecFamily L i y k =
      vecFamily L i y k := by
  by_cases hk : k = i
  · subst hk
    rw [funFamily, vecFamily, Pi.single_eq_same, Pi.single_eq_same, hf, one_smul]
  · rw [vecFamily, Pi.single_eq_of_ne hk, smul_zero]

lemma mul_funFamily_d_vecFamily (j k : ℤ) (hjk : j + 1 = k) (z : L.X k) :
    funFamily L i f k z * funFamily L i f k ((L.d j k).hom (vecFamily L i y j)) =
      funFamily L i f k z := by
  subst hjk
  by_cases hj : j = i
  · subst hj
    rw [funFamily, vecFamily, Pi.single_eq_same, Pi.single_eq_same, hf, mul_one]
  · rw [funFamily, Pi.single_eq_of_ne (by omega)]
    simp

lemma elemEndo_idem (k : ℤ) (z : L.X k) :
    ((elemEndo L i f y).f k).hom (((elemEndo L i f y).f k).hom z) =
      ((elemEndo L i f y).f k).hom z := by
  have hdd : ∀ w, (L.d k (k + 1)).hom ((L.d (k - 1) k).hom w) = 0 := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, L.d_comp_d]
    rfl
  rw [elemEndo_apply L i f y k (((elemEndo L i f y).f k).hom z), elemEndo_apply]
  simp only [map_add, map_smul, hdd, smul_zero, add_zero, smul_eq_mul,
    funFamily_vecFamily hf, mul_zero, zero_add,
    mul_funFamily_d_vecFamily hf (k - 1) k (by omega)]
  rw [mul_smul, funFamily_d_vecFamily_smul hf]

lemma elemEndo_self : ((elemEndo L i f y).f i).hom y = y := by
  rw [elemEndo_apply]
  simp only [funFamily, vecFamily, Pi.single_eq_same, hf, one_smul]
  rw [Pi.single_eq_of_ne (show i ≠ i + 1 by omega)]
  simp

end Elementary

section Local

variable [IsLocalRing A]

/-- One cancellation step: a differential component that is not zero modulo the maximal ideal
splits off a contractible summand, strictly lowering the rank in its source degree. -/
lemma exists_cancel (L : CochainComplex (ModuleCat.{u} A) ℤ)
    (hL : ∀ k, Module.Finite A (L.X k) ∧ Module.Projective A (L.X k)) (i : ℤ) (z : L.X i)
    (hz : (L.d i (i + 1)).hom z ∉
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (L.X (i + 1)))) :
    ∃ M : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ k, Module.Finite A (M.X k) ∧ Module.Projective A (M.X k)) ∧
      Nonempty (HomotopyEquiv M L) ∧
      (∀ k, Module.finrank A (M.X k) ≤ Module.finrank A (L.X k)) ∧
      Module.finrank A (M.X i) < Module.finrank A (L.X i) ∧
      (∀ k, IsZero (L.X k) → IsZero (M.X k)) := by
  obtain ⟨_, _⟩ := hL (i + 1)
  have : Module.Free A (L.X (i + 1)) := Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf⟩ := exists_functional_eq_one _ hz
  have he := elemEndo_idem hf
  refine ⟨kerComplex (elemEndo L i f z), fun k ↦ ?_,
    ⟨kerComplexHomotopyEquiv he (Homotopy.nullHomotopy' _)⟩, fun k ↦ ?_, ?_, fun k hk ↦ ?_⟩
  · obtain ⟨_, _⟩ := hL k
    exact kerComplex_finite_projective he k
  · obtain ⟨_, _⟩ := hL k
    exact (finrank_kerComplex he k).1
  · obtain ⟨_, _⟩ := hL i
    refine (finrank_kerComplex he i).2 fun h ↦ hz ?_
    have hself := elemEndo_self hf
    rw [h, LinearMap.zero_apply] at hself
    rw [← hself, map_zero]
    exact Submodule.zero_mem _
  · have := ModuleCat.subsingleton_of_isZero hk
    have : Subsingleton (LinearMap.ker ((elemEndo L i f z).f k).hom) :=
      ⟨fun x y ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_iff_subsingleton.2 this

/-- Repeated cancellation, by induction on a bound for the total rank: a bounded finite
projective complex over a local ring is homotopy equivalent to one with the same bounds whose
differentials vanish modulo the maximal ideal. -/
lemma exists_minimal_aux (a b : ℤ) (n : ℕ) : ∀ (L : CochainComplex (ModuleCat.{u} A) ℤ),
    L.IsStrictlyGE a → L.IsStrictlyLE b →
    (∀ k, Module.Finite A (L.X k) ∧ Module.Projective A (L.X k)) →
    ∑ k ∈ Finset.Icc a b, Module.finrank A (L.X k) < n →
    ∃ M : CochainComplex (ModuleCat.{u} A) ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ k, Module.Finite A (M.X k) ∧ Module.Projective A (M.X k)) ∧
      Nonempty (HomotopyEquiv M L) ∧
      ∀ k l (x : M.X k), (M.d k l).hom x ∈
        IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M.X l)) := by
  induction n with
  | zero => intro L _ _ _ h; omega
  | succ n ih =>
    intro L ha hb hL hn
    by_cases hmin : ∀ k l (x : L.X k), (L.d k l).hom x ∈
        IsLocalRing.maximalIdeal A • (⊤ : Submodule A (L.X l))
    · exact ⟨L, ha, hb, hL, ⟨HomotopyEquiv.refl L⟩, hmin⟩
    push Not at hmin
    obtain ⟨k, l, x, hx⟩ := hmin
    obtain rfl : l = k + 1 := by
      by_contra h
      rw [L.shape k l (by simp only [ComplexShape.up_Rel]; omega)] at hx
      exact hx (by simp)
    obtain ⟨M, hM, ⟨eM⟩, hle, hlt, hzero⟩ := exists_cancel L hL k x hx
    have hk : k ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      by_contra h
      have hL0 : IsZero (L.X k) := by
        rcases not_and_or.1 h with h | h
        · exact (CochainComplex.isStrictlyGE_iff L a).1 ha k (by omega)
        · exact (CochainComplex.isStrictlyLE_iff L b).1 hb k (by omega)
      have := ModuleCat.subsingleton_of_isZero hL0
      have h0 : Module.finrank A (L.X k) = 0 := Module.finrank_zero_of_subsingleton
      omega
    have hsum : ∑ j ∈ Finset.Icc a b, Module.finrank A (M.X j) <
        ∑ j ∈ Finset.Icc a b, Module.finrank A (L.X j) :=
      Finset.sum_lt_sum (fun j _ ↦ hle j) ⟨k, hk, hlt⟩
    obtain ⟨N, hNa, hNb, hN, ⟨eN⟩, hNmin⟩ := ih M
      ((CochainComplex.isStrictlyGE_iff M a).2 fun j hj ↦
        hzero j ((CochainComplex.isStrictlyGE_iff L a).1 ha j hj))
      ((CochainComplex.isStrictlyLE_iff M b).2 fun j hj ↦
        hzero j ((CochainComplex.isStrictlyLE_iff L b).1 hb j hj))
      hM (by omega)
    exact ⟨N, hNa, hNb, hN, ⟨eN.trans eM⟩, hNmin⟩

end Local

section Residue

variable [IsLocalRing A] {F : Type u} [Field F] (ψ : A →+* F)
  (hψ : ∀ r ∈ IsLocalRing.maximalIdeal A, ψ r = 0)
include hψ

/-- If every differential vanishes modulo the maximal ideal, then scalar extension along a map
to a field killing the maximal ideal has zero differentials. -/
lemma baseChange_d_eq_zero {M : CochainComplex (ModuleCat.{u} A) ℤ}
    (hM : ∀ k l (x : M.X k), (M.d k l).hom x ∈
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M.X l))) (k l : ℤ) :
    ((baseChange ψ).obj M).d k l = 0 := by
  let := ψ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext (M := M.X k)
  intro x
  change (1 : F) ⊗ₜ[A] (M.d k l).hom x = 0
  refine Submodule.smul_induction_on (hM k l x) (fun r hr n _ ↦ ?_) (fun _ _ h₁ h₂ ↦ ?_)
  · rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, hψ r hr, zero_mul, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, h₁, h₂, add_zero]

/-- Over a local ring, a finite free complex whose differentials vanish modulo the maximal ideal
has residue homology of the same dimension as its terms. -/
lemma finrank_homology_baseChange {M : CochainComplex (ModuleCat.{u} A) ℤ}
    (hfree : ∀ k, Module.Finite A (M.X k) ∧ Module.Free A (M.X k))
    (hM : ∀ k l (x : M.X k), (M.d k l).hom x ∈
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M.X l))) (i : ℤ) :
    Module.finrank F (((baseChange ψ).obj M).homology i) = Module.finrank A (M.X i) := by
  let N := (baseChange ψ).obj M
  have hN := baseChange_d_eq_zero ψ hψ hM
  let E : N.homology i ≅ N.X i :=
    (N.isoHomologyπ (i - 1) i (by simp) (hN _ _)).symm ≪≫
      N.iCyclesIso i (i + 1) (by simp) (hN _ _)
  rw [E.toLinearEquiv.finrank_eq]
  let := ψ.toAlgebra
  obtain ⟨_, _⟩ := hfree i
  change Module.finrank F (TensorProduct A F (M.X i)) = _
  exact Module.finrank_baseChange

end Residue

end PrimeMinimal

open PrimeMinimal in
/-- At a prime, the localization of a bounded finite projective complex is homotopy equivalent
to a finite free complex whose term ranks are the residue-field homology dimensions. -/
theorem primeMinimalPerfect : PrimeMinimalPerfectStatement.{u} := by
  intro R _ K hK p _
  refine ⟨finite_homology_baseChange (algebraMap R p.ResidueField) hK, ?_⟩
  obtain ⟨⟨a, b, ha, hb⟩, hKA⟩ :=
    isStrictlyPerfect_baseChange (algebraMap R (Localization.AtPrime p)) hK
  obtain ⟨M, hMa, hMb, hM, ⟨eM⟩, hMmin⟩ :=
    exists_minimal_aux a b _ _ ha hb hKA (Nat.lt_succ_self _)
  have hfree : ∀ k, Module.Finite (Localization.AtPrime p) (M.X k) ∧
      Module.Free (Localization.AtPrime p) (M.X k) := fun k ↦ by
    obtain ⟨_, _⟩ := hM k
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  refine ⟨M, ⟨⟨a, b, hMa, hMb⟩, hfree⟩, ⟨eM⟩, fun i ↦ ?_⟩
  obtain ⟨_, _⟩ := hfree i
  let ρ := IsLocalRing.residue (Localization.AtPrime p)
  have hcomp : ρ.comp (algebraMap R (Localization.AtPrime p)) =
      algebraMap R p.ResidueField :=
    (IsScalarTower.algebraMap_eq R (Localization.AtPrime p) p.ResidueField).symm
  have hrank : Module.finrank p.ResidueField
      (((baseChange (algebraMap R p.ResidueField)).obj K).homology i) =
        Module.finrank (Localization.AtPrime p) (M.X i) := by
    rw [← finrank_homology_baseChange ρ (fun r hr ↦ (IsLocalRing.residue_eq_zero_iff r).2 hr)
      hfree hMmin i, ← hcomp]
    let E₁ := HomologicalComplex.homologyMapIso
      ((baseChangeCompIso (algebraMap R (Localization.AtPrime p)) ρ).app K) i
    let E₂ := (baseChangeHomotopyEquiv ρ eM).toHomologyIso i
    exact (E₁ ≪≫ E₂.symm).toLinearEquiv.finrank_eq
  exact ⟨(Module.finBasisOfFinrankEq _ _ hrank.symm).equivFun⟩

end Langlands.Cohomology.ModuleComplex
