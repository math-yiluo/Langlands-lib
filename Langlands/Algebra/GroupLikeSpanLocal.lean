import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.MonoidAlgebra.Module
import Langlands.Algebra.NilpotentModuleFiniteness
import Langlands.Algebra.GroupLikeReconstruction

/-! # Group-like spanned flat Hopf algebras over local rings

Over a local ring `R`, a flat finitely presented commutative Hopf algebra spanned by its group-like
elements has linearly independent group-like elements; they form a finitely generated group and a
basis, and the Hopf algebra is the group algebra of this group as a bialgebra.
See the paired Markdown file for the proof outline. -/

noncomputable section

open TensorProduct

universe u v w

namespace Langlands.GroupLikeSpan

section charKer

variable {B : Type*} [CommRing B] {Γ : Type*} [CommGroup Γ] (y : Γ →* B)

/-- Elements of `Γ` whose image is congruent to one modulo an ideal. -/
def congrKer (I : Ideal B) : Subgroup Γ where
  carrier := {γ | y γ - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {γ δ} hγ hδ := by
    have : y (γ * δ) - 1 = y γ * (y δ - 1) + (y γ - 1) := by rw [map_mul]; ring
    simp only [Set.mem_ofPred_eq] at *
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hδ) hγ
  inv_mem' {γ} hγ := by
    have h1 : y γ⁻¹ * y γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have : y γ⁻¹ - 1 = -(y γ⁻¹ * (y γ - 1)) := by linear_combination h1
    simp only [Set.mem_ofPred_eq] at *
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hγ)

theorem mem_congrKer {I : Ideal B} {γ : Γ} : γ ∈ congrKer y I ↔ y γ - 1 ∈ I := Iff.rfl

theorem congrKer_mk_eq_mk_iff {I : Ideal B} {γ δ : Γ} :
    (QuotientGroup.mk γ : Γ ⧸ congrKer y I) = QuotientGroup.mk δ ↔ y γ - y δ ∈ I := by
  rw [QuotientGroup.eq, mem_congrKer]
  have h1 : y γ⁻¹ * y γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e1 : y (γ⁻¹ * δ) - 1 = -y γ⁻¹ * (y γ - y δ) := by
    rw [map_mul]; linear_combination h1
  have e2 : y γ - y δ = -y γ * (y (γ⁻¹ * δ) - 1) := by
    rw [map_mul]; linear_combination y δ * h1
  constructor
  · intro h; rw [e2]; exact Ideal.mul_mem_left _ _ h
  · intro h; rw [e1]; exact Ideal.mul_mem_left _ _ h

theorem congrKer_mono {I J : Ideal B} (h : I ≤ J) : congrKer y I ≤ congrKer y J :=
  fun _ hγ => h hγ

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] (x : Γ →* A)

/-- Characters congruent to one modulo the extension of an ideal of the base. -/
def charKer (I : Ideal R) : Subgroup Γ := congrKer x (I.map (algebraMap R A))

theorem mem_charKer {I : Ideal R} {γ : Γ} :
    γ ∈ charKer x I ↔ x γ - 1 ∈ I.map (algebraMap R A) := Iff.rfl

theorem mk_eq_mk_iff {I : Ideal R} {γ δ : Γ} :
    (QuotientGroup.mk γ : Γ ⧸ charKer x I) = QuotientGroup.mk δ ↔
      x γ - x δ ∈ I.map (algebraMap R A) :=
  congrKer_mk_eq_mk_iff x

theorem charKer_mono {I J : Ideal R} (h : I ≤ J) : charKer x I ≤ charKer x J :=
  congrKer_mono x (Ideal.map_mono h)

end charKer

section tensor

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

/-- `1 ⊗ a` vanishes in `(R ⧸ I) ⊗ A` exactly when `a` lies in the extension of `I`. -/
theorem one_tmul_eq_zero_iff (I : Ideal R) (a : A) :
    (1 : R ⧸ I) ⊗ₜ[R] a = 0 ↔ a ∈ I.map (algebraMap R A) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul A I).map_eq_zero_iff,
    ← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map]
  rfl

theorem mem_smul_top_iff_mem_map (I : Ideal R) (a : A) :
    a ∈ I • (⊤ : Submodule R A) ↔ a ∈ I.map (algebraMap R A) := by
  rw [Ideal.smul_top_eq_map]; rfl

/-- Coordinates of an element of `I • ⊤` in a basis lie in `I`. -/
theorem basis_repr_mem_of_mem_smul_top {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (b : Module.Basis ι R M) (I : Ideal R) {m : M}
    (hm : m ∈ I • (⊤ : Submodule R M)) (i : ι) : b.repr m i ∈ I := by
  refine Submodule.smul_induction_on hm (fun r hr n _ => ?_) (fun m n hm hn => ?_)
  · simpa using I.mul_mem_right _ hr
  · simpa using I.add_mem hm hn

end tensor

section fibre

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
  {Γ : Type w} [CommGroup Γ] (x : Γ →* A)

/-- Spanning families stay spanning after scalar extension. -/
theorem span_one_tmul_eq_top (S : Type*) [CommRing S] [Algebra R S]
    (hspan : Submodule.span R (Set.range x) = ⊤) :
    Submodule.span S (Set.range fun γ => (1 : S) ⊗ₜ[R] x γ) = ⊤ := by
  have h := Submodule.baseChange_span (R := R) (A := S) (Set.range x)
  rw [hspan, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h.symm

/-- Group-like elements stay group-like after scalar extension. -/
theorem isGroupLikeElem_one_tmul (S : Type*) [CommRing S] [Algebra R S] {a : A}
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem S ((1 : S) ⊗ₜ[R] a) where
  counit_eq_one := by simp [ha]
  comul_eq_tmul_self := by simp [ha]

/-- Scalar extension carries the extension of an ideal to the extension of its image. -/
theorem one_tmul_mem_map {S : Type*} [CommRing S] [Algebra R S] (J : Ideal R) {a : A}
    (ha : a ∈ J.map (algebraMap R A)) :
    (1 : S) ⊗ₜ[R] a ∈ (J.map (algebraMap R S)).map (algebraMap S (S ⊗[R] A)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hle : J.map (algebraMap R A) ≤ (J.map (algebraMap R (S ⊗[R] A))).comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr
  simpa using hle ha

/-- Prime-fibre coordinates: modulo a prime `q`, the coefficients of a relation which lies in the
extension of an ideal `J ⊇ q` have coset sums in `J`. -/
theorem coeff_mem_of_mem_map [Module.Flat R A] (hx : ∀ γ, IsGroupLikeElem R (x γ))
    (hspan : Submodule.span R (Set.range x) = ⊤) (q : Ideal R) [q.IsPrime] {J : Ideal R}
    (hqJ : q ≤ J) {H : Subgroup Γ} (hH : charKer x q = H) (a : Γ →₀ R)
    (ha : Finsupp.linearCombination R x a ∈ J.map (algebraMap R A)) (c : Γ ⧸ H) :
    Finsupp.mapDomain (QuotientGroup.mk : Γ → Γ ⧸ H) a c ∈ J := by
  subst hH
  classical
  let y : Γ → GroupLike (R ⧸ q) ((R ⧸ q) ⊗[R] A) := fun γ =>
    ⟨(1 : R ⧸ q) ⊗ₜ[R] x γ, isGroupLikeElem_one_tmul (R ⧸ q) (hx γ)⟩
  have hB : ⊤ ≤ Submodule.span (R ⧸ q)
      (Set.range (GroupLike.val (R := R ⧸ q) (A := (R ⧸ q) ⊗[R] A))) := by
    rw [← span_one_tmul_eq_top x (R ⧸ q) hspan]
    exact Submodule.span_mono (by rintro _ ⟨γ, rfl⟩; exact ⟨y γ, rfl⟩)
  let B := Module.Basis.mk (linearIndep_groupLikeVal (R := R ⧸ q)
    (A := (R ⧸ q) ⊗[R] A)) hB
  let yb : Γ ⧸ charKer x q → GroupLike (R ⧸ q) ((R ⧸ q) ⊗[R] A) := fun c => y c.out
  have hyeq : ∀ γ δ : Γ, y γ = y δ ↔
      (QuotientGroup.mk γ : Γ ⧸ charKer x q) = QuotientGroup.mk δ := by
    intro γ δ
    rw [mk_eq_mk_iff, ← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, sub_eq_zero,
      ← GroupLike.val_inj]
  have hy : ∀ γ, y γ = yb (QuotientGroup.mk γ) := by
    intro γ
    rw [hyeq, QuotientGroup.out_eq']
  have hyb : Function.Injective yb := by
    intro c d hcd
    have := (hyeq _ _).1 hcd
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hrepr : ∀ a : Γ →₀ R,
      B.repr ((1 : R ⧸ q) ⊗ₜ[R] Finsupp.linearCombination R x a) =
      Finsupp.mapDomain yb (Finsupp.mapRange (Ideal.Quotient.mk q) (map_zero _)
        (Finsupp.mapDomain QuotientGroup.mk a)) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add, TensorProduct.tmul_add, map_add, hf, hg, Finsupp.mapDomain_add,
        Finsupp.mapRange_add (map_add _), Finsupp.mapDomain_add]
    | single γ r =>
      have h1 : (1 : R ⧸ q) ⊗ₜ[R] Finsupp.linearCombination R x (Finsupp.single γ r) =
          (Ideal.Quotient.mk q r) • B (y γ) := by
        simp only [B, Module.Basis.mk_apply, y, Finsupp.linearCombination_single]
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
      rw [h1, map_smul, Module.Basis.repr_self, Finsupp.mapDomain_single,
        Finsupp.mapRange_single, Finsupp.mapDomain_single, ← hy, Finsupp.smul_single,
        smul_eq_mul, mul_one]
  have hmem := (mem_smul_top_iff_mem_map _ _).2 (one_tmul_mem_map (S := R ⧸ q) J ha)
  have hc := basis_repr_mem_of_mem_smul_top B _ hmem (yb c)
  rw [hrepr, Finsupp.mapDomain_apply_of_injective hyb, Finsupp.mapRange_apply,
    Ideal.Quotient.algebraMap_eq] at hc
  exact (Ideal.mem_quotient_iff_mem hqJ).1 hc

/-- For a proper ideal `J` containing a prime `q`, the congruence subgroups agree. -/
theorem charKer_eq_of_isPrime_le [Module.Flat R A] (hx : ∀ γ, IsGroupLikeElem R (x γ))
    (hspan : Submodule.span R (Set.range x) = ⊤) (q : Ideal R) [q.IsPrime] {J : Ideal R}
    (hJ : J ≠ ⊤) (hqJ : q ≤ J) : charKer x J = charKer x q := by
  classical
  refine le_antisymm (fun γ hγ => ?_) (charKer_mono x hqJ)
  by_contra hγq
  have ha : Finsupp.linearCombination R x (Finsupp.single γ 1 - Finsupp.single 1 1) ∈
      J.map (algebraMap R A) := by
    simpa using (mem_charKer x).1 hγ
  have h := coeff_mem_of_mem_map x hx hspan q hqJ rfl _ ha (QuotientGroup.mk γ)
  have hne : (1 : Γ ⧸ charKer x q) ≠ (γ : Γ ⧸ charKer x q) := by
    rw [ne_eq, eq_comm, QuotientGroup.eq_one_iff]
    exact hγq
  simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.coe_sub, Pi.sub_apply,
    Finsupp.single_eq_same, QuotientGroup.mk_one, Finsupp.single_apply, hne, ↓reduceIte,
    sub_zero] at h
  exact hJ ((Ideal.eq_top_iff_one J).2 h)

/-- Over a local base, the congruence subgroup of every prime is that of the maximal ideal. -/
theorem charKer_eq_maximalIdeal [IsLocalRing R] [Module.Flat R A]
    (hx : ∀ γ, IsGroupLikeElem R (x γ)) (hspan : Submodule.span R (Set.range x) = ⊤)
    (q : Ideal R) [q.IsPrime] : charKer x q = charKer x (IsLocalRing.maximalIdeal R) :=
  (charKer_eq_of_isPrime_le x hx hspan q (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))).symm

/-- Over a local base, coset sums of a linear relation are nilpotent. -/
theorem coeff_mem_nilradical [IsLocalRing R] [Module.Flat R A]
    (hx : ∀ γ, IsGroupLikeElem R (x γ)) (hspan : Submodule.span R (Set.range x) = ⊤)
    (a : Γ →₀ R) (ha : Finsupp.linearCombination R x a = 0)
    (c : Γ ⧸ charKer x (IsLocalRing.maximalIdeal R)) :
    Finsupp.mapDomain QuotientGroup.mk a c ∈ nilradical R := by
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro q hq
  have : q.IsPrime := hq
  exact coeff_mem_of_mem_map x hx hspan q le_rfl (charKer_eq_maximalIdeal x hx hspan q) a
    (by rw [ha]; exact zero_mem _) c

end fibre

section nakayama

variable {S : Type*} [CommRing S] {B : Type*} [CommRing B] [Algebra S B]
  {Γ : Type*} [CommGroup Γ] (y : Γ →* B)

/-- Fibrewise triviality of a finitely generated subgroup of characters, in the presence of a
linear retraction onto the group algebra of the quotient, implies triviality. -/
theorem eq_one_of_forall_isPrime (hspan : Submodule.span S (Set.range y) = ⊤)
    (K : Subgroup Γ) (hK : K.FG) (π : B →ₗ[S] (Γ ⧸ K →₀ S))
    (hπ : ∀ γ, π (y γ) = Finsupp.single (QuotientGroup.mk γ) 1)
    (hfib : ∀ P : Ideal S, P.IsPrime → ∀ κ ∈ K, y κ - 1 ∈ P.map (algebraMap S B))
    {κ : Γ} (hκ : κ ∈ K) : y κ = 1 := by
  classical
  obtain ⟨s, hs⟩ := Subgroup.isMulFG_iff.mp hK
  let 𝔞 : Ideal B := Ideal.span ((fun κ => y κ - 1) '' (s : Set Γ))
  have h𝔞fg : (𝔞 : Submodule B B).FG := ⟨s.image (fun κ => y κ - 1), by simp [𝔞]⟩
  have hK𝔞 : K ≤ congrKer y 𝔞 := by
    rw [← hs, Subgroup.closure_le]
    intro κ hκ
    exact Ideal.subset_span ⟨κ, hκ, rfl⟩
  let σ : (Γ ⧸ K →₀ S) →ₗ[S] B := Finsupp.linearCombination S (fun c => y c.out)
  let ρ : B →ₗ[S] B := LinearMap.id - σ ∘ₗ π
  have hρ𝔞 : ∀ b, ρ b ∈ 𝔞 := by
    have hsp : Submodule.span S (Set.range y) ≤ (𝔞.restrictScalars S).comap ρ := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hmem : γ⁻¹ * (QuotientGroup.mk γ : Γ ⧸ K).out ∈ K := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      have e : ρ (y γ) = -(y γ * (y (γ⁻¹ * (QuotientGroup.mk γ : Γ ⧸ K).out) - 1)) := by
        simp only [ρ, σ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hπ,
          Finsupp.linearCombination_single, one_smul]
        rw [map_mul, mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
        ring
      show ρ (y γ) ∈ 𝔞
      rw [e]
      exact neg_mem (Ideal.mul_mem_left _ _ (hK𝔞 hmem))
    intro b
    exact hsp (hspan ▸ Submodule.mem_top)
  have hρgen : ∀ κ ∈ K, ρ (y κ - 1) = y κ - 1 := by
    intro κ hκ
    have h1 : π (y κ - 1) = 0 := by
      rw [map_sub, hπ, ← map_one y, hπ, sub_eq_zero, (QuotientGroup.eq_one_iff κ).2 hκ]
      rfl
    simp [ρ, h1]
  have hle : ∀ Q : Ideal B, Q.IsMaximal → 𝔞 ≤ Q • 𝔞 := by
    intro Q hQ
    rw [Ideal.span_le]
    rintro _ ⟨κ, hκs, rfl⟩
    have hκK : κ ∈ K := hs ▸ Subgroup.subset_closure hκs
    have hP := hfib (Q.comap (algebraMap S B)) (Ideal.comap_isPrime _ _) κ hκK
    rw [← mem_smul_top_iff_mem_map] at hP
    have h2 := Submodule.mem_map_of_mem (f := ρ) hP
    rw [Submodule.map_smul'', hρgen κ hκK] at h2
    have h3 : (⊤ : Submodule S B).map ρ ≤ 𝔞.restrictScalars S := by
      rintro _ ⟨b, -, rfl⟩
      exact hρ𝔞 b
    have h4 := Submodule.smul_mono le_rfl h3 h2
    have h5 : Q.comap (algebraMap S B) • 𝔞.restrictScalars S ≤ (Q • 𝔞).restrictScalars S := by
      rw [Submodule.smul_le]
      intro p hp a ha
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul B p a]
      exact Submodule.smul_mem_smul hp ha
    exact h5 h4
  have hann : (𝔞 : Submodule B B).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle'⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul Q _ h𝔞fg (hle Q hQ)
    have hrQ : r ∈ Q := hle' (Submodule.mem_annihilator.2 hr)
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Q.sub_mem hrQ hr1))
  have h1 : (1 : B) ∈ (𝔞 : Submodule B B).annihilator := hann ▸ Submodule.mem_top
  have h2 := Submodule.mem_annihilator.1 h1 _ (hK𝔞 hκ)
  rwa [one_smul, sub_eq_zero] at h2

end nakayama

section finiteness

/-- A surjection from a finite-type algebra onto a finitely presented algebra has finitely
generated kernel. -/
theorem ker_fg_of_finiteType {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FinitePresentation R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : (RingHom.ker f.toRingHom).FG := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R A›
  convert! (Algebra.FinitePresentation.ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg)).map
    g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap, Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R →+* A) hg]

/-- Subgroups of finitely generated commutative groups are finitely generated. -/
theorem subgroup_fg {Γ : Type*} [CommGroup Γ] [Group.FG Γ] (K : Subgroup Γ) : K.FG := by
  have : Module.Finite ℤ (Additive Γ) := Module.Finite.iff_addGroup_fg.2 inferInstance
  rw [Subgroup.fg_iff_add_fg]
  exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule K.toAddSubgroup)).1
    (IsNoetherian.noetherian _)

end finiteness

section localRing

open IsLocalRing

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
  {Γ : Type w} [CommGroup Γ] (x : Γ →* A)

/-- Evaluating the group algebra at the characters is the corresponding linear combination. -/
theorem lift_eq_linearCombination (f : MonoidAlgebra R Γ) :
    MonoidAlgebra.lift R A Γ x f = Finsupp.linearCombination R x f.coeff := by
  rw [MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]

/-- If the characters span, evaluation of the group algebra is surjective. -/
theorem lift_surjective (hspan : Submodule.span R (Set.range x) = ⊤) :
    Function.Surjective (MonoidAlgebra.lift R A Γ x) := by
  intro a
  have ha : a ∈ LinearMap.range (Finsupp.linearCombination R x) := by
    rw [Finsupp.range_linearCombination, hspan]; trivial
  obtain ⟨f, hf⟩ := ha
  exact ⟨MonoidAlgebra.ofCoeff f, by rw [lift_eq_linearCombination]; exact hf⟩

/-- Over a local base, the characters congruent to one modulo the maximal ideal are congruent to
one modulo a nilpotent ideal. -/
theorem exists_isNilpotent_sub_one_mem [IsLocalRing R] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [Group.FG Γ]
    (hx : ∀ γ, IsGroupLikeElem R (x γ)) (hspan : Submodule.span R (Set.range x) = ⊤) :
    ∃ N : Ideal R, IsNilpotent N ∧
      ∀ κ ∈ charKer x (maximalIdeal R), x κ - 1 ∈ N.map (algebraMap R A) := by
  classical
  set K := charKer x (maximalIdeal R) with hKdef
  let ψ := MonoidAlgebra.lift R A Γ x
  have hψ : Function.Surjective ψ := lift_surjective x hspan
  obtain ⟨F, hF⟩ := ker_fg_of_finiteType ψ hψ
  let cs : MonoidAlgebra R Γ → (Γ ⧸ K →₀ R) := fun f =>
    Finsupp.mapDomain (QuotientGroup.mk : Γ → Γ ⧸ K) f.coeff
  let T : Finset R := F.biUnion fun f => (cs f).support.image (cs f)
  let N : Ideal R := Ideal.span (T : Set R)
  have hcsN : ∀ f ∈ F, ∀ c, cs f c ∈ N := by
    intro f hf c
    by_cases hc : c ∈ (cs f).support
    · exact Ideal.subset_span (Finset.mem_biUnion.2 ⟨f, hf, Finset.mem_image_of_mem _ hc⟩)
    · rw [Finsupp.notMem_support_iff.1 hc]; exact N.zero_mem
  have hNnil : IsNilpotent N := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨T, rfl⟩, Ideal.span_le]
    intro r hr
    obtain ⟨f, hf, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    have hfker : ψ f = 0 := by
      have : f ∈ RingHom.ker ψ.toRingHom := hF ▸ Ideal.subset_span hf
      exact this
    exact coeff_mem_nilradical x hx hspan f.coeff
      (by rw [← lift_eq_linearCombination]; exact hfker) c
  refine ⟨N, hNnil, ?_⟩
  let Θ : MonoidAlgebra R Γ →ₐ[R] MonoidAlgebra (R ⧸ N) (Γ ⧸ K) :=
    (MonoidAlgebra.mapAlgHom (Γ ⧸ K) (Ideal.Quotient.mkₐ R N)).comp
      (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.mk' K))
  have hΘ : ∀ f : MonoidAlgebra R Γ, ∀ c, (Θ f).coeff c = Ideal.Quotient.mk N (cs f c) := by
    intro f c
    simp [Θ, cs]
  have hle : RingHom.ker ψ.toRingHom ≤ RingHom.ker Θ.toRingHom := by
    rw [← hF, Ideal.span_le]
    intro f hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Θ f = 0
    apply MonoidAlgebra.coeff_injective
    ext c
    rw [hΘ, Ideal.Quotient.eq_zero_iff_mem.2 (hcsN f hf c)]
    rfl
  let g : A →ₐ[R] MonoidAlgebra (R ⧸ N) (Γ ⧸ K) := AlgHom.liftOfSurjective ψ hψ Θ hle
  have hg : ∀ γ, g (x γ) = MonoidAlgebra.single (QuotientGroup.mk γ) 1 := by
    intro γ
    have : x γ = ψ (MonoidAlgebra.single γ 1) := by simp [ψ]
    rw [this, AlgHom.liftOfSurjective_apply]
    simp [Θ]
  let πalg : (R ⧸ N) ⊗[R] A →ₐ[R ⧸ N] MonoidAlgebra (R ⧸ N) (Γ ⧸ K) :=
    Algebra.TensorProduct.lift (Algebra.ofId (R ⧸ N) _) g (fun _ _ => Commute.all _ _)
  let π : (R ⧸ N) ⊗[R] A →ₗ[R ⧸ N] (Γ ⧸ K →₀ R ⧸ N) :=
    (MonoidAlgebra.coeffLinearEquiv (R ⧸ N)).toLinearMap ∘ₗ πalg.toLinearMap
  let y : Γ →* (R ⧸ N) ⊗[R] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] (R ⧸ N) ⊗[R] A).toMonoidHom.comp x
  have hy : ∀ γ, y γ = (1 : R ⧸ N) ⊗ₜ[R] x γ := fun γ => rfl
  have hyspan : Submodule.span (R ⧸ N) (Set.range y) = ⊤ :=
    span_one_tmul_eq_top x (R ⧸ N) hspan
  have hπ : ∀ γ, π (y γ) = Finsupp.single (QuotientGroup.mk γ) 1 := by
    intro γ
    simp [π, πalg, hy, hg]
  have hfib : ∀ P : Ideal (R ⧸ N), P.IsPrime → ∀ κ ∈ K,
      y κ - 1 ∈ P.map (algebraMap (R ⧸ N) ((R ⧸ N) ⊗[R] A)) := by
    intro P hP κ hκ
    let q : Ideal R := P.comap (Ideal.Quotient.mk N)
    have hq : q.IsPrime := Ideal.comap_isPrime _ _
    have hκq : κ ∈ charKer x q := by
      rw [charKer_eq_maximalIdeal x hx hspan q]; exact hκ
    have h1 := one_tmul_mem_map (S := R ⧸ N) q hκq
    have h2 : q.map (algebraMap R (R ⧸ N)) ≤ P := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.map_comap_le
    have h3 := Ideal.map_mono (f := algebraMap (R ⧸ N) ((R ⧸ N) ⊗[R] A)) h2 h1
    rwa [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def] at h3
  intro κ hκ
  have h := eq_one_of_forall_isPrime y hyspan K (subgroup_fg K) π hπ hfib hκ
  rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def, ← hy, h,
    sub_self]

/-- Over a local base, representatives of the cosets of `charKer x 𝔪` span. -/
theorem span_out_eq_top [IsLocalRing R] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [Group.FG Γ]
    (hx : ∀ γ, IsGroupLikeElem R (x γ)) (hspan : Submodule.span R (Set.range x) = ⊤) :
    Submodule.span R (Set.range fun c : Γ ⧸ charKer x (maximalIdeal R) => x c.out) = ⊤ := by
  obtain ⟨N, hN, hK⟩ := exists_isNilpotent_sub_one_mem x hx hspan
  apply Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent N hN
  rw [eq_top_iff]
  refine hspan.ge.trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨γ, rfl⟩
  set c : Γ ⧸ charKer x (maximalIdeal R) := QuotientGroup.mk γ with hc
  have hmem : x γ - x c.out ∈ N • (⊤ : Submodule R A) := by
    rw [mem_smul_top_iff_mem_map]
    have hle : charKer x (maximalIdeal R) ≤ congrKer x (N.map (algebraMap R A)) :=
      fun κ hκ => hK κ hκ
    have : (QuotientGroup.mk γ : Γ ⧸ congrKer x (N.map (algebraMap R A))) =
        QuotientGroup.mk c.out := by
      rw [QuotientGroup.eq]
      apply hle
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact (congrKer_mk_eq_mk_iff x).1 this
  have e : x γ = x c.out + (x γ - x c.out) := by abel
  rw [SetLike.mem_coe, e]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨c, rfl⟩) hmem

/-- Modulo a prime, distinct cosets give linearly independent group-like elements. -/
theorem linearIndependent_one_tmul_out [Module.Flat R A] (hx : ∀ γ, IsGroupLikeElem R (x γ))
    (q : Ideal R) [q.IsPrime] :
    LinearIndependent (R ⧸ q) (fun c : Γ ⧸ charKer x q => (1 : R ⧸ q) ⊗ₜ[R] x c.out) := by
  let y : Γ ⧸ charKer x q → GroupLike (R ⧸ q) ((R ⧸ q) ⊗[R] A) := fun c =>
    ⟨(1 : R ⧸ q) ⊗ₜ[R] x c.out, isGroupLikeElem_one_tmul (R ⧸ q) (hx _)⟩
  have hy : Function.Injective y := by
    intro c d hcd
    have h : (1 : R ⧸ q) ⊗ₜ[R] x c.out = (1 : R ⧸ q) ⊗ₜ[R] x d.out :=
      congrArg GroupLike.val hcd
    rwa [← sub_eq_zero, ← TensorProduct.tmul_sub, one_tmul_eq_zero_iff, ← mk_eq_mk_iff,
      QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
  exact (linearIndep_groupLikeVal (R := R ⧸ q) (A := (R ⧸ q) ⊗[R] A)).comp y hy

/-- Over a local base, representatives of the cosets of `charKer x 𝔪` form a basis. -/
theorem exists_basis [IsLocalRing R] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [Group.FG Γ]
    (hx : ∀ γ, IsGroupLikeElem R (x γ)) (hspan : Submodule.span R (Set.range x) = ⊤) :
    ∃ b : Module.Basis (Γ ⧸ charKer x (maximalIdeal R)) R A, ∀ c, b c = x c.out := by
  have hli : LinearIndependent R (fun c : Γ ⧸ charKer x (maximalIdeal R) => x c.out) :=
    Module.IsLocalRing.linearIndependent_of_flat _
      (linearIndependent_one_tmul_out x hx (maximalIdeal R))
  exact ⟨Module.Basis.mk hli (span_out_eq_top x hx hspan).ge, fun c => Module.Basis.mk_apply _ _ _⟩

omit [CommGroup Γ] in
/-- Over a local ring, a group-like element is one of the vectors of a basis of group-like
elements. -/
theorem exists_eq_basis_of_isGroupLikeElem [IsLocalRing R] {ι : Type*} (b : Module.Basis ι R A)
    (hb : ∀ i, IsGroupLikeElem R (b i)) {g : A} (hg : IsGroupLikeElem R g) : ∃ i, g = b i := by
  classical
  set a := b.repr g with ha
  have hdiag : ∀ i, a i * a i = a i := by
    intro i
    let E : A ⊗[R] A →ₗ[R] R := LinearMap.mul' R R ∘ₗ TensorProduct.map (b.coord i) (b.coord i)
    have hL : E ∘ₗ Coalgebra.comul = b.coord i := by
      apply b.ext
      intro k
      simp only [LinearMap.comp_apply, (hb k).comul_eq_tmul_self, E, TensorProduct.map_tmul,
        LinearMap.mul'_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
      split_ifs <;> simp
    have := congrArg (fun L : A →ₗ[R] R => L g) hL
    simpa [E, hg.comul_eq_tmul_self] using this
  have hoff : ∀ i j, i ≠ j → a i * a j = 0 := by
    intro i j hij
    let E : A ⊗[R] A →ₗ[R] R := LinearMap.mul' R R ∘ₗ TensorProduct.map (b.coord i) (b.coord j)
    have hL : E ∘ₗ Coalgebra.comul = 0 := by
      apply b.ext
      intro k
      simp only [LinearMap.comp_apply, (hb k).comul_eq_tmul_self, E, TensorProduct.map_tmul,
        LinearMap.mul'_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all
    have := congrArg (fun L : A →ₗ[R] R => L g) hL
    simpa [E, hg.comul_eq_tmul_self] using this
  have hsum : (a.sum fun _ r => r) = 1 := by
    have h1 : Coalgebra.counit g = (1 : R) := hg.counit_eq_one
    rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, map_finsuppSum] at h1
    simpa [(hb _).counit_eq_one] using h1
  obtain ⟨i, hi⟩ : ∃ i, a i ∉ maximalIdeal R := by
    by_contra! h
    have : (a.sum fun _ r => r) ∈ maximalIdeal R := Ideal.sum_mem _ fun i _ => h i
    rw [hsum] at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hu : IsUnit (a i) := notMem_maximalIdeal.1 hi
  have hai : a i = 1 := hu.mul_left_cancel (by rw [hdiag, mul_one])
  refine ⟨i, b.repr.injective ?_⟩
  rw [Module.Basis.repr_self]
  ext j
  rw [Finsupp.single_apply]
  split_ifs with hij
  · subst hij; exact hai
  · have := hoff i j hij
    rwa [hai, one_mul] at this

end localRing

section main

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
  [Module.Flat R A] [Algebra.FinitePresentation R A]

/-- Over a local ring, a flat finitely presented commutative Hopf algebra spanned by its group-like
elements has linearly independent group-like elements, and they form a finitely generated
group. -/
theorem linearIndependent_and_groupFG
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    LinearIndependent R (fun g : GroupLike R A => (g : A)) ∧ Group.FG (GroupLike R A) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have hT : ∀ a : s, ∃ T : Finset A, (T : Set A) ⊆ {a : A | IsGroupLikeElem R a} ∧
      (a : A) ∈ Submodule.span R (T : Set A) := fun a =>
    Submodule.mem_span_finite_of_mem_span (hspan ▸ Submodule.mem_top)
  choose T hTgl hTmem using hT
  let U : Finset A := s.attach.biUnion T
  let S : Set (GroupLike R A) := GroupLike.val ⁻¹' (U : Set A)
  have hSfin : S.Finite := U.finite_toSet.preimage GroupLike.val_injective.injOn
  have : Finite S := hSfin.to_subtype
  let Γ : Subgroup (GroupLike R A) := Subgroup.closure S
  let x : Γ →* A := (GroupLike.valMonoidHom R A).comp Γ.subtype
  have hx : ∀ γ, IsGroupLikeElem R (x γ) := fun γ => (γ : GroupLike R A).isGroupLikeElem_val
  have hxspan : Submodule.span R (Set.range x) = ⊤ := by
    have hsub : (s : Set A) ⊆ Algebra.adjoin R (Set.range x) := by
      intro a ha
      apply Algebra.span_le_adjoin R _
      refine Submodule.span_mono ?_ (hTmem ⟨a, ha⟩)
      intro t ht
      have htU : t ∈ U := Finset.mem_biUnion.2 ⟨⟨a, ha⟩, Finset.mem_attach _ _, ht⟩
      exact ⟨⟨⟨t, hTgl ⟨a, ha⟩ ht⟩, Subgroup.subset_closure htU⟩, rfl⟩
    have htop : Algebra.adjoin R (Set.range x) = ⊤ := by
      rw [eq_top_iff, ← hs]
      exact Algebra.adjoin_le hsub
    have := congrArg Subalgebra.toSubmodule htop
    rwa [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq,
      Algebra.top_toSubmodule] at this
  obtain ⟨b, hb⟩ := exists_basis x hx hxspan
  have hgl : ∀ g : GroupLike R A, ∃ c, (g : A) = b c := fun g =>
    exists_eq_basis_of_isGroupLikeElem b (fun c => by rw [hb]; exact hx _) g.isGroupLikeElem_val
  choose f hf using hgl
  have hfinj : Function.Injective f := fun g h hgh =>
    GroupLike.val_injective (by rw [hf, hf, hgh])
  refine ⟨?_, ?_⟩
  · have e : (fun g : GroupLike R A => (g : A)) = b ∘ f := funext hf
    rw [e]
    exact b.linearIndependent.comp f hfinj
  · have hΓ : Γ = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have e : g = ((f g).out : GroupLike R A) :=
        GroupLike.val_injective (by rw [hf, hb]; rfl)
      rw [e]
      exact ((f g).out).2
    have hfg : Γ.FG := (Group.fg_iff_subgroup_fg Γ).1 inferInstance
    exact Group.fg_def.mpr (hΓ ▸ hfg)

/-- Over a local ring, the group-like elements of a flat finitely presented commutative Hopf
algebra spanned by them are linearly independent. -/
theorem linearIndependent_groupLike_of_isLocalRing
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    LinearIndependent R (fun g : GroupLike R A => (g : A)) :=
  (linearIndependent_and_groupFG hspan).1

/-- The group of group-like elements is finitely generated. -/
theorem groupFG (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    Group.FG (GroupLike R A) :=
  (linearIndependent_and_groupFG hspan).2

/-- The basis of group-like elements. -/
def basisGroupLike (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    Module.Basis (GroupLike R A) R A :=
  Module.Basis.mk (linearIndependent_groupLike_of_isLocalRing hspan) (by
    rw [← hspan]
    exact Submodule.span_mono fun a ha => ⟨⟨a, ha⟩, rfl⟩)

@[simp] theorem basisGroupLike_apply
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) (g : GroupLike R A) :
    basisGroupLike hspan g = g :=
  Module.Basis.mk_apply _ _ _

/-- A group-like element congruent to one modulo the maximal ideal equals one. -/
theorem eq_one_of_sub_one_mem (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤)
    {u : A} (hu : IsGroupLikeElem R u)
    (h : u - 1 ∈ (maximalIdeal R).map (algebraMap R A)) : u = 1 := by
  classical
  let B := basisGroupLike hspan
  let U : GroupLike R A := ⟨u, hu⟩
  have hm : B U - B 1 ∈ maximalIdeal R • (⊤ : Submodule R A) := by
    rw [mem_smul_top_iff_mem_map]
    simpa [B, U] using h
  have hc := basis_repr_mem_of_mem_smul_top B _ hm U
  by_contra hne
  have hU1 : U ≠ 1 := fun h' => hne (congrArg GroupLike.val h')
  rw [map_sub, B.repr_self, B.repr_self, Finsupp.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hU1, sub_zero] at hc
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hc)

/-- Evaluation of the group algebra on group-like elements is injective. -/
theorem liftGroupLikeBialgHom_injective
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    Function.Injective (_root_.MonoidAlgebra.liftGroupLikeBialgHom :
      _root_.MonoidAlgebra R (GroupLike R A) → A) := by
  intro f g hfg
  apply _root_.MonoidAlgebra.coeff_injective
  apply linearIndependent_groupLike_of_isLocalRing hspan
  exact (Langlands.MonoidAlgebra.liftGroupLikeBialgHom_eq_linearCombination f).symm.trans
    (hfg.trans (Langlands.MonoidAlgebra.liftGroupLikeBialgHom_eq_linearCombination g))

/-- Over a local ring, a flat finitely presented commutative Hopf algebra spanned by its group-like
elements is the group algebra of its group-like elements, as a bialgebra. -/
def bialgEquiv (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    _root_.MonoidAlgebra R (GroupLike R A) ≃ₐc[R] A :=
  BialgEquiv.ofBijective _root_.MonoidAlgebra.liftGroupLikeBialgHom
    ⟨liftGroupLikeBialgHom_injective hspan,
      Langlands.MonoidAlgebra.liftGroupLikeBialgHom_surjective hspan⟩

@[simp] theorem bialgEquiv_single (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤)
    (g : GroupLike R A) (r : R) :
    bialgEquiv hspan (_root_.MonoidAlgebra.single g r) = r • (g : A) := by
  change _root_.MonoidAlgebra.liftGroupLikeBialgHom (_root_.MonoidAlgebra.single g r) = _
  simp [_root_.MonoidAlgebra.liftGroupLikeBialgHom]

end main

end Langlands.GroupLikeSpan
