import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Open chart loci and field-valued coverage of the quotient Grassmannian

Adapted from the Anthropic FLT source at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the solutions
P2M/Sol/S_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top.lean and
P2M/Sol/S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset.lean.
The original distribution is licensed under Apache 2.0; see
licenses/Anthropic-FLT/LICENSE, NOTICE and ATTRIBUTION.md.
The paired Markdown records the source comparisons and Mathlib reuse.
-/

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace Module.Grassmannian.FieldCover

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ}
variable {ι : Type} (g : ι → M)
variable {K : Type} [Field K] [Algebra R K]

lemma span_mkQ_tmul_eq_top (hg : Submodule.span R (Set.range g) = ⊤) (N : Submodule K (K ⊗[R] M)) :
    Submodule.span K (Set.range fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = ⊤ := by
  have h1 : Submodule.span K (Set.range fun t => (1 : K) ⊗ₜ[R] g t) = ⊤ := by
    have := Submodule.baseChange_span (R := R) (A := K) (M := M) (Set.range g)
    rw [hg, Submodule.baseChange_top] at this
    rw [this, ← Set.range_comp]
    rfl
  have h2 : Set.range (fun t => N.mkQ ((1 : K) ⊗ₜ[R] g t)) = N.mkQ '' Set.range fun t => (1 : K) ⊗ₜ[R] g t := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]

lemma finrank_quotient_eq (N : Module.Grassmannian K (K ⊗[R] M) k) :
    Module.finrank K ((K ⊗[R] M) ⧸ N.toSubmodule) = k := by
  have h := N.rankAtStalk_eq ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact_mod_cast h

theorem cover (hg : Submodule.span R (Set.range g) = ⊤) (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) := by
  classical
  set w : ι → (K ⊗[R] M) ⧸ N.toSubmodule := fun t => N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g t) with hw
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  rw [span_mkQ_tmul_eq_top g hg] at hsp

  let b : Module.Basis κ K ((K ⊗[R] M) ⧸ N.toSubmodule) := Module.Basis.mk hli (by rw [hsp])
  have : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← finrank_quotient_eq N, Module.finrank_eq_card_basis b]
  let e : κ ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin k) K ((K ⊗[R] M) ⧸ N.toSubmodule) := b.reindex e
  have hb' : ∀ i, b' i = w (a (e.symm i)) := fun i => by
    simp [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  refine ⟨fun i => a (e.symm i), ha.comp e.symm.injective, ?_⟩
  have hfun : (fun v : Fin k → K => ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (a (e.symm i)))) =
      b'.equivFun.symm := by
    funext v
    rw [Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hb']
  rw [hfun]
  exact b'.equivFun.symm.bijective

end Module.Grassmannian.FieldCover

theorem Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (K : Type) [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) :=
  Module.Grassmannian.FieldCover.cover g hg N

namespace Module.Grassmannian.ChartOpenLocus

lemma bijective_of_surjective_of_rankAtStalk (B P : Type) [CommRing B] [AddCommGroup P] [Module B P]
    [Module.Finite B P] [Module.Projective B P] (k : ℕ) (hk : ∀ p, Module.rankAtStalk (R := B) P p = k)
    (g : (Fin k → B) →ₗ[B] P) (hg : Function.Surjective g) : Function.Bijective g := by
  apply Module.bijective_of_surjective_of_rankAtStalk_eq hg
  intro m _
  have : Nontrivial B := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact IsEmpty.false (⟨m, inferInstance⟩ : PrimeSpectrum B)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun, hk]
  rfl

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable {A : Type} [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k)

abbrev Q : Type := (A ⊗[R] M) ⧸ N.toSubmodule

def q0 (i : Fin k) : Q R N := N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)

def W : Submodule A (Q R N) := Submodule.span A (Set.range (q0 R x N))

abbrev K : Type := Q R N ⧸ W R x N

def U : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.zeroLocus (Module.annihilator A (K R x N) : Set A))ᶜ

lemma isOpen_U : IsOpen (U R x N) := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

lemma mem_U {p : PrimeSpectrum A} : p ∈ U R x N ↔ ¬ Module.annihilator A (K R x N) ≤ p.asIdeal := by
  simp [U, PrimeSpectrum.mem_zeroLocus]

section baseChange

variable (B : Type) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

omit [Algebra R B] [IsScalarTower R A B] in

lemma span_tmul_eq_top_iff :
    Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ ↔
      Subsingleton (B ⊗[A] K R x N) := by
  have hexact := lTensor_exact B (LinearMap.exact_subtype_mkQ (W R x N)) (Submodule.mkQ_surjective _)
  have hsurj := LinearMap.lTensor_surjective B (Submodule.mkQ_surjective (W R x N))
  have hrange : LinearMap.range (LinearMap.lTensor B (W R x N).subtype) =
      (Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i)).restrictScalars A := by
    have h1 : LinearMap.range (LinearMap.lTensor B (W R x N).subtype) =
        ((W R x N).baseChange B).restrictScalars A := by
      ext z
      simp only [Submodule.baseChange, LinearMap.mem_range, Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]⟩
    rw [h1, W, Submodule.baseChange_span, ← Set.range_comp]
    rfl
  constructor
  · intro htop
    have hzero : ∀ z, LinearMap.lTensor B (W R x N).mkQ z = 0 := fun z => by
      have hz : z ∈ LinearMap.range (LinearMap.lTensor B (W R x N).subtype) := by
        rw [hrange, htop]; trivial
      exact (hexact z).mpr (LinearMap.mem_range.mp hz)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    rw [hzero, hzero]
  · intro hsub
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ LinearMap.range (LinearMap.lTensor B (W R x N).subtype) :=
      LinearMap.mem_range.mpr ((hexact z).mp (Subsingleton.elim _ _))
    rw [hrange] at hz
    exact hz

omit [Algebra R B] [IsScalarTower R A B] in

lemma subsingleton_iff_forall_mem_U :
    Subsingleton (B ⊗[A] K R x N) ↔
      ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap A B) q ∈ U R x N := by
  constructor
  · intro hs q
    rw [mem_U]
    intro hle
    set p := PrimeSpectrum.comap (algebraMap A B) q with hp_def
    have hp : p ∈ Module.support A (K R x N) := Module.mem_support_iff_of_finite.mpr hle
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
    let L := q.asIdeal.ResidueField
    have h1 : p.asIdeal ≤ RingHom.ker (Algebra.ofId A L) := fun a ha => by
      rw [RingHom.mem_ker]
      change algebraMap B L (algebraMap A B a) = 0
      rw [Ideal.algebraMap_residueField_eq_zero]
      exact ha
    have h2 : p.asIdeal.primeCompl ≤ (IsUnit.submonoid L).comap (Algebra.ofId A L) := fun a ha => by
      change IsUnit (algebraMap B L (algebraMap A B a))
      rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
      exact ha
    let τ : p.asIdeal.ResidueField →ₐ[A] L := Ideal.ResidueField.liftₐ p.asIdeal (Algebra.ofId A L) h1 h2
    let : Algebra p.asIdeal.ResidueField L := τ.toRingHom.toAlgebra
    have : IsScalarTower A p.asIdeal.ResidueField L :=
      IsScalarTower.of_algebraMap_eq fun a => (τ.commutes a).symm
    have : Nontrivial (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N)) :=
      inferInstance
    have e1 := AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField L L (K R x N)
    have e2 := AlgebraTensorModule.cancelBaseChange A B L L (K R x N)
    have : Subsingleton (L ⊗[B] (B ⊗[A] K R x N)) := inferInstance
    have : Subsingleton (L ⊗[A] K R x N) := e2.symm.toEquiv.subsingleton
    have : Subsingleton (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N)) :=
      e1.toEquiv.subsingleton
    exact false_of_nontrivial_of_subsingleton
      (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N))
  · intro h
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have hJ : Module.annihilator B (B ⊗[A] K R x N) ≠ ⊤ := by
      rw [Ne, Module.annihilator_eq_top_iff, ← not_nontrivial_iff_subsingleton]
      exact fun h' => h' hnt
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
    have := h ⟨m, hm.isPrime⟩
    rw [mem_U] at this
    apply this
    intro a ha
    change algebraMap A B a ∈ m
    apply hJm
    rw [Module.mem_annihilator]
    intro z
    rw [algebraMap_smul]
    induction z using TensorProduct.inductionOn with
    | tmul b y => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Module.mem_annihilator.mp ha y,
        tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]

lemma exists_equiv (f : A →ₐ[R] B) (hf : ∀ a, algebraMap A B a = f a) :
    ∃ e : ((B ⊗[R] M) ⧸ (Module.Grassmannian.map f N).toSubmodule) ≃ₗ[B] B ⊗[A] Q R N,
      ∀ i, e ((Module.Grassmannian.map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) =
        (1 : B) ⊗ₜ[A] q0 R x N i := by
  have h : (Module.Grassmannian.map f N).toSubmodule =
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) := by
    have h' : ‹Algebra A B› = f.toAlgebra := Algebra.algebra_ext _ _ fun a => by rw [hf]; rfl
    subst h'
    exact Module.Grassmannian.map_toSubmodule f N
  refine ⟨Submodule.quotEquivOfEq _ _ h ≪≫ₗ Module.Grassmannian.baseChangeMkQEquiv N.toSubmodule,
    fun i => ?_⟩
  rw [LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    Module.Grassmannian.baseChangeMkQEquiv,
    LinearMap.quotKerEquivOfSurjective_apply_mk, Module.Grassmannian.baseChangeMkQ,
    LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul]
  rfl

lemma bijective_iff (f : A →ₐ[R] B) (hf : ∀ a, algebraMap A B a = f a) :
    (Function.Bijective fun v : Fin k → B =>
        ∑ i, v i • (Module.Grassmannian.map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
      Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ := by
  obtain ⟨e, he⟩ := exists_equiv R x N B f hf
  let N' := Module.Grassmannian.map f N
  let c : (Fin k → B) →ₗ[B] (B ⊗[R] M) ⧸ N'.toSubmodule :=
    Fintype.linearCombination B fun i => N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)
  have hc : ⇑c = fun v : Fin k → B => ∑ i, v i • N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i) := rfl
  rw [← hc]
  have hr : (e : _ → _) '' Set.range (fun i => N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) =
      Set.range (fun i => (1 : B) ⊗ₜ[A] q0 R x N i) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact he i
  have hspan : Function.Surjective c ↔
      Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination,
      ← map_eq_top_iff (Submodule.orderIsoMapComap e), Submodule.orderIsoMapComap_apply,
      Submodule.map_span, ← hr]
    rfl
  constructor
  · exact fun hb => hspan.mp hb.2
  · intro htop
    exact bijective_of_surjective_of_rankAtStalk B _ k N'.rankAtStalk_eq c (hspan.mpr htop)

end baseChange

end Module.Grassmannian.ChartOpenLocus

open Module.Grassmannian.ChartOpenLocus in
theorem Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M)
    (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        (Function.Bijective fun v : Fin k → B =>
            ∑ i, v i • (Module.Grassmannian.map φ N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
          Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := by
  refine ⟨U R x N, isOpen_U R x N, fun B _ _ φ => ?_⟩
  let : Algebra A B := φ.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Set.range_subset_iff, show φ.toRingHom = algebraMap A B from rfl,
    ← subsingleton_iff_forall_mem_U R x N B, ← span_tmul_eq_top_iff R x N B,
    bijective_iff R x N B φ (fun _ => rfl)]
