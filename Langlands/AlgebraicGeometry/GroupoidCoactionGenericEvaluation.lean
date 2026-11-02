import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantIdeal
import Langlands.AlgebraicGeometry.GroupoidCoactionCokernel
import Langlands.AlgebraicGeometry.GroupoidCoactionInduced
import Langlands.AlgebraicGeometry.GroupoidCoactionPushforward
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Support

/-! # Generic evaluation for coactions induced from a finite faithfully flat cover

Let `(B, C, t)` be an affine étale equivalence relation and `(D, P, td)` a source-cartesian cover
of it, with invariant ring `A = invariantRing td`, `D` faithfully flat over `A` and
`D ⊗[A] D ≅ P`. For a prime `q` of `A` the module `G = D ⊗[A] (A ⧸ q)` carries the pushed
forward induced coaction. For a finite module `H` with a coaction, evaluation at finitely many
elements `1 ⊗ aᵢ` gives an equivariant map `Hom_B(G, H) → Hⁿ`. Over a Noetherian reduced base
with `D` finite and `Spec D → Spec B` surjective, the elements can be chosen so that kernel and
cokernel of this evaluation are killed by a nonzero invariant ideal.
-/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

section Pi

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] {t : B →+* C}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- The coordinatewise additive coaction on a finite product. -/
def piCoactionMap (θ : GroupoidCoaction t M) : (ι → M) →+ C ⊗[B] (ι → M) where
  toFun f := ∑ i, LinearMap.lTensor C (LinearMap.single B (fun _ : ι => M) i) (θ.coaction (f i))
  map_zero' := by simp
  map_add' f g := by simp [Finset.sum_add_distrib]

lemma piCoactionMap_apply (θ : GroupoidCoaction t M) (f : ι → M) :
    piCoactionMap θ f =
      ∑ i, LinearMap.lTensor C (LinearMap.single B (fun _ : ι => M) i) (θ.coaction (f i)) :=
  rfl

lemma piCoactionMap_smul (θ : GroupoidCoaction t M) (b : B) (f : ι → M) :
    piCoactionMap θ (b • f) = t b • piCoactionMap θ f := by
  simp only [piCoactionMap_apply, Pi.smul_apply, θ.map_smul, lTensor_alg_smul, Finset.smul_sum]

lemma piCoactionMap_single (θ : GroupoidCoaction t M) (i : ι) (m : M) :
    piCoactionMap θ (LinearMap.single B (fun _ : ι => M) i m) =
      LinearMap.lTensor C (LinearMap.single B (fun _ : ι => M) i) (θ.coaction m) := by
  rw [piCoactionMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- A finite product of copies of a coaction, with the coordinatewise coaction. -/
def piCoaction (θ : GroupoidCoaction t M) : GroupoidCoaction t (ι → M) where
  coaction := piCoactionMap θ
  map_smul := piCoactionMap_smul θ
  counit T _ _ φ hφ f := by
    simp only [piCoactionMap_apply, map_sum, ← lTensor_rTensor_commute, θ.counit T φ hφ,
      LinearMap.lTensor_tmul, ← tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ f := by
    simp only [piCoactionMap_apply, map_sum, ← lTensor_rTensor_commute,
      θ.coassoc T φ₁ φ₂ φ₃ h h₃]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact coactionCompose_map θ.coaction (piCoactionMap θ) θ.map_smul (piCoactionMap_smul θ)
      (LinearMap.single B (fun _ : ι => M) i) (fun m => piCoactionMap_single θ i m) φ₁ φ₂ h _

lemma lTensor_pi_eq_sum (f : ι → N →ₗ[B] M) (x : C ⊗[B] N) :
    LinearMap.lTensor C (LinearMap.pi f) x =
      ∑ i, LinearMap.lTensor C (LinearMap.single B (fun _ : ι => M) i)
        (LinearMap.lTensor C (f i) x) := by
  induction x with
  | tmul c n =>
    simp only [LinearMap.lTensor_tmul, ← tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]

/-- A family of equivariant maps gives an equivariant map into the product coaction. -/
lemma isHom_pi (θN : GroupoidCoaction t N) (θ : GroupoidCoaction t M)
    (f : ι → N →ₗ[B] M) (hf : ∀ i, θN.IsHom θ (f i)) :
    θN.IsHom (piCoaction θ) (LinearMap.pi f) := by
  intro n
  change piCoactionMap θ (LinearMap.pi f n) = _
  rw [piCoactionMap_apply, lTensor_pi_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.pi_apply, hf i n]

end Pi

section Generic

variable {B : Type u} [CommRing B]

/-- A finite module all of whose elements are killed by elements outside a prime is killed by
one element outside it. -/
lemma exists_smul_eq_zero_of_forall {M : Type*} [AddCommGroup M] [Module B M]
    [Module.Finite B M] (p : Ideal B) [p.IsPrime] (h : ∀ m : M, ∃ c ∉ p, c • m = 0) :
    ∃ s ∉ p, ∀ m : M, s • m = 0 := by
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B M :=
    Module.notMem_support_iff'.mpr h
  rw [Module.mem_support_iff_of_finite] at hp
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp hp
  exact ⟨s, hsp, fun m => Module.mem_annihilator.mp hs m⟩

/-- Generic freeness at a minimal prime: a finite module over a reduced Noetherian ring,
generated by the values of `v`, has finitely many of these values which become a basis after
localizing at a minimal prime `p`; one `s ∉ p` kills the kernel and cokernel of the
corresponding map from the free module. -/
lemma exists_generic_basis {G : Type v} [AddCommGroup G] [Module B G] {α : Type v}
    [IsNoetherianRing B] [IsReduced B] [Module.Finite B G]
    (p : Ideal B) (hp : p ∈ minimalPrimes B) (v : α → G)
    (hv : Submodule.span B (Set.range v) = ⊤) (x₀ : α) (hx₀ : ∀ c ∉ p, c • v x₀ ≠ 0) :
    ∃ (r : ℕ) (_ : 0 < r) (a : Fin r → α) (s : B), s ∉ p ∧
      (∀ g : G, s • g ∈ LinearMap.range (Fintype.linearCombination B (v ∘ a))) ∧
      (∀ x ∈ LinearMap.ker (Fintype.linearCombination B (v ∘ a)), s • x = 0) := by
  classical
  have : p.IsPrime := hp.1.1
  let S := p.primeCompl
  let k := Localization.AtPrime p
  have : Ring.KrullDimLE 0 k := .of_isLocalization p hp k
  let _ : Field k := Ring.KrullDimLE.isField_of_isReduced.toField
  let μ := LocalizedModule.mkLinearMap S G
  let v₀ : α → LocalizedModule S G := fun x => μ (v x)
  have hspan : Submodule.span k (Set.range v₀) = ⊤ := by
    have h := span_eq_top_of_isLocalizedModule k S μ hv
    rwa [← Set.range_comp] at h
  obtain ⟨κ, a, -, hspan', hli⟩ := exists_linearIndependent' k v₀
  have : Finite κ := hli.finite_of_isNoetherian
  obtain ⟨r, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  let a' : Fin r → α := a ∘ eκ.symm
  have hli' : LinearIndependent k (v₀ ∘ a') := hli.comp eκ.symm eκ.symm.injective
  have hspan'' : Submodule.span k (Set.range (v₀ ∘ a')) = ⊤ := by
    rw [show v₀ ∘ a' = (v₀ ∘ a) ∘ eκ.symm from rfl, eκ.symm.surjective.range_comp, hspan', hspan]
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exfalso
      have hbot : (⊤ : Submodule k (LocalizedModule S G)) = ⊥ := by
        rw [← hspan'', Set.range_eq_empty, Submodule.span_empty]
      have h0 : v₀ x₀ = 0 := by
        rw [← Submodule.mem_bot k, ← hbot]
        exact Submodule.mem_top
      obtain ⟨c, hc, hc0⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp (LinearMap.mem_ker.mpr h0)
      exact hx₀ c hc hc0
    · exact hr
  let φ := Fintype.linearCombination B (v ∘ a')
  -- kernel: every element is killed by an element outside `p`
  have hker : ∀ x : LinearMap.ker φ, ∃ c ∉ p, c • x = 0 := by
    rintro ⟨x, hx⟩
    have h1 : ∑ i, algebraMap B k (x i) • (v₀ ∘ a') i = 0 := by
      have := congrArg μ (LinearMap.mem_ker.mp hx)
      simpa [φ, Fintype.linearCombination_apply, map_sum, algebraMap_smul, v₀] using this
    have h2 := Fintype.linearIndependent_iff.mp hli' _ h1
    choose c hc using fun i => (IsLocalization.map_eq_zero_iff S k (x i)).mp (h2 i)
    refine ⟨∏ i, (c i : B), ?_, ?_⟩
    · rw [← Submonoid.coe_finsetProd]
      exact (∏ i, c i).property
    · apply Subtype.ext
      funext i
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun j => (c j : B)) (Finset.mem_univ i)
      change (∏ j, (c j : B)) * x i = 0
      rw [hd, mul_comm (c i : B) d, mul_assoc, hc i, mul_zero]
  -- cokernel: the localized map is surjective
  have hsurjloc : Function.Surjective (LocalizedModule.map S φ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan'', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨LocalizedModule.mk (Pi.single i 1) 1, ?_⟩
    simp [φ, v₀, μ, LocalizedModule.map_mk, Fintype.linearCombination_apply_single,
      LocalizedModule.mkLinearMap_apply]
  have hcok : ∀ y : G ⧸ LinearMap.range φ, ∃ c ∉ p, c • y = 0 := by
    intro y
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, hz⟩ := hsurjloc (LocalizedModule.mk g 1)
    induction z using LocalizedModule.induction_on with
    | h x c =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hz
      obtain ⟨w, hw⟩ := hz
      refine ⟨(w : B) * c, (w * c).property, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨(w : B) • x, ?_⟩
      rw [_root_.map_smul, mul_smul]
      simpa [Submonoid.smul_def] using hw
  obtain ⟨s₁, hs₁p, hs₁⟩ := exists_smul_eq_zero_of_forall (M := LinearMap.ker φ) p hker
  obtain ⟨s₂, hs₂p, hs₂⟩ := exists_smul_eq_zero_of_forall (M := G ⧸ LinearMap.range φ) p hcok
  refine ⟨r, hr, a', s₁ * s₂, ?_, ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
    · exact hs₁p h
    · exact hs₂p h
  · intro g
    have hg : s₂ • g ∈ LinearMap.range φ := by
      have := hs₂ (Submodule.Quotient.mk g)
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    rw [mul_smul]
    exact Submodule.smul_mem _ s₁ hg
  · intro x hx
    have := congrArg Subtype.val (hs₁ ⟨x, hx⟩)
    simp only [Submodule.coe_smul, ZeroMemClass.coe_zero] at this
    rw [mul_comm, mul_smul, this, smul_zero]

/-- Evaluation of linear maps at a family `g` whose span has cokernel killed by `s` and whose
relations are killed by `s` has kernel killed by `s` and cokernel killed by `s * s`. -/
lemma evaluation_annihilators {G H : Type v} [AddCommGroup G] [Module B G]
    [AddCommGroup H] [Module B H] {r : ℕ} (g : Fin r → G) (s : B)
    (hK : ∀ y : G, s • y ∈ LinearMap.range (Fintype.linearCombination B g))
    (hL : ∀ x ∈ LinearMap.ker (Fintype.linearCombination B g), s • x = 0) :
    s ∈ Module.annihilator B
        (LinearMap.ker (LinearMap.pi fun i => LinearMap.applyₗ (R := B) (M₂ := H) (g i))) ∧
      s * s ∈ Module.annihilator B ((Fin r → H) ⧸
        LinearMap.range (LinearMap.pi fun i => LinearMap.applyₗ (R := B) (M₂ := H) (g i))) := by
  classical
  let φ := Fintype.linearCombination B g
  let Ev := LinearMap.pi fun i => LinearMap.applyₗ (R := B) (M₂ := H) (g i)
  constructor
  · rw [Module.mem_annihilator]
    rintro ⟨ψ, hψ⟩
    apply Subtype.ext
    have hψi : ∀ i, ψ (g i) = 0 := fun i => by
      simpa [Ev] using congrFun (LinearMap.mem_ker.mp hψ) i
    change s • ψ = 0
    ext y
    obtain ⟨x, hx⟩ := hK y
    rw [LinearMap.smul_apply, ← _root_.map_smul, ← hx]
    simp [Fintype.linearCombination_apply, hψi]
  · rw [Module.mem_annihilator]
    intro y
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    let η := Fintype.linearCombination B h
    have hle : LinearMap.ker φ ≤ LinearMap.ker (s • η) := fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.smul_apply, ← _root_.map_smul, hL x hx, map_zero]
    let ψ₀ : LinearMap.range φ →ₗ[B] H :=
      ((LinearMap.ker φ).liftQ (s • η) hle).comp φ.quotKerEquivRange.symm.toLinearMap
    let ψ : G →ₗ[B] H :=
      ψ₀.comp ((s • (LinearMap.id : G →ₗ[B] G)).codRestrict (LinearMap.range φ) hK)
    have hval : ∀ i, ψ (g i) = (s * s) • h i := by
      intro i
      have hmem : (⟨s • g i, hK (g i)⟩ : LinearMap.range φ) =
          ⟨φ (s • Pi.single i 1), LinearMap.mem_range_self φ _⟩ := by
        apply Subtype.ext
        simp [φ, Fintype.linearCombination_apply_single]
      change ψ₀ ⟨s • g i, hK (g i)⟩ = _
      rw [hmem]
      change (LinearMap.ker φ).liftQ (s • η) hle
        (φ.quotKerEquivRange.symm ⟨φ (s • Pi.single i 1), _⟩) = _
      rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
        Submodule.liftQ_apply]
      simp [η, Fintype.linearCombination_apply_single, mul_smul]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨ψ, ?_⟩
    funext i
    simp [hval]

/-- Linear maps between finite modules over a Noetherian ring form a finite module. -/
lemma finite_linearMap_of_isNoetherianRing [IsNoetherianRing B] {G H : Type v}
    [AddCommGroup G] [Module B G] [AddCommGroup H] [Module B H]
    [Module.Finite B G] [Module.Finite B H] : Module.Finite B (G →ₗ[B] H) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B G
  refine Module.Finite.of_injective (LinearMap.lcomp B H π) fun f₁ f₂ hf => ?_
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  exact LinearMap.congr_fun hf y

end Generic

section Cover

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
variable {t : B →+* C} {td : D →+* P}

/-- On a source-cartesian cover by a faithfully flat effective relation, the covering ring is
spanned over its invariant ring by the image of the base ring. -/
lemma span_range_algebraMap_eq_top (hE : RingEtaleEquivalenceRelation t)
    (e : P ≃ₐ[D] D ⊗[B] C) (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
    [Module.FaithfullyFlat (invariantRing td) D]
    (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
    (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d) :
    Submodule.span (invariantRing td) (Set.range (algebraMap B D)) = ⊤ := by
  set S₀ := Submodule.span (invariantRing td) (Set.range (algebraMap B D))
  let ψ : D ⊗[invariantRing td] D →ₗ[D] D ⊗[invariantRing td] (D ⧸ S₀) :=
    AlgebraTensorModule.lTensor D D S₀.mkQ
  let Φ : D ⊗[B] C →ₗ[D] D ⊗[invariantRing td] (D ⧸ S₀) :=
    ψ ∘ₗ ε.toLinearMap ∘ₗ e.symm.toLinearMap
  have hC : Submodule.span B (Set.range t) = ⊤ := by
    have h := congrArg Subalgebra.toSubmodule hE.adjoin_range_eq_top
    rw [Algebra.adjoin_eq_span_of_subset, Algebra.top_toSubmodule] at h
    · exact h
    · refine fun x hx => Submodule.subset_span ?_
      have hle : Submonoid.closure (Set.range t) ≤ MonoidHom.mrange (t : B →* C) :=
        Submonoid.closure_le.mpr (by rintro _ ⟨b, rfl⟩; exact ⟨b, rfl⟩)
      obtain ⟨b, hb⟩ := MonoidHom.mem_mrange.mp (hle hx)
      exact ⟨b, hb⟩
  have h₁ : ∀ c : C, Φ ((1 : D) ⊗ₜ[B] c) = 0 := by
    intro c
    have hc : c ∈ Submodule.span B (Set.range t) := hC ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have h₂ : e.symm ((1 : D) ⊗ₜ[B] t b) = td (algebraMap B D b) := by
        rw [← cartesianBaseMap_apply]
        exact RingHom.congr_fun ht b
      have h₃ : S₀.mkQ (algebraMap B D b) = 0 :=
        (Submodule.Quotient.mk_eq_zero S₀).mpr (Submodule.subset_span ⟨b, rfl⟩)
      simp only [Φ, ψ, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, h₂, hε,
        AlgebraTensorModule.lTensor_tmul, h₃, tmul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add, map_add, hx, hy, add_zero]
    | smul b x _ hx =>
      rw [tmul_smul, ← algebraMap_smul D b, LinearMap.map_smul, hx, smul_zero]
  have hΦ : ∀ x, Φ x = 0 := by
    intro x
    induction x with
    | tmul d c =>
      have h : d ⊗ₜ[B] c = d • ((1 : D) ⊗ₜ[B] c) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [h, LinearMap.map_smul, h₁, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have hψ : ∀ y, ψ y = 0 := by
    intro y
    simpa [Φ] using hΦ (e (ε.symm y))
  have hsub : ∀ x : D ⊗[invariantRing td] (D ⧸ S₀), x = 0 := by
    intro x
    induction x with
    | tmul d z =>
      obtain ⟨d', rfl⟩ := S₀.mkQ_surjective z
      simpa [ψ] using hψ (d ⊗ₜ d')
    | add x y hx hy => rw [hx, hy, add_zero]
  have : Subsingleton (D ⊗[invariantRing td] (D ⧸ S₀)) :=
    ⟨fun x y => by rw [hsub x, hsub y]⟩
  have := Module.FaithfullyFlat.lTensor_reflects_triviality (invariantRing td) D (D ⧸ S₀)
  exact Submodule.Quotient.subsingleton_iff.mp inferInstance

/-- If the covering ring is spanned over the invariant ring by the base ring, then an extended
module is spanned over the base ring by the elements `1 ⊗ n`. -/
lemma span_range_one_tmul_eq_top
    (hspan : Submodule.span (invariantRing td) (Set.range (algebraMap B D)) = ⊤)
    (N : Type u) [AddCommGroup N] [Module (invariantRing td) N] :
    Submodule.span B (Set.range fun n : N => (1 : D) ⊗ₜ[invariantRing td] n) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x with
  | add x y hx hy => exact add_mem hx hy
  | tmul d n =>
    have hd : d ∈ Submodule.span (invariantRing td) (Set.range (algebraMap B D)) :=
      hspan ▸ Submodule.mem_top
    induction hd using Submodule.span_induction generalizing n with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have h : (algebraMap B D b) ⊗ₜ[invariantRing td] n =
          b • ((1 : D) ⊗ₜ[invariantRing td] n) := by
        rw [smul_tmul', Algebra.smul_def, mul_one]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_tmul]
      exact add_mem (hx n) (hy n)
    | smul a x _ hx =>
      rw [smul_tmul]
      exact hx (a • n)

/-- The extension of a quotient of the invariant ring is finite over the base ring when the
covering ring is. -/
lemma finite_tensor_quotient [Module.Finite B D] (q : Ideal (invariantRing td)) :
    Module.Finite B (D ⊗[invariantRing td] (invariantRing td ⧸ q)) := by
  let f : D →ₗ[B] D ⊗[invariantRing td] (invariantRing td ⧸ q) :=
    { toFun := fun d => d ⊗ₜ 1
      map_add' := fun x y => add_tmul x y 1
      map_smul' := fun b d => (smul_tmul' b d 1).symm }
  refine Module.Finite.of_surjective f fun x => ?_
  induction x with
  | tmul d z =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨a • d, ?_⟩
    change (a • d) ⊗ₜ[invariantRing td] (1 : invariantRing td ⧸ q) = _
    rw [smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add f x' y'⟩

end Cover

section Evaluation

variable (B : Type u) {D P : Type u} [CommRing B] [CommRing D] [CommRing P]
  [Algebra B D] [Algebra D P]

/-- Evaluation of `B`-linear maps `D ⊗[A] (A ⧸ q) → H` at the elements `1 ⊗ aᵢ`, where
`A = invariantRing td` is the invariant ring of the covering relation. -/
noncomputable def genericEvaluation (td : D →+* P) (q : Ideal (invariantRing td)) {r : ℕ}
    (a : Fin r → invariantRing td ⧸ q) (H : Type u) [AddCommGroup H] [Module B H] :
    ((D ⊗[invariantRing td] (invariantRing td ⧸ q)) →ₗ[B] H) →ₗ[B] (Fin r → H) :=
  LinearMap.pi fun i => LinearMap.applyₗ (R := B) (M₂ := H) ((1 : D) ⊗ₜ[invariantRing td] a i)

@[simp]
lemma genericEvaluation_apply (td : D →+* P) (q : Ideal (invariantRing td)) {r : ℕ}
    (a : Fin r → invariantRing td ⧸ q) (H : Type u) [AddCommGroup H] [Module B H]
    (ψ : (D ⊗[invariantRing td] (invariantRing td ⧸ q)) →ₗ[B] H) (i : Fin r) :
    genericEvaluation B td q a H ψ i = ψ ((1 : D) ⊗ₜ[invariantRing td] a i) :=
  rfl

end Evaluation

section Main

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P] [Algebra B P] [IsScalarTower B D P]
variable {t : B →+* C} {td : D →+* P}

/-- The elements `1 ⊗ a` of the pushed forward induced module are invariant. -/
lemma pushforward_induced_one_tmul_mem_invariants (hE : RingEtaleEquivalenceRelation t)
    (hP : RingEtaleEquivalenceRelation td) (e : P ≃ₐ[D] D ⊗[B] C)
    (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
    (N : Type u) [AddCommGroup N] [Module (invariantRing td) N] (n : N) :
    (1 : D) ⊗ₜ[invariantRing td] n ∈ (pushforward e ht (induced td N) hE hP).invariants := by
  change pushforwardTensorEquiv e ((induced td N).coaction ((1 : D) ⊗ₜ n)) =
    (1 : C) ⊗ₜ[B] ((1 : D) ⊗ₜ[invariantRing td] n)
  rw [show (induced td N).coaction ((1 : D) ⊗ₜ n) = (1 : P) ⊗ₜ[D] ((1 : D) ⊗ₜ n) from
      induced_one_tmul_mem_invariants td N n,
    ← map_one (cartesianBaseMap e), pushforwardTensorEquiv_base_tmul]

/-- Generic evaluation (ring form of a generic step for the proof of Stacks Lemma 69.17.3,
Tag 07VP). Over a Noetherian reduced nonzero base `B`, let `D` be finite over `B` with
`Spec D → Spec B` surjective, carrying a source-cartesian relation `P` with invariant ring
`A`, `D` faithfully flat over `A` and `P ≅ D ⊗[A] D`. For every finite module `H` with a
coaction there are a prime `q` of `A`, elements `a₁, …, a_r` (`r > 0`) of `A ⧸ q`, and a
nonzero invariant ideal `I` such that `G = D ⊗[A] (A ⧸ q)` is finite over `B` and the kernel
and cokernel of evaluation `Hom_B(G, H) → H^r` at the `1 ⊗ aᵢ` are supported in `V(I)`. -/
theorem exists_genericEvaluation (hE : RingEtaleEquivalenceRelation t)
    (hP : RingEtaleEquivalenceRelation td) (e : P ≃ₐ[D] D ⊗[B] C)
    (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
    [Module.FaithfullyFlat (invariantRing td) D]
    (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
    (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d)
    [IsNoetherianRing B] [IsReduced B] [Nontrivial B] [Module.Finite B D]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B D)))
    (H : Type u) [AddCommGroup H] [Module B H] [Module.Finite B H]
    (θH : GroupoidCoaction t H) :
    ∃ (q : Ideal (invariantRing td)) (_ : q.IsPrime) (r : ℕ) (_ : 0 < r)
      (a : Fin r → invariantRing td ⧸ q) (I : Ideal B),
      I ≠ ⊥ ∧ IsInvariantIdeal t I ∧
      Module.Finite B (D ⊗[invariantRing td] (invariantRing td ⧸ q)) ∧
      I ≤ (Module.annihilator B (LinearMap.ker (genericEvaluation B td q a H))).radical ∧
      I ≤ (Module.annihilator B
        ((Fin r → H) ⧸ LinearMap.range (genericEvaluation B td q a H))).radical := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal B) ≤ m)
  have : p.IsPrime := hp.1.1
  obtain ⟨Q, hQ⟩ := hsurj ⟨p, inferInstance⟩
  have hQp : Q.asIdeal.comap (algebraMap B D) = p := congrArg PrimeSpectrum.asIdeal hQ
  let q : Ideal (invariantRing td) := Q.asIdeal.comap (algebraMap (invariantRing td) D)
  let G := D ⊗[invariantRing td] (invariantRing td ⧸ q)
  have hspanG := span_range_one_tmul_eq_top
    (span_range_algebraMap_eq_top hE e ht ε hε) (invariantRing td ⧸ q)
  have hGfin : Module.Finite B G := finite_tensor_quotient q
  have hx₀ : ∀ c ∉ p, c • ((1 : D) ⊗ₜ[invariantRing td] (1 : invariantRing td ⧸ q)) ≠ 0 := by
    intro c hc h0
    let ρ : G →ₐ[invariantRing td] D ⧸ Q.asIdeal :=
      Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (invariantRing td) Q.asIdeal)
        (Ideal.quotientMapₐ Q.asIdeal (Algebra.ofId (invariantRing td) D) fun x hx => hx)
        (fun _ _ => Commute.all _ _)
    have h₁ : ρ (c • ((1 : D) ⊗ₜ[invariantRing td] (1 : invariantRing td ⧸ q))) =
        Ideal.Quotient.mk Q.asIdeal (algebraMap B D c) := by
      rw [smul_tmul', Algebra.TensorProduct.lift_tmul, map_one, mul_one,
        Algebra.smul_def, mul_one]
      rfl
    rw [h0, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h₁
    exact hc (hQp ▸ h₁)
  obtain ⟨r, hr, a, s, hsp, hK, hL⟩ := exists_generic_basis p hp
    (fun x : invariantRing td ⧸ q => (1 : D) ⊗ₜ[invariantRing td] x) hspanG 1 hx₀
  obtain ⟨hs₁, hs₂⟩ := evaluation_annihilators (H := H)
    ((fun x : invariantRing td ⧸ q => (1 : D) ⊗ₜ[invariantRing td] x) ∘ a) s hK hL
  have : Module.FinitePresentation B G := Module.finitePresentation_of_finite B G
  let θG := pushforward e ht (induced td (invariantRing td ⧸ q)) hE hP
  let θhom := hom hE θG θH
  let Ev := genericEvaluation B td q a H
  have hEv : θhom.IsHom (piCoaction θH) Ev :=
    isHom_pi θhom θH _ fun i => hom_eval_isHom hE θG θH _
      (pushforward_induced_one_tmul_mem_invariants hE hP e ht _ (a i))
  have : Module.Finite B (G →ₗ[B] H) := finite_linearMap_of_isNoetherianRing
  have : Module.FinitePresentation B (LinearMap.ker Ev) :=
    Module.finitePresentation_of_finite B _
  have : Module.FinitePresentation B ((Fin r → H) ⧸ LinearMap.range Ev) :=
    Module.finitePresentation_of_finite B _
  have hI₁ := annihilator_isInvariantIdeal hE (kernel hE θhom (piCoaction θH) Ev hEv)
  have hI₂ := annihilator_isInvariantIdeal hE (cokernel θhom (piCoaction θH) Ev hEv)
  refine ⟨q, inferInstance, r, hr, a,
    Module.annihilator B (LinearMap.ker Ev) *
      Module.annihilator B ((Fin r → H) ⧸ LinearMap.range Ev), ?_, hI₁.mul hI₂, hGfin,
    Ideal.mul_le_left.trans Ideal.le_radical, Ideal.mul_le_right.trans Ideal.le_radical⟩
  intro hbot
  have hmem : s * (s * s) ∈ Module.annihilator B (LinearMap.ker Ev) *
      Module.annihilator B ((Fin r → H) ⧸ LinearMap.range Ev) := Ideal.mul_mem_mul hs₁ hs₂
  rw [hbot, Ideal.mem_bot] at hmem
  have h0 : s * (s * s) ∈ p := hmem ▸ p.zero_mem
  rcases Ideal.IsPrime.mem_or_mem inferInstance h0 with h | h
  · exact hsp h
  · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h <;> exact hsp h

end Main

end Langlands.AlgebraicGeometry.GroupoidCoaction
