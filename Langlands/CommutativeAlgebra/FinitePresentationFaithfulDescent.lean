import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Faithfully flat descent, localization spreading and presentations of modules -/

universe u v w

open TensorProduct

namespace Langlands.CommutativeAlgebra

section Descent

variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- Finite presentation of a module descends along a faithfully flat ring map. -/
theorem finitePresentation_of_finitePresentation_tensorProduct
    [Module.FaithfullyFlat R S] [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let K := LinearMap.ker π
  let πS : S ⊗[R] (Fin n → R) →ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S S π
  let ιS : S ⊗[R] K →ₗ[S] S ⊗[R] (Fin n → R) :=
    TensorProduct.AlgebraTensorModule.lTensor S S K.subtype
  have hπS : Function.Surjective πS := LinearMap.lTensor_surjective S hπ
  have hιS : Function.Injective ιS :=
    Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
  have hex : Function.Exact ιS πS :=
    lTensor_exact S (LinearMap.exact_subtype_ker_map π) hπ
  have hker : (LinearMap.ker πS).FG := Module.FinitePresentation.fg_ker πS hπS
  have hrange : LinearMap.range ιS = LinearMap.ker πS := by
    ext z
    exact (hex z).symm
  let e : S ⊗[R] K ≃ₗ[S] LinearMap.ker πS :=
    (LinearEquiv.ofInjective ιS hιS).trans (LinearEquiv.ofEq _ _ hrange)
  have : Module.Finite S (LinearMap.ker πS) := Module.Finite.iff_fg.mpr hker
  have : Module.Finite S (S ⊗[R] K) := Module.Finite.equiv e.symm
  have : Module.Finite R K := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.finitePresentation_of_surjective π hπ (Module.Finite.iff_fg.mp this)

end Descent

section Spreading

variable {R : Type u} [CommRing R] {A : Type v} {B : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- If a linear map becomes bijective after inverting `g`, it is bijective at every
prime not containing `g`, for any choice of localizations at that prime. -/
theorem bijective_map_of_bijective_away (l : A →ₗ[R] B) (g : R)
    (hg : Function.Bijective (LocalizedModule.map (Submonoid.powers g) l))
    (p : Ideal R) [p.IsPrime] (hp : g ∉ p)
    {Ap : Type*} {Bp : Type*} [AddCommGroup Ap] [Module R Ap] [AddCommGroup Bp] [Module R Bp]
    (fA : A →ₗ[R] Ap) (fB : B →ₗ[R] Bp)
    [IsLocalizedModule p.primeCompl fA] [IsLocalizedModule p.primeCompl fB] :
    Function.Bijective (IsLocalizedModule.map p.primeCompl fA fB l) := by
  have hgS : ∀ k : ℕ, g ^ k ∈ p.primeCompl := fun k => p.primeCompl.pow_mem hp k
  have hpow : ∀ t ∈ Submonoid.powers g, t ∈ p.primeCompl := by
    rintro t ⟨k, rfl⟩
    exact hgS k
  -- Consequences of bijectivity away from `g`.
  have hinj : ∀ a : A, l a = 0 → ∃ t ∈ Submonoid.powers g, t • a = 0 := by
    intro a ha
    have h0 : LocalizedModule.map (Submonoid.powers g) l (LocalizedModule.mk a 1) = 0 := by
      rw [LocalizedModule.map_mk, ha, LocalizedModule.zero_mk]
    have h1 : LocalizedModule.mk a (1 : Submonoid.powers g) = 0 :=
      hg.1 (h0.trans (map_zero _).symm)
    rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g), LocalizedModule.mk_eq] at h1
    obtain ⟨t, ht⟩ := h1
    exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩
  have hsurj : ∀ b : B, ∃ a : A, ∃ t ∈ Submonoid.powers g, t • b = l a := by
    intro b
    obtain ⟨x, hx⟩ := hg.2 (LocalizedModule.mk b 1)
    induction x using LocalizedModule.induction_on with
    | h a s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hx
      obtain ⟨u, hu⟩ := hx
      refine ⟨(u : R) • a, (u : R) * s, mul_mem u.2 s.2, ?_⟩
      simp only [one_smul, Submonoid.smul_def] at hu
      rw [map_smul, mul_smul]
      exact hu.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl fA x
    simp only [Function.uncurry_apply_pair, IsLocalizedModule.map_mk'] at hx ⊢
    rw [IsLocalizedModule.mk'_eq_zero'] at hx ⊢
    obtain ⟨u, hu⟩ := hx
    rw [Submonoid.smul_def, ← LinearMap.map_smul] at hu
    obtain ⟨t, ht, hta⟩ := hinj _ hu
    exact ⟨⟨t, hpow t ht⟩ * u, by rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]; exact hta⟩
  · intro y
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl fB y
    obtain ⟨a, t, ht, hta⟩ := hsurj b
    let t' : p.primeCompl := ⟨t, hpow t ht⟩
    refine ⟨IsLocalizedModule.mk' fA a (t' * s), ?_⟩
    simp only [Function.uncurry_apply_pair, IsLocalizedModule.map_mk']
    rw [← hta]
    exact IsLocalizedModule.mk'_cancel_left fB b t' s

/-- For a finite module and a finitely presented module, bijectivity of a linear map
at one prime spreads to every prime avoiding some element outside it. -/
theorem exists_notMem_forall_bijective [Module.Finite R A] [Module.FinitePresentation R B]
    (l : A →ₗ[R] B) (p₀ : Ideal R) [p₀.IsPrime]
    {Ap₀ : Type*} {Bp₀ : Type*} [AddCommGroup Ap₀] [Module R Ap₀] [AddCommGroup Bp₀]
    [Module R Bp₀] (fA₀ : A →ₗ[R] Ap₀) (fB₀ : B →ₗ[R] Bp₀)
    [IsLocalizedModule p₀.primeCompl fA₀] [IsLocalizedModule p₀.primeCompl fB₀]
    (hl : Function.Bijective (IsLocalizedModule.map p₀.primeCompl fA₀ fB₀ l)) :
    ∃ g : R, g ∉ p₀ ∧ ∀ (p : Ideal R) [p.IsPrime], g ∉ p →
      ∀ {Ap : Type*} {Bp : Type*} [AddCommGroup Ap] [Module R Ap] [AddCommGroup Bp]
        [Module R Bp] (fA : A →ₗ[R] Ap) (fB : B →ₗ[R] Bp)
        [IsLocalizedModule p.primeCompl fA] [IsLocalizedModule p.primeCompl fB],
        Function.Bijective (IsLocalizedModule.map p.primeCompl fA fB l) := by
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective l p₀ fA₀ fB₀ hl
  exact ⟨g, hg, fun p _ hp _ _ _ _ _ _ fA fB _ _ =>
    bijective_map_of_bijective_away l g h p hp fA fB⟩

end Spreading

section Presentation

/-- A linear map is bijective if it sends a finite spanning family, which satisfies a
given family of relations, to a spanning family all of whose relations are generated by
those relations. -/
theorem bijective_of_presentation {O : Type u} {P : Type v} {B : Type w} [CommRing O]
    [AddCommGroup P] [Module O P] [AddCommGroup B] [Module O B] {n m : ℕ} (x : Fin n → P)
    (hx : Submodule.span O (Set.range x) = ⊤) (ρ : Fin m → Fin n → O)
    (hρ : ∀ j, ∑ k, ρ j k • x k = 0) (ℓ : P →ₗ[O] B)
    (hℓ : Submodule.span O (Set.range (ℓ ∘ x)) = ⊤)
    (hker : ∀ c : Fin n → O, ∑ k, c k • ℓ (x k) = 0 → c ∈ Submodule.span O (Set.range ρ)) :
    Function.Bijective ℓ := by
  let L := Fintype.linearCombination O x
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hx]
  have hρL : Submodule.span O (Set.range ρ) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hρ j
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨c, rfl⟩ := hL z
    have hc : ∑ k, c k • ℓ (x k) = 0 := by
      rw [← hz]
      simp only [L, Fintype.linearCombination_apply, map_sum, map_smul]
    exact hρL (hker c hc)
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hℓ, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨x k, rfl⟩

/-- A spanning set for the scalars of a surjective ring map is also spanning for the
original scalars, when these act through the ring map. -/
theorem span_eq_top_of_surjective {O : Type u} {O' : Type v} {P : Type w} [CommRing O]
    [CommRing O'] [AddCommGroup P] [Module O P] [Module O' P] (σ : O →+* O')
    (hσ : Function.Surjective σ) (hsmul : ∀ (o : O) (z : P), o • z = σ o • z) {s : Set P}
    (hs : Submodule.span O' s = ⊤) : Submodule.span O s = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span O' s := hs ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add z w _ _ hz hw => exact add_mem hz hw
  | smul a z _ hz =>
    obtain ⟨o, rfl⟩ := hσ a
    rw [← hsmul]
    exact Submodule.smul_mem _ o hz

end Presentation

end Langlands.CommutativeAlgebra
