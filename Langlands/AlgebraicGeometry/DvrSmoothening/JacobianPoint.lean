import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus

/-! # The Jacobian criterion at a point for a quotient of a polynomial ring -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Localization commutes with quotients: if `A'` is the localization of `A` at `M`, then
`A' ⧸ J A'` is the localization of `A ⧸ J` at the image of `M`. -/
theorem isLocalization_quotient {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (M : Submonoid A) [IsLocalization M A'] (J : Ideal A) :
    letI := (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A')
      Ideal.le_comap_map).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk J)) (A' ⧸ J.map (algebraMap A A')) := by
  letI := (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A')
      Ideal.le_comap_map).toAlgebra
  have halg : ∀ a : A, algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A'))
      (Ideal.Quotient.mk J a) = Ideal.Quotient.mk _ (algebraMap A A' a) := fun a => rfl
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [halg]
    exact (IsLocalization.map_units A' ⟨m, hm⟩).map (Ideal.Quotient.mk _)
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, m⟩, ha⟩ := IsLocalization.surj M y
    refine ⟨⟨Ideal.Quotient.mk J a, ⟨Ideal.Quotient.mk J m, m, m.2, rfl⟩⟩, ?_⟩
    simp only
    rw [halg, halg, ← map_mul, ha]
  · intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [halg, halg, Ideal.Quotient.eq, ← map_sub] at hab
    obtain ⟨⟨j, m⟩, hjm⟩ := (IsLocalization.mem_map_algebraMap_iff M A').mp hab
    simp only at hjm
    rw [← map_mul] at hjm
    obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists M A').mp hjm
    refine ⟨⟨Ideal.Quotient.mk J ((d : A) * m), (d : A) * m, M.mul_mem d.2 m.2, rfl⟩, ?_⟩
    simp only
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : (d : A) * m * (x - y) = (d : A) * (j : A) := by
      rw [← hd]
      ring
    rw [this]
    exact J.mul_mem_left _ j.2

/-- A linear map is injective if its domain is spanned by a finite family whose image is
linearly independent. -/
theorem injective_of_span_eq_top_of_linearIndependent {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] {ι : Type*} [Fintype ι]
    (F : M →ₗ[K] N) (v : ι → M) (hv : Submodule.span K (Set.range v) = ⊤)
    (hli : LinearIndependent K (F ∘ v)) : Function.Injective F := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hxs : x ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  have h0 : ∑ i, a i • (F ∘ v) i = 0 := by
    simpa [map_sum] using (LinearMap.mem_ker.mp hx)
  have ha := Fintype.linearIndependent_iff.mp hli a h0
  simp [ha]

section Jacobian

variable {R : Type u} [CommRing R]

/-- The Jacobian criterion at a point: let `P` be a formally smooth `R`-algebra with finite free
differentials, `f₁, …, f_c ∈ P`, and `𝔓` the kernel of an algebra map from `P` to a field `L`
which kills the `fᵢ`. If the differentials `1 ⊗ dfᵢ ∈ L ⊗ Ω_P` are linearly independent over
`L`, then the localization `P'` of `P` at `𝔓`, divided by the `fᵢ`, is formally smooth over
`R`. -/
theorem formallySmooth_quotient_of_linearIndependent {P P' L : Type u} [CommRing P] [Algebra R P]
    [CommRing P'] [Algebra P P'] [Algebra R P'] [IsScalarTower R P P'] [Field L] [Algebra P L]
    [Algebra P' L] [IsScalarTower P P' L] (𝔓 : Ideal P) [𝔓.IsPrime]
    [IsLocalization.AtPrime P' 𝔓] (h𝔓 : 𝔓 = RingHom.ker (algebraMap P L))
    [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    {c : ℕ} (f : Fin c → P) (hf : ∀ i, algebraMap P L (f i) = 0)
    (hli : LinearIndependent L (fun i => (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (f i))) :
    Algebra.FormallySmooth R (P' ⧸ (Ideal.span (Set.range f)).map (algebraMap P P')) := by
  classical
  set J' := (Ideal.span (Set.range f)).map (algebraMap P P') with hJ'def
  have : IsLocalRing P' := IsLocalization.AtPrime.isLocalRing P' 𝔓
  have hJ' : J' ≤ RingHom.ker (algebraMap P' L) := by
    rw [hJ'def, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact hf i
  letI : Algebra (P' ⧸ J') L := (Ideal.Quotient.lift J' (algebraMap P' L) hJ').toAlgebra
  have : IsScalarTower P' (P' ⧸ J') L :=
    IsScalarTower.of_algebraMap_eq (R := P') (S := P' ⧸ J') (A := L) fun x => rfl
  have hJ'top : J' ≠ ⊤ := fun h => by
    have : (1 : P') ∈ RingHom.ker (algebraMap P' L) := hJ' (h ▸ Submodule.mem_top)
    simp at this
  have : Nontrivial (P' ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hJ'top
  have : IsLocalRing (P' ⧸ J') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
  have : Algebra.FormallyEtale P P' := Algebra.FormallyEtale.of_isLocalization 𝔓.primeCompl
  have : Algebra.FormallySmooth R P' := Algebra.FormallySmooth.comp R P P'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R P P'
  have : Module.Free P' Ω[P'⁄R] := .of_equiv e
  have : Module.Finite P' Ω[P'⁄R] := .of_surjective e.toLinearMap e.surjective
  have h₁ : Function.Surjective (algebraMap P' (P' ⧸ J')) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap P' (P' ⧸ J')) = J' := Ideal.mk_ker
  have hfg : (Ideal.span (Set.range f)).FG :=
    ⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  have h₂ : (RingHom.ker (algebraMap P' (P' ⧸ J'))).FG := by
    rw [hker]
    exact hfg.map _
  have hmax : IsLocalRing.maximalIdeal P' ≤ RingHom.ker (algebraMap P' L) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔓 P', Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    rw [h𝔓] at hx
    exact hx
  have h₃ : IsLocalRing.maximalIdeal (P' ⧸ J') ≤ RingHom.ker (algebraMap (P' ⧸ J') L) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : y ∈ IsLocalRing.maximalIdeal P' := by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).mp hx ((IsLocalRing.notMem_maximalIdeal.mp h).map _)
    exact hmax hy
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P' L h₁ h₂ h₃]
  let g : Fin c → RingHom.ker (algebraMap P' (P' ⧸ J')) := fun i =>
    ⟨algebraMap P P' (f i), by
      rw [hker]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hg : Submodule.span P' (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective
      (RingHom.ker (algebraMap P' (P' ⧸ J'))).injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    change Submodule.span P' (Set.range fun i => algebraMap P P' (f i)) =
      RingHom.ker (algebraMap P' (P' ⧸ J'))
    rw [hker, hJ'def, Ideal.map_span, ← Set.range_comp]
    rfl
  have hv : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[P'] g i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have key : ∀ k ∈ Submodule.span P' (Set.range g), ∀ l : L,
        l ⊗ₜ[P'] k ∈ Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[P'] g i) := by
      intro k hk
      induction hk using Submodule.span_induction with
      | mem k hk =>
        obtain ⟨i, rfl⟩ := hk
        intro l
        have : l ⊗ₜ[P'] g i = l • ((1 : L) ⊗ₜ[P'] g i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      | zero => intro l; rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add k₁ k₂ _ _ h₁ h₂ =>
        intro l; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ (h₁ l) (h₂ l)
      | smul a k _ h => intro l; rw [← TensorProduct.smul_tmul]; exact h _
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | tmul l k => exact key k (hg ▸ Submodule.mem_top) l
  let Φ : L ⊗[P] Ω[P⁄R] ≃ₗ[L] L ⊗[P'] Ω[P'⁄R] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P P' L L Ω[P⁄R]).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) e)
  have hΦ : ∀ i, Φ ((1 : L) ⊗ₜ KaehlerDifferential.D R P (f i)) =
      (1 : L) ⊗ₜ KaehlerDifferential.D R P' (algebraMap P P' (f i)) := by
    intro i
    simp [Φ, e, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
  have hli' : LinearIndependent L
      (KaehlerDifferential.cotangentComplexBaseChange R (P' ⧸ J') P' L ∘
        fun i => (1 : L) ⊗ₜ[P'] g i) := by
    have := hli.map' Φ.toLinearMap (LinearEquiv.ker _)
    convert this using 1
    funext i
    simp only [Function.comp_apply, LinearEquiv.coe_coe, hΦ,
      KaehlerDifferential.cotangentComplexBaseChange_tmul, KaehlerDifferential.kerToTensor_apply,
      one_smul, g]
  exact injective_of_span_eq_top_of_linearIndependent _ _ hv hli'

end Jacobian

section Relations

/-- Let `P → A` be surjective and `L` a field which is an `A`-algebra, with `L ⊗_P Ω_{P/R}`
finite-dimensional over `L`. Then there are elements `f₁, …, f_c` of the kernel whose
differentials `1 ⊗ dfᵢ ∈ L ⊗_P Ω_{P/R}` are linearly independent, with `c` at least
`dim (L ⊗_P Ω_{P/R}) − dim (L ⊗_A Ω_{A/R})`. -/
theorem exists_relations_linearIndependent {R P A L : Type u} [CommRing R] [CommRing P]
    [CommRing A] [Field L] [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    [Algebra A L] [Algebra P L] [IsScalarTower P A L]
    (hsurj : Function.Surjective (algebraMap P A)) [Module.Finite L (L ⊗[P] Ω[P⁄R])] :
    ∃ (c : ℕ) (f : Fin c → P), (∀ i, algebraMap P A (f i) = 0) ∧
      LinearIndependent L (fun i => (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (f i)) ∧
      Module.finrank L (L ⊗[P] Ω[P⁄R]) ≤ c + Module.finrank L (L ⊗[A] Ω[A⁄R]) := by
  classical
  let v : RingHom.ker (algebraMap P A) → L ⊗[P] Ω[P⁄R] :=
    fun g => (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (g : P)
  let W := Submodule.span L (Set.range v)
  let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange P A L L Ω[P⁄R]
  let ψ : L ⊗[P] Ω[P⁄R] →ₗ[L] L ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor L L (KaehlerDifferential.mapBaseChange R P A) ∘ₗ
      cb.symm.toLinearMap
  have hg := KaehlerDifferential.mapBaseChange_surjective R P A hsurj
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective L hg y
    exact ⟨cb z, by simp [ψ]⟩
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R P A hsurj
  have hex' := lTensor_exact (R := A) (M := LinearMap.ker (KaehlerDifferential.mapBaseChange R P A))
    (N := A ⊗[P] Ω[P⁄R]) (P := Ω[A⁄R]) L
    (LinearMap.exact_subtype_ker_map (KaehlerDifferential.mapBaseChange R P A)) hg
  have hker : LinearMap.ker ψ ≤ W := by
    intro x hx
    have hy : LinearMap.lTensor L (KaehlerDifferential.mapBaseChange R P A) (cb.symm x) = 0 := hx
    obtain ⟨z, hz⟩ := (hex' _).mp hy
    have : x = cb (LinearMap.lTensor L (LinearMap.ker
        (KaehlerDifferential.mapBaseChange R P A)).subtype z) := by
      rw [hz, LinearEquiv.apply_symm_apply]
    rw [this]
    clear this hz
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add]; exact W.add_mem h₁ h₂
    | tmul l k =>
      obtain ⟨t, ht⟩ := (hex k.1).mp k.2
      obtain ⟨g, rfl⟩ := Ideal.toCotangent_surjective _ t
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← ht,
        KaehlerDifferential.kerCotangentToTensor_toCotangent,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
      have : l ⊗ₜ[P] KaehlerDifferential.D R P (g : P) = l • v g := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact W.smul_mem _ (Submodule.subset_span ⟨g, rfl⟩)
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' L v
  have : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun i => (a (e.symm i) : P), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · exact hli.comp _ e.symm.injective
  · have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.mpr hψ, finrank_top] at h1
    have h2 : Module.finrank L (LinearMap.ker ψ) ≤ Fintype.card κ := by
      calc Module.finrank L (LinearMap.ker ψ) ≤ Module.finrank L W := Submodule.finrank_mono hker
        _ = Module.finrank L (Submodule.span L (Set.range (v ∘ a))) := by rw [hspan]
        _ = Fintype.card κ := finrank_span_eq_card hli
    omega

end Relations

section Kernel

/-- Let `C → A` be a surjection of local `R`-algebras, both formally smooth over `R`, with `C`
noetherian and `Ω_{C/R}` finite free, and let `K` be a field which is an `A`-algebra through the
residue field of `A`, with `K ⊗_C Ω_{C/R}` finite-dimensional over `K` (automatic here, as
`Ω_{C/R}` is finite). If `dim_K (K ⊗_C Ω_{C/R}) ≤ dim_K (K ⊗_A Ω_{A/R})`, then `C → A` is
injective. -/
theorem ker_eq_bot_of_finrank_le {R C A K : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Field K] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A] [Algebra A K]
    [Algebra C K] [IsScalarTower C A K] [IsLocalRing C] [IsLocalRing A] [IsNoetherianRing C]
    [Algebra.FormallySmooth R C] [Module.Free C Ω[C⁄R]] [Module.Finite C Ω[C⁄R]]
    [Algebra.FormallySmooth R A] (hsurj : Function.Surjective (algebraMap C A))
    (hK : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A K))
    [Module.Finite K (K ⊗[C] Ω[C⁄R])]
    (hdim : Module.finrank K (K ⊗[C] Ω[C⁄R]) ≤ Module.finrank K (K ⊗[A] Ω[A⁄R])) :
    RingHom.ker (algebraMap C A) = ⊥ := by
  classical
  have h₂ : (RingHom.ker (algebraMap C A)).FG := IsNoetherian.noetherian _
  have hinj := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := R) C K
    hsurj h₂ hK).mp inferInstance
  let F := KaehlerDifferential.cotangentComplexBaseChange R A C K
  let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange C A K K Ω[C⁄R]
  let G : K ⊗[C] Ω[C⁄R] →ₗ[K] K ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor K K (KaehlerDifferential.mapBaseChange R C A) ∘ₗ
      cb.symm.toLinearMap
  have hg := KaehlerDifferential.mapBaseChange_surjective R C A hsurj
  have hG : Function.Surjective G := by
    intro y
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective K hg y
    exact ⟨cb z, by simp [G]⟩
  have hGF : ∀ x, G (F x) = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | tmul k t =>
      simp only [F, G, cb, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        KaehlerDifferential.cotangentComplexBaseChange_tmul, KaehlerDifferential.kerToTensor_apply,
        map_smul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        TensorProduct.AlgebraTensorModule.lTensor_tmul, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D, one_smul]
      rw [RingHom.mem_ker.mp t.2, map_zero, TensorProduct.tmul_zero, smul_zero]
  have : Module.Finite K (K ⊗[A] Ω[A⁄R]) := Module.Finite.of_surjective G hG
  have h1 := LinearMap.finrank_range_add_finrank_ker G
  rw [LinearMap.range_eq_top.mpr hG, finrank_top] at h1
  have hker0 : LinearMap.ker G = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hF0 : ∀ x, F x = 0 := fun x => by
    have : F x ∈ LinearMap.ker G := hGF x
    rwa [hker0, Submodule.mem_bot] at this
  have hsub : Subsingleton (K ⊗[C] RingHom.ker (algebraMap C A)) :=
    ⟨fun x y => hinj (by rw [hF0, hF0])⟩
  -- Nakayama.
  have : IsLocalHom (algebraMap C A) := IsLocalHom.of_surjective _ hsurj
  have hCK : IsLocalRing.maximalIdeal C ≤ RingHom.ker (algebraMap C K) := by
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply C A K]
    exact hK (map_nonunit (algebraMap C A) x hx)
  letI : Algebra (IsLocalRing.ResidueField C) K :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal C) (algebraMap C K) hCK).toAlgebra
  have : IsScalarTower C (IsLocalRing.ResidueField C) K :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange C (IsLocalRing.ResidueField C) K K
    (RingHom.ker (algebraMap C A))
  have : Subsingleton (K ⊗[IsLocalRing.ResidueField C]
      (IsLocalRing.ResidueField C ⊗[C] RingHom.ker (algebraMap C A))) := e.toEquiv.subsingleton
  have hk : Subsingleton (IsLocalRing.ResidueField C ⊗[C] RingHom.ker (algebraMap C A)) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ K).mp this
  have : Module.Finite C (RingHom.ker (algebraMap C A)) := Module.IsNoetherian.finite C _
  have : Subsingleton (RingHom.ker (algebraMap C A)) :=
    (IsLocalRing.subsingleton_tensorProduct).mp hk
  exact (Submodule.subsingleton_iff_eq_bot).mp this

end Kernel

section Ranks

/-- For a nonzero formally étale `C`-algebra `S` with free `Ω_{S/R}` and a field `F` over `S`,
the dimension of `F ⊗_C Ω_{C/R}` is the rank of `Ω_{S/R}` (both `Module.finrank`). -/
theorem finrank_tensor_kaehler_eq {R C S F : Type u} [CommRing R] [CommRing C] [CommRing S]
    [Field F] [Algebra R C] [Algebra C S] [Algebra R S] [IsScalarTower R C S]
    [Algebra.FormallyEtale C S] [Algebra S F] [Algebra C F] [IsScalarTower C S F] [Nontrivial S]
    [Module.Free S Ω[S⁄R]] :
    Module.finrank F (F ⊗[C] Ω[C⁄R]) = Module.finrank S Ω[S⁄R] := by
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange C S F F Ω[C⁄R]
  let e₂ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R C S
  let e : F ⊗[C] Ω[C⁄R] ≃ₗ[F] F ⊗[S] Ω[S⁄R] :=
    e₁.symm.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e₂)
  rw [e.finrank_eq, Module.finrank_baseChange]

/-- The differentials of a formally smooth local algebra which is essentially of finite type are
free. -/
theorem free_kaehler_of_formallySmooth {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [Algebra.FormallySmooth R S] [Algebra.EssFiniteType R S] :
    Module.Free S Ω[S⁄R] :=
  Module.free_of_flat_of_isLocalRing

/-- Let `P → A` be surjective and `L` a field which is an `A`-algebra, with `L ⊗_P Ω_{P/R}`
finite-dimensional over `L`. If `f₁, …, f_c` vanish in `A` and the `1 ⊗ dfᵢ` are linearly
independent in `L ⊗_P Ω_{P/R}`, then `dim (L ⊗_A Ω_{A/R}) + c ≤ dim (L ⊗_P Ω_{P/R})`. -/
theorem finrank_add_le_of_linearIndependent {R P A L : Type u} [CommRing R] [CommRing P]
    [CommRing A] [Field L] [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    [Algebra A L] [Algebra P L] [IsScalarTower P A L]
    (hsurj : Function.Surjective (algebraMap P A)) [Module.Finite L (L ⊗[P] Ω[P⁄R])]
    {c : ℕ} (f : Fin c → P) (hf : ∀ i, algebraMap P A (f i) = 0)
    (hli : LinearIndependent L (fun i => (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (f i))) :
    Module.finrank L (L ⊗[A] Ω[A⁄R]) + c ≤ Module.finrank L (L ⊗[P] Ω[P⁄R]) := by
  let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange P A L L Ω[P⁄R]
  let ψ : L ⊗[P] Ω[P⁄R] →ₗ[L] L ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor L L (KaehlerDifferential.mapBaseChange R P A) ∘ₗ
      cb.symm.toLinearMap
  have hg := KaehlerDifferential.mapBaseChange_surjective R P A hsurj
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective L hg y
    exact ⟨cb z, by simp [ψ]⟩
  have hspan : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (f i))
      ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [ψ, cb, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      KaehlerDifferential.mapBaseChange_tmul, hf i]
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_eq_top.mpr hψ, finrank_top] at h1
  have h2 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h2
  omega

end Ranks

section Generization

/-- For a finitely presented algebra, smoothness at a prime passes to the primes it contains. -/
theorem isSmoothAt_of_le {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] (𝔔 𝔔' : Ideal C) [𝔔.IsPrime] [𝔔'.IsPrime]
    [Algebra.IsSmoothAt R 𝔔] (h : 𝔔' ≤ 𝔔) : Algebra.IsSmoothAt R 𝔔' := by
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R 𝔔
  have := (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (f := g)).mpr hsm
  exact this (show (⟨𝔔', ‹_›⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen g from
    fun hg' => hg (h hg'))

end Generization

end Langlands.AlgebraicGeometry.DvrSmoothening
