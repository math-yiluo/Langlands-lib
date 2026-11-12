import Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistenceAlgebra
import Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistenceTests
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing

/-!
# Descent step of the valuative existence criterion

Let `A` be a valuation ring with fraction field `K`, let `f : X ⟶ Y` be a separated morphism of
algebraic spaces over `S`, and let `x ∈ X(K)` and `y ∈ Y(A)` with `f(x) = y|_K`. Suppose given
an `A`-algebra `P` and a section `ξ ∈ X(P)` with `f(ξ) = y|_P` whose point of `X ×_Y Spec A` is
étale, together with a prime `v` of `P` over the maximal ideal of `A` such that every basic open
`D(p) ∋ v` of `Spec P` meets the locus where `ξ` agrees with `x`. Then `x` extends to a section
over `Spec A` lifting `y`.

The section is obtained by fppf descent along `A → D`, where `D` is the image of `P` in the
coordinate ring of the locus in `Spec (K ⊗[A] P)` where the pullbacks of `x` and `ξ` agree.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence

variable {S : Scheme.{u}} {A : Type u} [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S)

theorem algTestMap_id (R : Type u) [CommRing R] [Algebra A R] :
    algTestMap s (AlgHom.id A R) = 𝟙 _ := by
  ext1
  change Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _
  exact Spec.map_id _

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Y.sections (Over.mk s))

/-- Two sections over `Spec R` agree once they agree after an injective ring map, provided the
locus where they agree is cut out by an ideal. -/
theorem eq_of_pullback_eq_of_injective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] {I : Ideal R} {ξ₁ ξ₂ : X.sections (algTest s R)}
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I)) ξ₁ ξ₂)
    (ψ : R →ₐ[A] R') (hψ : Function.Injective ψ)
    (h : X.pullback (algTestMap s ψ) ξ₁ = X.pullback (algTestMap s ψ) ξ₂) : ξ₁ = ξ₂ := by
  have hle := (pullback_eq_iff_le_ker s hI ψ).mp h
  have hbot : I ≤ RingHom.ker (AlgHom.id A R) := by
    intro t ht
    have h0 := hle ht
    rw [RingHom.mem_ker] at h0 ⊢
    exact hψ (h0.trans (map_zero ψ).symm)
  have h' := (pullback_eq_iff_le_ker s hI (AlgHom.id A R)).mpr hbot
  rwa [algTestMap_id, pullback_id, pullback_id] at h'

/-- Restrictions of a section lying over `y` lie over `y`. -/
theorem mapSections_pullback_algTestMap {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] {χ : X.sections (algTest s R)}
    (hχ : mapSections f _ χ = Y.pullback (algTestBase s R) y) (φ : R →ₐ[A] R') :
    mapSections f _ (X.pullback (algTestMap s φ) χ) = Y.pullback (algTestBase s R') y := by
  rw [← mapSections_naturality, hχ, ← pullback_comp, algTestMap_base]

/-- **Algebraic core of finite presentation.** Let `D = P ⧸ J` be faithfully flat over `A`, let
`q : D ⊗[A] P → O` be a surjection of `A`-algebras with `O` étale over `D` (via `D → D ⊗[A] P → O`),
and let `σ : O → D ⊗[A] D` be compatible with `D ⊗[A] P → D ⊗[A] D`. If the map
`P → O → K ⊗[A] O` kills `J`, then `σ` is bijective, so `D ⊗[A] D` is of finite presentation over
`D`, and `D` is of finite presentation over `A` by faithfully flat descent. -/
theorem finitePresentation_of_etale (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    {P O : Type u} [CommRing P] [Algebra A P] [CommRing O] [Algebra A O]
    (J : Ideal P) [Module.FaithfullyFlat A (P ⧸ J)]
    (q : (P ⧸ J) ⊗[A] P →ₐ[A] O) (hq : Function.Surjective q)
    (hφ : (q.comp
      (Algebra.TensorProduct.includeLeft : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] P)).toRingHom.Etale)
    (σ : O →ₐ[A] (P ⧸ J) ⊗[A] (P ⧸ J))
    (hσ : σ.comp q = Algebra.TensorProduct.map (AlgHom.id A (P ⧸ J)) (Ideal.Quotient.mkₐ A J))
    (hJg : ∀ p ∈ J, ((Algebra.TensorProduct.includeRight : O →ₐ[A] K ⊗[A] O).comp
      (q.comp (Algebra.TensorProduct.includeRight : P →ₐ[A] (P ⧸ J) ⊗[A] P))) p = 0) :
    Algebra.FinitePresentation A (P ⧸ J) := by
  set φ := q.comp (Algebra.TensorProduct.includeLeft : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] P)
  obtain ⟨hφflat, -, hφfp⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp hφ
  -- `O` is flat over `A`.
  have hDflat : (algebraMap A (P ⧸ J)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Module.Flat A O := by
    rw [← RingHom.flat_algebraMap_iff]
    have e : φ.toRingHom.comp (algebraMap A (P ⧸ J)) = algebraMap A O :=
      RingHom.ext fun a => φ.commutes a
    rw [← e]
    exact hDflat.comp hφflat
  -- The map `τ : D ⊗[A] D → K ⊗[A] O` is a left inverse of `σ` after `O → K ⊗[A] O`.
  let τ := Algebra.TensorProduct.productMap ((Algebra.TensorProduct.includeRight).comp φ)
    (Ideal.Quotient.liftₐ J _ hJg)
  have hτσq : (τ.comp σ).comp q =
      (Algebra.TensorProduct.includeRight : O →ₐ[A] K ⊗[A] O).comp q := by
    rw [AlgHom.comp_assoc, hσ]
    apply Algebra.TensorProduct.ext'
    intro d p
    have hl : Ideal.Quotient.liftₐ J _ hJg (Ideal.Quotient.mkₐ A J p) =
        (Algebra.TensorProduct.includeRight : O →ₐ[A] K ⊗[A] O) (q (1 ⊗ₜ p)) :=
      congrArg (fun F => F p) (Ideal.Quotient.liftₐ_comp J _ hJg)
    simp only [τ, φ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hl,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, mul_one, one_mul]
  have hσinj : Function.Injective σ := by
    intro a b hab
    apply includeRight_injective (A := A) (K := K) O
    obtain ⟨a', rfl⟩ := hq a
    obtain ⟨b', rfl⟩ := hq b
    have h := congrArg τ hab
    have ha := congrArg (fun F => F a') hτσq
    have hb := congrArg (fun F => F b') hτσq
    simp only [AlgHom.comp_apply] at ha hb
    rw [← ha, ← hb, h]
  have hσsurj : Function.Surjective σ := by
    intro z
    obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective (P ⧸ J)
      (g := (Ideal.Quotient.mkₐ A J).toLinearMap) (Ideal.Quotient.mkₐ_surjective A J) z
    refine ⟨q w, ?_⟩
    rw [← AlgHom.comp_apply, hσ]
    exact hw
  have hσφ : σ.toRingHom.comp φ.toRingHom =
      algebraMap (P ⧸ J) ((P ⧸ J) ⊗[A] (P ⧸ J)) := by
    refine RingHom.ext fun d => ?_
    have h := congrArg (fun F => F (d ⊗ₜ[A] (1 : P))) hσ
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      map_one] at h
    simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, h,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hfp : (algebraMap (P ⧸ J) ((P ⧸ J) ⊗[A] (P ⧸ J))).FinitePresentation := by
    rw [← hσφ]
    exact (RingHom.FinitePresentation.of_bijective (f := σ.toRingHom) ⟨hσinj, hσsurj⟩).comp
      hφfp
  have := RingHom.finitePresentation_algebraMap.mp hfp
  exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat (P ⧸ J)

section Core

variable {K : Type u} [Field K] [Algebra A K] {x : X.sections (algTest s K)}
  {P : Type u} [CommRing P] [Algebra A P] {ξ : X.sections (algTest s P)}
  {I : Ideal (K ⊗[A] P)}

/-- Two restrictions of `ξ` and `x` agree exactly when the induced map out of `K ⊗[A] P` kills
the equalizer ideal. -/
theorem pullback_eq_iff_le_ker_productMap
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ))
    {R : Type u} [CommRing R] [Algebra A R] (k : K →ₐ[A] R) (g : P →ₐ[A] R) :
    X.pullback (algTestMap s g) ξ = X.pullback (algTestMap s k) x ↔
      I ≤ RingHom.ker (Algebra.TensorProduct.productMap k g) := by
  rw [← pullback_eq_iff_le_ker s hI, ← pullback_comp, ← pullback_comp, ← algTestMap_comp,
    ← algTestMap_comp, Algebra.TensorProduct.productMap_left,
    Algebra.TensorProduct.productMap_right, eq_comm]

variable [IsDomain A] [IsFractionRing A K]

/-- **Restrictions through the quotient.** Write `J ⊆ P` for the preimage of the equalizer
ideal. For every `A`-algebra `R`, `A`-algebra map `k : K → R` and `h : P ⧸ J → R`, the
restriction of `ξ` along `P → P ⧸ J → R` agrees with that of `x` along `k`. -/
theorem pullback_quotient_eq
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ))
    {R : Type u} [CommRing R] [Algebra A R] (k : K →ₐ[A] R)
    (h : P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) →ₐ[A] R) :
    X.pullback (algTestMap s h)
        (X.pullback (algTestMap s (Ideal.Quotient.mkₐ A
          (I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)))) ξ) =
      X.pullback (algTestMap s k) x := by
  rw [← pullback_comp, ← algTestMap_comp, pullback_eq_iff_le_ker_productMap s hI]
  let : Algebra K R := k.toRingHom.toAlgebra
  have : IsScalarTower A K R := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  intro t ht
  refine map_eq_zero_of_tmul _ I (fun p hp => ?_) ht
  have hp' : p ∈ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) := hp
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp']

omit [IsDomain A] [IsFractionRing A K] in
/-- If the restrictions of `ξ` along `g` and of `x` along `k` agree, then `g` kills the preimage
`J ⊆ P` of the equalizer ideal. -/
theorem eq_zero_of_pullback_eq
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ))
    {R : Type u} [CommRing R] [Algebra A R] (k : K →ₐ[A] R) (g : P →ₐ[A] R)
    (he : X.pullback (algTestMap s g) ξ = X.pullback (algTestMap s k) x) {p : P}
    (hp : p ∈ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) : g p = 0 := by
  have h0 := (pullback_eq_iff_le_ker_productMap s hI k g).mp he (Ideal.mem_comap.mp hp)
  rw [RingHom.mem_ker] at h0
  simpa only [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul] using h0

omit [IsDomain A] [IsFractionRing A K] in
/-- The equalizer locus meets every basic open `D(p) ∋ v`, so the preimage `J` of the
equalizer ideal is contained in `v`. -/
theorem comap_le_of_forall_ne_zero
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ))
    (v : Ideal P)
    (Htop : ∀ p ∉ v, ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (k : K →ₐ[A] R)
      (g : P →ₐ[A] R), X.pullback (algTestMap s g) ξ = X.pullback (algTestMap s k) x ∧ g p ≠ 0) :
    I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) ≤ v := by
  intro p hp
  by_contra hpv
  obtain ⟨R, _, _, k, g, he, hgp⟩ := Htop p hpv
  exact hgp (eq_zero_of_pullback_eq s hI k g he hp)

variable (K) in
/-- The image of `P` in `(K ⊗[A] P) ⧸ I` is flat over the valuation ring `A`. -/
theorem flat_quotient_comap [ValuationRing A] (I : Ideal (K ⊗[A] P)) :
    Module.Flat A (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) := by
  let ι := Ideal.quotientMapₐ I (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) le_rfl
  have hinj : Function.Injective ι := Ideal.quotientMap_injective' (H := le_rfl) le_rfl
  exact flat_of_injective (K := K) ι.toLinearMap hinj

/-- If `J ⊆ v` with `v` a prime over the maximal ideal of `A`, then `P ⧸ J` is faithfully flat
over `A`. -/
theorem faithfullyFlat_quotient [ValuationRing A] (I : Ideal (K ⊗[A] P)) (v : Ideal P)
    [v.IsPrime] (hv : (IsLocalRing.maximalIdeal A).map (algebraMap A P) ≤ v)
    (hJ : I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) ≤ v) :
    Module.FaithfullyFlat A
      (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) := by
  have := flat_quotient_comap K I
  apply faithfullyFlat_of_map_maximalIdeal_ne_top
  intro htop
  let q := Ideal.Quotient.factor hJ
  have hle : (IsLocalRing.maximalIdeal A).map
      (algebraMap A (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P))) ≤
      RingHom.ker q := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← Ideal.Quotient.mk_algebraMap]
    simp only [q, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv (Ideal.mem_map_of_mem _ ha))
  rw [htop, top_le_iff] at hle
  exact RingHom.ker_ne_top q hle

/-- **Cocycle condition.** The restriction `θ` of `ξ` to `D = P ⧸ J` has equal pullbacks along
the two maps `D → D ⊗[A] D`: both agree with `x` after base change to `K`, and `D ⊗[A] D`
embeds into `K ⊗[A] (D ⊗[A] D)` by flatness. -/
theorem pullback_includeLeft_eq_includeRight [ValuationRing A] (hf : IsSeparatedMorphism f)
    (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y)
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ)) :
    X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft :
        P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) →ₐ[A]
          (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ⊗[A]
            (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P))))
        (X.pullback (algTestMap s (Ideal.Quotient.mkₐ A
          (I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)))) ξ) =
      X.pullback (algTestMap s (Algebra.TensorProduct.includeRight :
        P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P) →ₐ[A]
          (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ⊗[A]
            (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P))))
        (X.pullback (algTestMap s (Ideal.Quotient.mkₐ A
          (I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)))) ξ) := by
  set J := I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)
  have := flat_quotient_comap K I
  have hθ := mapSections_pullback_algTestMap s f y hξ (Ideal.Quotient.mkₐ A J)
  obtain ⟨I₂, hI₂⟩ := exists_ideal_representsEqualizer s f hf _ _
    ((mapSections_pullback_algTestMap s f y hθ
      (Algebra.TensorProduct.includeLeft : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] (P ⧸ J))).trans
      (mapSections_pullback_algTestMap s f y hθ
      (Algebra.TensorProduct.includeRight : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] (P ⧸ J))).symm)
  have hinj := includeRight_injective (A := A) (K := K) ((P ⧸ J) ⊗[A] (P ⧸ J))
  refine eq_of_pullback_eq_of_injective s hI₂ _ hinj ?_
  have e₁ := pullback_quotient_eq s hI (R := K ⊗[A] ((P ⧸ J) ⊗[A] (P ⧸ J)))
    Algebra.TensorProduct.includeLeft
    ((Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft)
  have e₂ := pullback_quotient_eq s hI (R := K ⊗[A] ((P ⧸ J) ⊗[A] (P ⧸ J)))
    Algebra.TensorProduct.includeLeft
    ((Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight)
  simp only [← pullback_comp, ← algTestMap_comp, AlgHom.comp_assoc] at e₁ e₂ ⊢
  rw [e₁, e₂]

/-- **Finite presentation.** The algebra `D = P ⧸ J` is of finite presentation over `A`. The
locus in `Spec (D ⊗[A] P)` where the two pullbacks of `θ = ξ|_D` and `ξ` agree is étale over
`Spec D`, and `finitePresentation_of_etale` applies to its ideal. -/
theorem finitePresentation_quotient [ValuationRing A] (hf : IsSeparatedMorphism f)
    (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y)
    (hb : IsEtale (zOf s f y ξ (algTestBase s P) hξ))
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ))
    [Module.FaithfullyFlat A
      (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P))] :
    Algebra.FinitePresentation A
      (P ⧸ I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) := by
  set J := I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)
  have hθ := mapSections_pullback_algTestMap s f y hξ (Ideal.Quotient.mkₐ A J)
  have hc := pullback_includeLeft_eq_includeRight s f y hf hξ hI
  obtain ⟨I', hI'⟩ := exists_ideal_representsEqualizer s f hf
    (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] P))
      (X.pullback (algTestMap s (Ideal.Quotient.mkₐ A J)) ξ))
    (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] (P ⧸ J) ⊗[A] P)) ξ)
    ((mapSections_pullback_algTestMap s f y hθ _).trans
      (mapSections_pullback_algTestMap s f y hξ _).symm)
  have het := etale_of_chart s f y ξ hξ hb _ hθ hI'
  have hker : ∀ t ∈ I',
      Algebra.TensorProduct.map (AlgHom.id A (P ⧸ J)) (Ideal.Quotient.mkₐ A J) t = 0 := by
    have h := (pullback_eq_iff_le_ker s hI'
      (Algebra.TensorProduct.map (AlgHom.id A (P ⧸ J)) (Ideal.Quotient.mkₐ A J))).mp (by
        simp only [← pullback_comp, ← algTestMap_comp] at hc ⊢
        convert hc using 3 <;> ext <;> simp <;> rfl)
    exact fun t ht => h ht
  refine finitePresentation_of_etale K J (Ideal.Quotient.mkₐ A I')
    (Ideal.Quotient.mkₐ_surjective A I') ?_ (Ideal.Quotient.liftₐ I' _ hker)
    (Ideal.Quotient.liftₐ_comp I' _ hker) ?_
  · rw [algTestMap_left] at het
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  · intro p hp
    have heq : X.pullback (algTestMap s (Ideal.Quotient.mkₐ A I'))
        (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft :
          P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] P)) (X.pullback (algTestMap s (Ideal.Quotient.mkₐ A J)) ξ)) =
        X.pullback (algTestMap s (Ideal.Quotient.mkₐ A I'))
          (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight :
            P →ₐ[A] (P ⧸ J) ⊗[A] P)) ξ) :=
      (hI' (algTestMap s (Ideal.Quotient.mkₐ A I'))).1 ⟨𝟙 _, Category.id_comp _⟩
    refine eq_zero_of_pullback_eq s hI (R := K ⊗[A] (((P ⧸ J) ⊗[A] P) ⧸ I'))
      Algebra.TensorProduct.includeLeft _ ?_ hp
    rw [← pullback_quotient_eq s hI _ ((Algebra.TensorProduct.includeRight).comp
      ((Ideal.Quotient.mkₐ A I').comp
        (Algebra.TensorProduct.includeLeft : P ⧸ J →ₐ[A] (P ⧸ J) ⊗[A] P)))]
    simp only [algTestMap_comp, pullback_comp]
    rw [heq]

/-- **Descent step.** Let `ξ` be a section over an `A`-algebra `P` lying over `y` whose point of
`X ×_Y Spec A` is étale, and `v` a prime of `P` over the maximal ideal of `A` such that every
basic open `D(p) ∋ v` meets the locus where `ξ` agrees with `x`. Then `x` extends to a section
over `Spec A` lying over `y`. -/
theorem exists_lift_of_chart [ValuationRing A] (hf : IsSeparatedMorphism f)
    (hx : mapSections f _ x = Y.pullback (algTestBase s K) y)
    (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y)
    (hb : IsEtale (zOf s f y ξ (algTestBase s P) hξ))
    (v : Ideal P) [v.IsPrime] (hv : (IsLocalRing.maximalIdeal A).map (algebraMap A P) ≤ v)
    (Htop : ∀ p ∉ v, ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (k : K →ₐ[A] R)
      (g : P →ₐ[A] R), X.pullback (algTestMap s g) ξ = X.pullback (algTestMap s k) x ∧ g p ≠ 0) :
    ∃ a : X.sections (Over.mk s),
      X.pullback (algTestBase s K) a = x ∧ mapSections f _ a = y := by
  obtain ⟨I, hI⟩ := exists_ideal_representsEqualizer s f hf
    (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] P)) x)
    (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)) ξ)
    ((mapSections_pullback_algTestMap s f y hx _).trans
      (mapSections_pullback_algTestMap s f y hξ _).symm)
  set J := I.comap (Algebra.TensorProduct.includeRight : P →ₐ[A] K ⊗[A] P)
  have hJ : J ≤ v := comap_le_of_forall_ne_zero s hI v Htop
  have : Module.FaithfullyFlat A (P ⧸ J) := faithfullyFlat_quotient I v hv hJ
  have : Algebra.FinitePresentation A (P ⧸ J) := finitePresentation_quotient s f y hf hξ hb hI
  -- `Spec (P ⧸ J) ⟶ Spec A` is an fppf covering.
  have hff : (algebraMap A (P ⧸ J)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hfs := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A (P ⧸ J)))).mpr hff
  have : Flat (algTestBase s (P ⧸ J)).left := hfs.1
  have : Surjective (algTestBase s (P ⧸ J)).left := hfs.2
  have : LocallyOfFinitePresentation (algTestBase s (P ⧸ J)).left := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A (P ⧸ J))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  -- Descend `θ = ξ|_{P ⧸ J}`.
  have hθ := mapSections_pullback_algTestMap s f y hξ (Ideal.Quotient.mkₐ A J)
  obtain ⟨a, ha⟩ := ProductPointsDescent.exists_pullback_eq X (algTestBase s (P ⧸ J))
    (isPullback_algTest s (P ⧸ J) (P ⧸ J)) _ (pullback_includeLeft_eq_includeRight s f y hf hξ hI)
  have hfa : mapSections f _ a = y := by
    apply ProductPointsDescent.pullback_injective Y (algTestBase s (P ⧸ J))
    rw [mapSections_naturality, ha, hθ]
  refine ⟨a, ?_, hfa⟩
  -- `a|_K = x` by separatedness, checked after the injective map `K → K ⊗[A] (P ⧸ J)`.
  obtain ⟨I₀, hI₀⟩ := exists_ideal_representsEqualizer s f hf
    (X.pullback (algTestBase s K) a) x
    ((mapSections_naturality f _ a).symm.trans (by rw [hfa, hx]))
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] (P ⧸ J)) :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] (P ⧸ J)).toRingHom.injective
  refine eq_of_pullback_eq_of_injective s hI₀ _ hinj ?_
  rw [← pullback_comp, (isPullback_algTest s K (P ⧸ J)).w, pullback_comp, ha]
  exact pullback_quotient_eq s hI _ _

end Core

end Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence
