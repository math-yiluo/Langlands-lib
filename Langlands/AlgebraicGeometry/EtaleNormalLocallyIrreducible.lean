import Langlands.AnthropicFLT.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.LocallyConstant.Basic

/-! # Étale algebras over integrally closed domains are locally irreducible -/

universe u

open TensorProduct Polynomial CategoryTheory AlgebraicGeometry
open P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.EtaleLocNormalAux

namespace Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible

section Domain

variable {R C : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing C] [Algebra R C] [Algebra.Etale R C]

variable (R) in
include R in
/-- **Idempotent splitting.** Let `R` be an integrally closed domain and `C` an étale
`R`-algebra. Every prime `Q` of `C` avoids an idempotent `e` such that `C[1/e]` is an
integrally closed domain. -/
theorem exists_isIdempotentElem_isDomain_isIntegrallyClosed (Q : Ideal C) [hQ : Q.IsPrime] :
    ∃ e : C, IsIdempotentElem e ∧ e ∉ Q ∧ IsDomain (Localization.Away e) ∧
      IsIntegrallyClosed (Localization.Away e) := by
  classical
  let K := FractionRing R
  obtain ⟨I, hI, L, hL, hLK, eqv, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[R] C)).1 inferInstance
  have : Fintype I := Fintype.ofFinite I
  let e₀ : C ⊗[R] K ≃+* Π i, L i :=
    (Algebra.TensorProduct.comm R C K).toRingEquiv.trans eqv.toRingEquiv
  let φ : C →+* C ⊗[R] K := Algebra.TensorProduct.includeLeftRingHom
  have hφ : Function.Injective φ :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)
  have hφa : algebraMap C (C ⊗[R] K) = φ := rfl
  let ε : I → C ⊗[R] K := fun i => e₀.symm (Pi.single i 1)
  have hεε : ∀ i, ε i * ε i = ε i := fun i => by
    simp only [ε, ← map_mul, ← Pi.single_mul, mul_one]
  have hεint : ∀ i, IsIntegral C (ε i) := by
    intro i
    refine ⟨X ^ 2 - X, ?_, ?_⟩
    · exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
    · simp [pow_two, hεε]
  choose c hc using fun i => exists_algebraMap_eq_of_isIntegral_genericFibre R K C (hεint i)
  have hcφ : ∀ i, φ (c i) = ε i := hc
  have hsum : ∑ i, c i = 1 := by
    apply hφ
    rw [map_sum, map_one]
    simp only [hcφ, ε, ← map_sum, Finset.univ_sum_single]
    exact map_one _
  obtain ⟨i, hi⟩ : ∃ i, c i ∉ Q := by
    by_contra h
    push Not at h
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun i _ => h i))
  set e := c i with he
  have hee : IsIdempotentElem e := hφ (by rw [map_mul, hcφ, hεε])
  -- the projection to the `i`-th factor
  let ψ : C →+* L i := (Pi.evalRingHom L i).comp (e₀.toRingHom.comp φ)
  have hψ : ∀ x, ψ x = e₀ (φ x) i := fun _ => rfl
  have hψe : ψ e = 1 := by
    rw [hψ, hcφ]; simp [ε]
  have hψker : ∀ x, ψ x = 0 → x * e = 0 := by
    intro x hx
    apply hφ
    rw [map_zero, map_mul, hcφ]
    apply e₀.injective
    rw [map_mul, map_zero]
    simp only [ε, RingEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp [← hψ, hx]
    · simp [hj]
  let A := Localization.Away e
  have hAe : algebraMap C A e = 1 := by
    have hu : IsUnit (algebraMap C A e) := IsLocalization.Away.algebraMap_isUnit e
    apply hu.mul_left_cancel
    rw [← map_mul, hee.eq, mul_one]
  have hAsurj : Function.Surjective (algebraMap C A) := by
    intro a
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) a
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 s.2
    refine ⟨x, ?_⟩
    have := IsLocalization.mk'_spec A x s
    rw [← hn, map_pow, hAe, one_pow, mul_one] at this
    exact this.symm
  let ψ' : A →+* L i := IsLocalization.Away.lift e (g := ψ) (by rw [hψe]; exact isUnit_one)
  have hψ' : ∀ x, ψ' (algebraMap C A x) = ψ x := fun x => IsLocalization.lift_eq _ _
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := hAsurj a
    rw [hψ'] at ha
    rw [← mul_one (algebraMap C A x), ← hAe, ← map_mul, hψker x ha, map_zero]
  have hdom : IsDomain A := Function.Injective.isDomain ψ' hinj
  refine ⟨e, hee, hi, hdom, ?_⟩
  -- integral closedness
  refine (isIntegrallyClosed_iff (FractionRing A)).2 fun {x} hx => ?_
  let j : FractionRing A →+* L i := IsFractionRing.lift hinj
  have hj : ∀ a, j (algebraMap A (FractionRing A) a) = ψ' a := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  obtain ⟨p, hpm, hp⟩ := hx
  have hlifts : p ∈ lifts (algebraMap C A) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact hAsurj _
  obtain ⟨q, hqp, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlifts hpm
  set y := j x with hy
  have hψcomp : ψ = (j.comp (algebraMap A (FractionRing A))).comp (algebraMap C A) := by
    ext c'
    simp [hj, hψ']
  have hq : q.eval₂ ψ y = 0 := by
    rw [hψcomp, ← eval₂_map, hqp, hy, ← hom_eval₂, hp, map_zero]
  -- lift `y` to an element of `C ⊗[R] K` integral over `C`
  set Y : C ⊗[R] K := e₀.symm (Pi.single i y) with hY
  have hYint : IsIntegral C Y := by
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    rw [eval₂_mul, eval₂_X]
    apply e₀.injective
    rw [map_mul, map_zero]
    change e₀.toRingHom Y * e₀.toRingHom (eval₂ (algebraMap C (C ⊗[R] K)) Y q) = 0
    rw [hom_eval₂]
    have hY' : e₀.toRingHom Y = Pi.single i y := e₀.apply_symm_apply _
    rw [hY']
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.mul_apply, Pi.zero_apply, Pi.single_eq_same]
      change y * (Pi.evalRingHom L k) (eval₂ _ (Pi.single k y) q) = 0
      rw [hom_eval₂, Pi.evalRingHom_apply, Pi.single_eq_same]
      convert mul_zero y using 2
    · simp [hk]
  obtain ⟨c', hc'⟩ := exists_algebraMap_eq_of_isIntegral_genericFibre R K C hYint
  have hψc' : ψ c' = y := by
    rw [hψ]
    change e₀ (algebraMap C (C ⊗[R] K) c') i = y
    rw [hc', hY, RingEquiv.apply_symm_apply, Pi.single_eq_same]
  refine ⟨algebraMap C A c', j.injective ?_⟩
  rw [hj, hψ', hψc']

end Domain

section NormalBase

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Étale over normal is normal (algebraic form).** If every local ring of `R` at a prime is an
integrally closed domain and `C` is an étale `R`-algebra, then every local ring of `C` at a prime
is an integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_localization_atPrime_of_etale {R C : Type u} [CommRing R]
    [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (hR : ∀ (P : Ideal R) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P))
    (Q : Ideal C) [hQ : Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let p : Ideal R := Q.comap (algebraMap R C)
  let Rp := Localization.AtPrime p
  obtain ⟨hRpd, hRpi⟩ := hR p
  let Cp := Rp ⊗[R] C
  let M : Submonoid C := Algebra.algebraMapSubmonoid C p.primeCompl
  have hloc : IsLocalization M Cp := IsLocalization.tensorRight (S := C) Rp p.primeCompl
  have hdisj : Disjoint (M : Set C) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    exact hr hrQ
  let Q' : Ideal Cp := Q.map (algebraMap C Cp)
  have hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Cp Q hQ hdisj
  have hcomap : Q'.comap (algebraMap C Cp) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M Cp hQ hdisj
  obtain ⟨hTdom, hTic⟩ :=
    Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime Rp Cp Q'
      (Localization.AtPrime Q')
  let T := Localization.AtPrime Q'
  have h1 : IsLocalization (Q'.comap (algebraMap C Cp)).primeCompl T :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (S := Cp) T Q'
  have heq : (Q'.comap (algebraMap C Cp)).primeCompl = Q.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  have h2 : IsLocalization Q.primeCompl T := heq ▸ h1
  let f : Localization.AtPrime Q ≃ₐ[C] T := IsLocalization.algEquiv Q.primeCompl _ _
  have := hTdom
  have := hTic
  exact ⟨Function.Injective.isDomain f.toRingEquiv f.injective,
    IsIntegrallyClosed.of_equiv (R := T) f.toRingEquiv.symm⟩

end NormalBase

section Topology

/-- A topological space is *locally preirreducible* if every point has a preirreducible open
neighbourhood. For example, the underlying space of a scheme étale over an irreducible scheme with
integrally closed domain stalks is locally preirreducible (`isLocallyPreirreducible_of_etale`). -/
def IsLocallyPreirreducible (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U

variable {X : Type*} [TopologicalSpace X]

/-- In a space in which every point has a preirreducible open neighbourhood, the closure of an
open set is clopen. -/
theorem isClopen_closure_of_isOpen
    (hX : IsLocallyPreirreducible X)
    {W : Set X} (hWo : IsOpen W) : IsClopen (closure W) := by
  refine ⟨isClosed_closure, isOpen_iff_forall_mem_open.2 fun y hy => ?_⟩
  obtain ⟨U, hUo, hyU, hUi⟩ := hX y
  refine ⟨U, ?_, hUo, hyU⟩
  have hne : (U ∩ W).Nonempty := mem_closure_iff.1 hy U hUo hyU
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hUi hWo hne).trans
    (closure_mono Set.inter_subset_right)

/-- In a space in which every point has a preirreducible open neighbourhood, the connected
component of a point is open and irreducible. -/
theorem isIrreducible_connectedComponent_and_isOpen
    (hX : IsLocallyPreirreducible X) (x : X) :
    IsIrreducible (connectedComponent x) ∧ IsOpen (connectedComponent x) := by
  obtain ⟨U, hUo, hxU, hUi⟩ := hX x
  have hcl := isClopen_closure_of_isOpen hX hUo
  have hirr : IsIrreducible (closure U) := (show IsIrreducible U from ⟨⟨x, hxU⟩, hUi⟩).closure
  have heq : connectedComponent x = closure U :=
    (hcl.connectedComponent_subset (subset_closure hxU)).antisymm
      (hirr.isConnected.isPreconnected.subset_connectedComponent (subset_closure hxU))
  exact heq ▸ ⟨hirr, hcl.isOpen⟩

/-- A connected space in which every point has a preirreducible open neighbourhood is
irreducible. -/
theorem irreducibleSpace_of_connectedSpace
    (hX : IsLocallyPreirreducible X) [ConnectedSpace X] :
    IrreducibleSpace X := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
  have h := (isIrreducible_connectedComponent_and_isOpen hX x).1
  rw [PreconnectedSpace.connectedComponent_eq_univ] at h
  exact (irreducibleSpace_def X).2 h

/-- **Generic determination.** Let `f : X → S` be generalizing (e.g. a flat morphism of schemes)
and let `η` be a generic point of `S` (it specializes to every point). Two locally constant
functions on `X` that agree on the fibre `f⁻¹{η}` are equal. -/
theorem eq_of_isLocallyConstant_of_generalizingMap {S T : Type*} [TopologicalSpace S]
    {f : X → S} (hf : GeneralizingMap f) {η : S} (hη : ∀ s, η ⤳ s)
    {g₁ g₂ : X → T} (h₁ : IsLocallyConstant g₁) (h₂ : IsLocallyConstant g₂)
    (h : ∀ x, f x = η → g₁ x = g₂ x) : g₁ = g₂ := by
  funext x
  obtain ⟨x', hx'x, hfx'⟩ := hf (hη (f x))
  have e₁ : g₁ x' = g₁ x := hx'x.mem_open (h₁.isOpen_fiber (g₁ x)) rfl
  have e₂ : g₂ x' = g₂ x := hx'x.mem_open (h₂.isOpen_fiber (g₂ x)) rfl
  rw [← e₁, ← e₂, h x' hfx']

/-- A generalizing map from a `T₀` space sends a generic point to a generic point. -/
theorem apply_eq_of_generalizingMap {S : Type*} [TopologicalSpace S] [T0Space X]
    {f : X → S} (hf : GeneralizingMap f) {ξ : X} (hξ : ∀ x, ξ ⤳ x) {η : S} (hη : ∀ s, η ⤳ s) :
    f ξ = η := by
  obtain ⟨x', hx'ξ, hfx'⟩ := hf (hη (f ξ))
  rw [← (hx'ξ.antisymm (hξ x')).eq]
  exact hfx'

end Topology

section Scheme

variable {X S : Scheme.{u}}

/-- Being an integrally closed domain transfers along ring isomorphisms. -/
theorem isDomain_isIntegrallyClosed_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : IsDomain A ∧ IsIntegrallyClosed A) :
    IsDomain B ∧ IsIntegrallyClosed B := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨Function.Injective.isDomain e.symm.toRingHom e.symm.injective,
    IsIntegrallyClosed.of_equiv e⟩

/-- If every stalk of `S` is an integrally closed domain, then so is every localization of the
ring of sections over an affine open at a prime ideal. -/
theorem localization_atPrime_of_stalk
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    {V : S.Opens} (hV : IsAffineOpen V) (P : Ideal Γ(S, V)) [hP : P.IsPrime] :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  let y : PrimeSpectrum Γ(S, V) := ⟨P, hP⟩
  have hy : hV.fromSpec y ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact Set.mem_range_self y
  let := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hV.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (S.presheaf.stalk (hV.fromSpec y)) P :=
    hV.isLocalization_stalk' y hy
  exact isDomain_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (S.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime P)).toRingEquiv (hS _)

/-- **Étale over normal is normal.** If every stalk of `S` is an integrally closed domain and
`f : X ⟶ S` is étale, then every stalk of `X` is an integrally closed domain. -/
theorem stalk_isDomain_isIntegrallyClosed_of_etale (f : X ⟶ S) [Etale f]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV : U ≤ f ⁻¹ᵁ V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).2
  have het : (f.appLE V U hUV).hom.Etale :=
    HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Etale Γ(S, V) Γ(X, U) := het
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isDomain_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv
    (isDomain_isIntegrallyClosed_localization_atPrime_of_etale
      (fun P _ => localization_atPrime_of_stalk hS hV P) _)

/-- If `S` is irreducible and every stalk of `S` is an integrally closed domain, then the ring of
sections over a nonempty affine open is an integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_sections [IrreducibleSpace S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    {V : S.Opens} (hV : IsAffineOpen V) [Nonempty V] :
    IsDomain Γ(S, V) ∧ IsIntegrallyClosed Γ(S, V) := by
  have : ∀ s : S, _root_.IsReduced (S.presheaf.stalk s) := fun s => by
    have := (hS s).1
    infer_instance
  have : IsReduced S := isReduced_of_isReduced_stalk S
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  refine ⟨inferInstance, IsIntegrallyClosed.of_localization_maximal fun P _ _ => ?_⟩
  exact (localization_atPrime_of_stalk hS hV P).2

/-- **Étale schemes over irreducible normal schemes are locally irreducible.** If `S` is
irreducible, every stalk of `S` is an integrally closed domain, and `f : X ⟶ S` is étale, then
every point of `X` has an irreducible open neighbourhood. -/
theorem exists_isIrreducible_of_etale [IrreducibleSpace S] (f : X ⟶ S) [Etale f]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV : U ≤ f ⁻¹ᵁ V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).2
  have : Nonempty V := ⟨⟨f x, hxV⟩⟩
  obtain ⟨hRd, hRi⟩ := isDomain_isIntegrallyClosed_sections hS hV
  have het : (f.appLE V U hUV).hom.Etale :=
    HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Etale Γ(S, V) Γ(X, U) := het
  obtain ⟨e, -, heQ, hdom, -⟩ :=
    exists_isIdempotentElem_isDomain_isIntegrallyClosed Γ(S, V) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  refine ⟨X.basicOpen e, ?_, ?_⟩
  · have h1 : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen e := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 heQ
    have h2 : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen e := h1
    rw [hU.fromSpec_primeIdealOf] at h2
    exact h2
  · have hrange : Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) (Localization.Away e))) =
        PrimeSpectrum.basicOpen e := PrimeSpectrum.localization_away_comap_range _ e
    have hirr : IsIrreducible (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, U))) := by
      rw [← hrange, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (PrimeSpectrum.continuous_comap _).continuousOn
    have himg : hU.fromSpec '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, U))) =
        X.basicOpen e := by
      have h2 : (hU.fromSpec ⁻¹ᵁ X.basicOpen e : Set (Spec Γ(X, U))) =
          (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, U))) :=
        congrArg SetLike.coe (hU.fromSpec_preimage_basicOpen e)
      rw [← h2]
      show hU.fromSpec '' (hU.fromSpec ⁻¹' (X.basicOpen e : Set X)) = _
      refine Set.image_preimage_eq_of_subset ?_
      rw [hU.range_fromSpec]
      exact X.basicOpen_le e
    rw [← himg]
    exact hirr.image _ hU.fromSpec.continuous.continuousOn

/-- The underlying space of a scheme étale over an irreducible scheme with integrally closed
domain stalks is locally preirreducible. -/
theorem isLocallyPreirreducible_of_etale [IrreducibleSpace S] (f : X ⟶ S) [Etale f]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)) :
    IsLocallyPreirreducible X := fun x =>
  let ⟨U, hxU, hU⟩ := exists_isIrreducible_of_etale f hS x
  ⟨U, U.2, hxU, hU.2⟩

/-- A connected scheme étale over an irreducible scheme with integrally closed domain stalks is
irreducible. -/
theorem irreducibleSpace_of_etale [IrreducibleSpace S] (f : X ⟶ S) [Etale f]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    [ConnectedSpace X] : IrreducibleSpace X :=
  irreducibleSpace_of_connectedSpace (isLocallyPreirreducible_of_etale f hS)

/-- For a scheme étale over an irreducible scheme with integrally closed domain stalks, every
connected component is open and irreducible. -/
theorem isIrreducible_connectedComponent_of_etale [IrreducibleSpace S] (f : X ⟶ S) [Etale f]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (x : X) : IsIrreducible (connectedComponent x) ∧ IsOpen (connectedComponent x) :=
  isIrreducible_connectedComponent_and_isOpen (isLocallyPreirreducible_of_etale f hS) x

/-- **Generic determination for flat schemes.** If `S` is irreducible and `f : X ⟶ S` is flat,
then two locally constant functions on `X` that agree on the fibre over the generic point of `S`
are equal. -/
theorem eq_of_isLocallyConstant_of_flat [IrreducibleSpace S] (f : X ⟶ S) [Flat f]
    {T : Type*} {g₁ g₂ : X → T} (h₁ : IsLocallyConstant g₁) (h₂ : IsLocallyConstant g₂)
    (h : ∀ x, f x = genericPoint S → g₁ x = g₂ x) : g₁ = g₂ :=
  eq_of_isLocallyConstant_of_generalizingMap (Flat.generalizingMap f) genericPoint_specializes
    h₁ h₂ h

/-- A flat morphism between irreducible schemes sends the generic point to the generic point. -/
theorem apply_genericPoint_of_flat [IrreducibleSpace S] [IrreducibleSpace X] (f : X ⟶ S)
    [Flat f] : f (genericPoint X) = genericPoint S :=
  apply_eq_of_generalizingMap (Flat.generalizingMap f) genericPoint_specializes
    genericPoint_specializes

/-- A finite étale morphism from a nonempty scheme to a connected scheme is surjective. -/
theorem surjective_of_isFinite_of_etale [ConnectedSpace S] [Nonempty X] (f : X ⟶ S)
    [IsFinite f] [Etale f] : Function.Surjective f := by
  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  exact Set.range_eq_univ.1 (hcl.eq_univ ⟨f x, x, rfl⟩)

end Scheme

end Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible
