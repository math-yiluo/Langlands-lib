import Langlands.AlgebraicGeometry.SmoothRelationGoodPointEtale
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointMono
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointEtaleImage
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointConverse

/-! # Every orbit of a smooth relation contains a good point

Let `t s : R ⟶ U` be morphisms of schemes such that `(t, s) : R ⟶ U × U` is a monomorphism, `s`
is smooth, and `e : U ⟶ R` is a common section. For every `x : U` there is `r : R` with
`s r = x` such that `t r` is a good point.
-/

universe u

open CategoryTheory Limits IsLocalRing

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

open _root_.AlgebraicGeometry

variable {U R : Scheme.{u}}

/-- On an affine chart, `f` maps the point of a prime `P` to the point of its contraction. -/
lemma apply_fromSpec (f : R ⟶ U) {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens}
    (hW : IsAffineOpen W) (hWf : W ≤ f ⁻¹ᵁ V) (P : PrimeSpectrum Γ(R, W)) :
    f (hW.fromSpec P) = hV.fromSpec (PrimeSpectrum.comap (f.appLE V W hWf).hom P) := by
  change (hW.fromSpec ≫ f) P = (Spec.map (f.appLE V W hWf) ≫ hV.fromSpec) P
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWf]

/-- **Existence of good points.** If `(t, s)` is a monomorphism, `s` is smooth and `e` is a
common section of `t` and `s`, then every `x : U` is `s r` for some `r : R` such that `t r` is a
good point. -/
theorem exists_isGoodPoint (t s : R ⟶ U) (hmono : Mono (prod.lift t s)) (hs : Smooth s)
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U) (x : U) :
    ∃ r : R, s r = x ∧ IsGoodPoint t s e (t r) := by
  classical
  have : Smooth s := hs
  have hsx : s (e x) = x := apply_apply_of_comp_eq_id e hes x
  have htx : t (e x) = x := apply_apply_of_comp_eq_id e het x
  -- affine charts `V ∋ x` and `W ∋ e x` with `W ⊆ s⁻¹ V ∩ t⁻¹ V`
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : U.Opens) from trivial)
  have hexV : e x ∈ s ⁻¹ᵁ V ⊓ t ⁻¹ᵁ V :=
    ⟨show s (e x) ∈ V by rwa [hsx], show t (e x) ∈ V by rwa [htx]⟩
  obtain ⟨W, hW, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset hexV
  have hWs : W ≤ s ⁻¹ᵁ V := fun r hr ↦ (hWsub hr).1
  have hWt : W ≤ t ⁻¹ᵁ V := fun r hr ↦ (hWsub hr).2
  let : Algebra Γ(U, V) Γ(R, W) := (s.appLE V W hWs).hom.toAlgebra
  have hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom := rfl
  have : Algebra.Smooth Γ(U, V) Γ(R, W) :=
    HasRingHomProperty.appLE @Smooth s hs ⟨V, hV⟩ ⟨W, hW⟩ hWs
  -- étale coordinates at the prime of `e x`
  obtain ⟨p0, hp0⟩ : ∃ p, p = hW.primeIdealOf ⟨e x, hxW⟩ := ⟨_, rfl⟩
  have hp0x : hW.fromSpec p0 = e x := hp0 ▸ hW.fromSpec_primeIdealOf _
  obtain ⟨ι, hι, g, hg⟩ := exists_etale_coordinates (t.appLE V W hWt).hom
    (span_targetDifferentials_eq_top_of_mono hmono hV hW hWs hWt hσ) p0.asIdeal
  let : Algebra (MvPolynomial ι Γ(U, V)) Γ(R, W) :=
    (MvPolynomial.aeval ((t.appLE V W hWt).hom ∘ g)).toRingHom.toAlgebra
  have : IsScalarTower Γ(U, V) (MvPolynomial ι Γ(U, V)) Γ(R, W) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (MvPolynomial.aeval_C _ a).symm
  have hX : ∀ i, algebraMap (MvPolynomial ι Γ(U, V)) Γ(R, W) (MvPolynomial.X i) =
      (t.appLE V W hWt).hom (g i) := fun i ↦ MvPolynomial.aeval_X _ i
  have : Algebra.IsEtaleAt (MvPolynomial ι Γ(U, V)) p0.asIdeal := hg hX
  have : Algebra.FinitePresentation (MvPolynomial ι Γ(U, V)) Γ(R, W) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation Γ(U, V) _ _
  obtain ⟨c, hcq, hc⟩ :=
    Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial ι Γ(U, V)) p0.asIdeal
  -- the open set of primes `P` with `c ∉ P` and `e (t P) ∈ D(c)`
  have hmem : ∀ P : PrimeSpectrum Γ(R, W), hW.fromSpec P ∈ R.basicOpen c ↔ c ∉ P.asIdeal := by
    intro P
    change P ∈ hW.fromSpec ⁻¹ᵁ R.basicOpen c ↔ _
    rw [hW.fromSpec_preimage_basicOpen]
    rfl
  let O : Set (PrimeSpectrum Γ(R, W)) :=
    (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum Γ(R, W))) ∩
      {P | e (t (hW.fromSpec P)) ∈ R.basicOpen c}
  have hO : IsOpen O := (PrimeSpectrum.basicOpen c).isOpen.inter
    ((R.basicOpen c).isOpen.preimage
      (e.continuous.comp (t.continuous.comp hW.fromSpec.continuous)))
  have hp0O : p0 ∈ O := by
    refine ⟨hcq, ?_⟩
    change e (t (hW.fromSpec p0)) ∈ R.basicOpen c
    rw [hp0x, htx, ← hp0x]
    exact (hmem p0).mpr hcq
  -- a prime over the same point of `U` with simple integer equations
  obtain ⟨P, hPO, hPC, hPsimple⟩ :=
    exists_prime_simpleIntegerRoots_of_etale_away (A := Γ(U, V)) (ι := ι) c O hO
      Set.inter_subset_left p0 hp0O
  have hcomp : (algebraMap (MvPolynomial ι Γ(U, V)) Γ(R, W)).comp MvPolynomial.C =
      (s.appLE V W hWs).hom := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    rfl
  rw [hcomp] at hPC
  refine ⟨hW.fromSpec P, ?_, ?_⟩
  · have : PrimeSpectrum.comap (s.appLE V W hWs).hom P =
        PrimeSpectrum.comap (s.appLE V W hWs).hom p0 := PrimeSpectrum.ext hPC
    rw [apply_fromSpec s hV hW hWs P, this, ← apply_fromSpec s hV hW hWs p0, hp0x, hsx]
  · set y := t (hW.fromSpec P) with hy
    have hey : e y ∈ R.basicOpen c := hPO.2
    have heyW : e y ∈ W := R.basicOpen_le c hey
    have hP''x : hW.fromSpec (hW.primeIdealOf ⟨e y, heyW⟩) = e y :=
      hW.fromSpec_primeIdealOf _
    have hcP'' : c ∉ (hW.primeIdealOf ⟨e y, heyW⟩).asIdeal := by
      rw [← hmem, hP''x]
      exact hey
    have hsub := (Algebra.basicOpen_subset_etaleLocus_iff
      (R := MvPolynomial ι Γ(U, V)) (A := Γ(R, W)) (f := c)).mpr inferInstance
    have : Algebra.IsEtaleAt (MvPolynomial ι Γ(U, V))
        (hW.primeIdealOf ⟨e y, heyW⟩).asIdeal := hsub hcP''
    have hθP : (hW.primeIdealOf ⟨e y, heyW⟩).asIdeal.comap (t.appLE V W hWt).hom =
        P.asIdeal.comap (t.appLE V W hWt).hom := by
      have h1 : hV.fromSpec (PrimeSpectrum.comap (t.appLE V W hWt).hom
          (hW.primeIdealOf ⟨e y, heyW⟩)) =
          hV.fromSpec (PrimeSpectrum.comap (t.appLE V W hWt).hom P) := by
        rw [← apply_fromSpec t hV hW hWt, ← apply_fromSpec t hV hW hWt, hP''x,
          apply_apply_of_comp_eq_id e het]
      exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective h1)
    have hθaeval : ∀ (a : Γ(U, V)) (Q : Polynomial ℤ),
        (t.appLE V W hWt).hom (Polynomial.aeval a Q) =
          Polynomial.aeval ((t.appLE V W hWt).hom a) Q := fun a Q ↦
      (Polynomial.aeval_algHom_apply (t.appLE V W hWt).hom.toIntAlgHom a Q).symm
    refine isGoodPoint_of_simpleIntegerRoots het hes y hV hW heyW hWs hWt hσ _ rfl g
      (residueSpan_eq_top_of_isEtaleAt (t.appLE V W hWt).hom g hX _) fun i ↦ ?_
    obtain ⟨Q, hQ, hdQ⟩ := hPsimple i
    rw [hX] at hQ hdQ
    refine ⟨Q, ?_, ?_⟩
    · rw [hθP, Ideal.mem_comap, hθaeval]
      exact hQ
    · rw [hθP, Ideal.mem_comap, hθaeval]
      exact hdQ

/-- A point of `R` over `x` (via `s`) whose image under `t` is good, chosen by
`exists_isGoodPoint`. -/
noncomputable def goodPointOver (t s : R ⟶ U) (hmono : Mono (prod.lift t s)) (hs : Smooth s)
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U) (x : U) : R :=
  (exists_isGoodPoint t s hmono hs e het hes x).choose

lemma apply_goodPointOver (t s : R ⟶ U) (hmono : Mono (prod.lift t s)) (hs : Smooth s)
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U) (x : U) :
    s (goodPointOver t s hmono hs e het hes x) = x :=
  (exists_isGoodPoint t s hmono hs e het hes x).choose_spec.1

lemma isGoodPoint_goodPointOver (t s : R ⟶ U) (hmono : Mono (prod.lift t s)) (hs : Smooth s)
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U) (x : U) :
    IsGoodPoint t s e (t (goodPointOver t s hmono hs e het hes x)) :=
  (exists_isGoodPoint t s hmono hs e het hes x).choose_spec.2

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
