import Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatStatement
import Langlands.CommutativeAlgebra.Popescu.RegularParameterExtensionStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianEtaleCriterionStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1FiniteStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatSubalgebraStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianUnitEnlargementStatement
import Langlands.CommutativeAlgebra.Popescu.SmoothApproxTools
import Langlands.CommutativeAlgebra.EtaleFlatLocalDescentProof

/-! # The final step of the proof of Stacks Lemma 16.11.2 (07FH)

Given a flat local map `ψ' : D' → Λ_q/qⁿΛ_q` from an Artinian local `k`-algebra, elements
`g_x ∈ D'` with images `G_x ∈ Λ` whose residue differentials form a basis of `Ω_{κ_{D'}/k}`, and
elements of `D'` hitting a generating family `ν` of `q`, we produce the data of Lemma 16.11.2. -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace SmoothApprox

open IsLocalRing MvPolynomial

theorem final_step (hb : GeometricRegularityFlatStatement.{u})
    (hb2 : RegularParameterExtensionStatement.{u}) (hf : ArtinianEtaleCriterionStatement.{u})
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hreg : GeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime] {n : ℕ} (hn : 0 < n)
    [IsLocalRing (localTruncation q n)]
    (E : Finset (localTruncation q n))
    (D' : Type u) [CommRing D'] [IsLocalRing D'] [IsArtinianRing D'] [Algebra k D']
    [Algebra.EssFiniteType k D']
    (ψ' : D' →ₐ[k] localTruncation q n) [IsLocalHom ψ']
    (hψ'flat : (ψ' : D' →+* localTruncation q n).Flat)
    {t' : ℕ} (G' : Fin t' → Λ) (gD : Fin t' → D')
    (hGD : ∀ x, ψ' (gD x) = toLocalTruncation q n (G' x))
    (hli : LinearIndependent (ResidueField D')
      fun x => KaehlerDifferential.D k (ResidueField D') (residue D' (gD x)))
    (hsp : Submodule.span (ResidueField D')
      (Set.range fun x => KaehlerDifferential.D k (ResidueField D') (residue D' (gD x))) = ⊤)
    {d : ℕ} (ν : Fin d → Λ) (hν : Ideal.span (Set.range ν) = q) (aν : Fin d → D')
    (hνD : ∀ j, ψ' (aν j) = toLocalTruncation q n (ν j))
    (hE : (E : Set (localTruncation q n)) ⊆ Set.range ψ')
    (eL : ResidueField (localTruncation q n) ≃ₐ[k] q.ResidueField)
    (heL : ∀ y, eL (residue _ (Ideal.Quotient.mk _ y)) = residue (Localization.AtPrime q) y) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔭 : Ideal (MvPolynomial (Fin m) k))
      (_ : 𝔭.IsPrime) (h𝔭 : 𝔭 = q.comap (φ : MvPolynomial (Fin m) k →+* Λ)),
      𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      (Localization.localRingHom 𝔭 q φ h𝔭).Flat ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D)
        (_ : Algebra (localTruncation 𝔭 n) D) (ψ : D →+* localTruncation q n),
        EssentiallySmooth (localTruncation 𝔭 n) D ∧
        IsLocalHom ψ ∧ ψ.Flat ∧
        (∀ y : MvPolynomial (Fin m) k,
          ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
            toLocalTruncation q n (φ y)) ∧
        (E : Set (localTruncation q n)) ⊆ Set.range ψ := by
  classical
  have : IsNoetherianRing Λ := hreg.1
  have hψ'inj : Function.Injective ψ' :=
    injective_of_flat_of_isLocalHom (ψ' : D' →+* localTruncation q n) hψ'flat
  -- the residue field of `D'` inside `κ(q)`
  let θ : ResidueField D' →ₐ[k] q.ResidueField := eL.toAlgHom.comp (ResidueField.mapAlgHom ψ')
  have hθ : ∀ (x : D') (y : Λ), ψ' x = toLocalTruncation q n y →
      θ (residue D' x) = algebraMap Λ q.ResidueField y := by
    intro x y hxy
    have h1 : θ (residue D' x) = eL (residue _ (ψ' x)) := rfl
    rw [h1, hxy]
    exact heL _
  let eθ := θ.equivFieldRange
  have : Algebra.FiniteType D' (ResidueField D') :=
    .of_surjective (IsScalarTower.toAlgHom D' D' (ResidueField D')) residue_surjective
  have hkD : Algebra.EssFiniteType k (ResidueField D') := .comp k D' (ResidueField D')
  have hFG : θ.fieldRange.FG := IntermediateField.essFiniteType_iff.mp
    (Algebra.EssFiniteType.of_surjective eθ.toAlgHom eθ.surjective)
  -- applying 07E6 to any `φ₁` with `φ₁(X x) = G' x`
  have hbG : ∀ (φ₁ : MvPolynomial (Fin t') k →ₐ[k] Λ), (∀ i, φ₁ (X i) = G' i) →
      ∀ (𝔭₀ : Ideal (MvPolynomial (Fin t') k)) [𝔭₀.IsPrime]
        (h₀ : 𝔭₀ = q.comap (φ₁ : MvPolynomial (Fin t') k →+* Λ)),
        (Localization.localRingHom 𝔭₀ q φ₁ h₀).Flat ∧
          IsRegularLocalRing (Localization.AtPrime q ⧸
            𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp φ₁)) := by
    intro φ₁ hφ₁ 𝔭₀ _ h₀
    have hF : ∀ i, algebraMap Λ q.ResidueField (φ₁ (X i)) ∈ θ.fieldRange := fun i =>
      ⟨residue D' (gD i), by rw [hφ₁]; exact hθ _ _ (hGD i)⟩
    have hdiff : (fun i => KaehlerDifferential.D k θ.fieldRange ⟨_, hF i⟩) =
        fun i => KaehlerDifferential.D k θ.fieldRange (eθ (residue D' (gD i))) := by
      funext i
      congr 1
      apply Subtype.ext
      change algebraMap Λ q.ResidueField (φ₁ (X i)) = θ (residue D' (gD i))
      rw [hφ₁]
      exact (hθ _ _ (hGD i)).symm
    obtain ⟨h1, h2⟩ := kaehler_basis_of_algEquiv eθ _ hli hsp
    rw [← hdiff] at h1 h2
    exact hb k Λ p hreg q θ.fieldRange hFG t' φ₁ hF h1 h2 𝔭₀ h₀
  -- the first part of `φ`
  let φ₁ : MvPolynomial (Fin t') k →ₐ[k] Λ := aeval G'
  let 𝔭₀ : Ideal (MvPolynomial (Fin t') k) := q.comap (φ₁ : MvPolynomial (Fin t') k →+* Λ)
  have : 𝔭₀.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨-, hreg₀⟩ := hbG φ₁ (fun i => aeval_X _ _) 𝔭₀ rfl
  let I₀ := 𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp (φ₁ : _ →+* Λ))
  have : IsRegularLocalRing (Localization.AtPrime q ⧸ I₀) := hreg₀
  -- the images of `ν` generate the maximal ideal of `Λ_q/𝔭₀Λ_q`
  have hqν : q.map (algebraMap Λ (Localization.AtPrime q)) =
      Ideal.span (Set.range fun j => algebraMap Λ (Localization.AtPrime q) (ν j)) := by
    have h1 : (Ideal.span (Set.range ν)).map (algebraMap Λ (Localization.AtPrime q)) =
        Ideal.span (Set.range fun j => algebraMap Λ (Localization.AtPrime q) (ν j)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hν] at h1
    exact h1
  have hgen : Ideal.span (Set.range fun j => Ideal.Quotient.mk I₀
      (algebraMap Λ (Localization.AtPrime q) (ν j))) =
      maximalIdeal (Localization.AtPrime q ⧸ I₀) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I₀) Ideal.Quotient.mk_surjective,
      ← Localization.AtPrime.map_eq_maximalIdeal, hqν, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨σ, hσ⟩ := exists_select_maximalIdeal _ hgen
  let d₁ := (maximalIdeal (Localization.AtPrime q ⧸ I₀)).spanFinrank
  -- the full `φ`
  let φ : MvPolynomial (Fin (t' + d₁)) k →ₐ[k] Λ := aeval (Fin.append G' (ν ∘ σ))
  have hφX1 : ∀ i, φ (X (Fin.castAdd d₁ i)) = G' i := fun i => by
    simp only [φ, aeval_X, Fin.append_left]
  have hφX2 : ∀ j, φ (X (Fin.natAdd t' j)) = ν (σ j) := fun j => by
    simp only [φ, aeval_X, Fin.append_right, Function.comp_apply]
  have hφ₁eq : φ.comp (rename (Fin.castAdd d₁)) = φ₁ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, hφX1, φ₁, aeval_X]
  have h₀' : 𝔭₀ = q.comap (φ.comp (rename (Fin.castAdd d₁)) : MvPolynomial (Fin t') k →+* Λ) := by
    rw [hφ₁eq]
  obtain ⟨hflat₀, hreg₀'⟩ := hbG (φ.comp (rename (Fin.castAdd d₁)))
    (fun i => by simp only [AlgHom.comp_apply, rename_X, hφX1]) 𝔭₀ h₀'
  have hI : 𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp
      (φ.comp (rename (Fin.castAdd d₁)) : MvPolynomial (Fin t') k →+* Λ)) = I₀ := by
    show _ = 𝔭₀.map _
    have hcomp : (algebraMap Λ (Localization.AtPrime q)).comp
        (φ.comp (rename (Fin.castAdd d₁)) : MvPolynomial (Fin t') k →+* Λ) =
        (algebraMap Λ (Localization.AtPrime q)).comp (φ₁ : MvPolynomial (Fin t') k →+* Λ) := by
      rw [hφ₁eq]
    rw [hcomp]
  have : IsRegularLocalRing (Localization.AtPrime q ⧸ 𝔭₀.map
      ((algebraMap Λ (Localization.AtPrime q)).comp
        (φ.comp (rename (Fin.castAdd d₁)) : MvPolynomial (Fin t') k →+* Λ))) := hreg₀'
  have key := hb2 k Λ q t' d₁ φ 𝔭₀ h₀' hflat₀
  let 𝔭 : Ideal (MvPolynomial (Fin (t' + d₁)) k) := q.comap (φ : _ →+* Λ)
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hflat, hmax⟩ := key
    (fun j => by rw [hφX2, ← hν]; exact Ideal.subset_span ⟨σ j, rfl⟩)
    (spanFinrank_transport hI)
    (by
      simp only [hφX2]
      exact span_mk_transport hI (fun j => algebraMap Λ (Localization.AtPrime q) (ν (σ j))) hσ)
    𝔭 rfl
  refine ⟨t' + d₁, φ, 𝔭, inferInstance, rfl, hmax, hflat, ?_⟩
  -- the map `k[y] → D'`
  let gAll : Fin (t' + d₁) → D' := Fin.append gD (aν ∘ σ)
  let χ₀ : MvPolynomial (Fin (t' + d₁)) k →ₐ[k] D' := aeval gAll
  have hχ₀ : ∀ y, ψ' (χ₀ y) = toLocalTruncation q n (φ y) := by
    intro y
    have h : ψ'.comp χ₀ = (Ideal.Quotient.mkₐ k (maximalIdeal (Localization.AtPrime q) ^ n)).comp
        ((IsScalarTower.toAlgHom k Λ (Localization.AtPrime q)).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [AlgHom.comp_apply, χ₀, gAll, aeval_X, Fin.append_left, hGD, hφX1]
        rfl
      · simp only [AlgHom.comp_apply, χ₀, gAll, aeval_X, Fin.append_right, Function.comp_apply,
          hνD, hφX2]
        rfl
    exact AlgHom.congr_fun h y
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (χ₀ (y : MvPolynomial (Fin (t' + d₁)) k)) := by
    intro y
    apply isUnit_of_map_unit ψ'
    rw [hχ₀]
    have h2 : IsUnit (algebraMap Λ (Localization.AtPrime q) (φ y)) :=
      IsLocalization.map_units (Localization.AtPrime q) (⟨φ y, y.2⟩ : q.primeCompl)
    exact h2.map (Ideal.Quotient.mk _)
  let χ₁ : Localization.AtPrime 𝔭 →+* D' := IsLocalization.lift (M := 𝔭.primeCompl)
    (g := (χ₀ : MvPolynomial (Fin (t' + d₁)) k →+* D')) hunit
  have hχ₁alg : ∀ y, χ₁ (algebraMap _ (Localization.AtPrime 𝔭) y) = χ₀ y :=
    fun y => IsLocalization.lift_eq hunit y
  have hχ₁ : ∀ x, ψ' (χ₁ x) = Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)
      (Localization.localRingHom 𝔭 q φ rfl x) := by
    have h : (ψ' : D' →+* localTruncation q n).comp χ₁ =
        (Ideal.Quotient.mk _).comp (Localization.localRingHom 𝔭 q φ rfl) := by
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      refine RingHom.ext fun y => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [hχ₁alg, hχ₀, Localization.localRingHom_to_map]
      rfl
    exact fun x => RingHom.congr_fun h x
  have hle : (maximalIdeal (Localization.AtPrime 𝔭)).map (Localization.localRingHom 𝔭 q φ rfl) ≤
      maximalIdeal (Localization.AtPrime q) := map_maximalIdeal_le _
  have hkill : ∀ x ∈ maximalIdeal (Localization.AtPrime 𝔭) ^ n, χ₁ x = 0 := by
    intro x hx
    apply hψ'inj
    rw [hχ₁, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := Ideal.mem_map_of_mem (Localization.localRingHom 𝔭 q φ rfl) hx
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle n h1
  let χ : localTruncation 𝔭 n →+* D' := Ideal.Quotient.lift _ χ₁ hkill
  let _ : Algebra (localTruncation 𝔭 n) D' := χ.toAlgebra
  have hχgen : ∀ y, χ (toLocalTruncation 𝔭 n y) = χ₀ y := fun y => by
    show Ideal.Quotient.lift _ χ₁ hkill (Ideal.Quotient.mk _ (algebraMap _ _ y)) = _
    rw [Ideal.Quotient.lift_mk]
    exact hχ₁alg y
  -- the truncated map `P → Λ_q/qⁿΛ_q` and the local structure
  have : IsLocalRing (localTruncation 𝔭 n) := isLocalRing_localTruncation 𝔭 hn
  have : IsArtinianRing (localTruncation 𝔭 n) := isArtinianRing_localTruncation 𝔭
  obtain ⟨χP, hχPflat, hχPmk⟩ := exists_flat_truncation_map (R := MvPolynomial (Fin (t' + d₁)) k)
    (Λ := Λ) 𝔭 q n (φ : MvPolynomial (Fin (t' + d₁)) k →+* Λ) rfl hflat hmax
  have hψχ : ∀ z, ψ' (χ z) = χP z := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hχPmk]
    exact hχ₁ x
  have hgmax : (maximalIdeal (Localization.AtPrime 𝔭)).map (Localization.localRingHom 𝔭 q φ rfl) =
      maximalIdeal (Localization.AtPrime q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭), Ideal.map_map]
    have : (Localization.localRingHom 𝔭 q φ rfl).comp (algebraMap _ (Localization.AtPrime 𝔭)) =
        (algebraMap Λ (Localization.AtPrime q)).comp
          (φ : MvPolynomial (Fin (t' + d₁)) k →+* Λ) :=
      RingHom.ext fun x => Localization.localRingHom_to_map 𝔭 q φ rfl x
    rw [this, hmax]
  have hmapP : (maximalIdeal (localTruncation 𝔭 n)).map χP =
      maximalIdeal (localTruncation q n) := by
    rw [← map_maximalIdeal_localTruncation 𝔭 (n := n), Ideal.map_map]
    have : χP.comp (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime 𝔭) ^ n)) =
        (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)).comp
          (Localization.localRingHom 𝔭 q φ rfl) := RingHom.ext hχPmk
    rw [this, ← Ideal.map_map, hgmax, map_maximalIdeal_localTruncation q]
  have hχloc : IsLocalHom (algebraMap (localTruncation 𝔭 n) D') := ⟨fun x hx => by
    by_contra h
    have hxm : x ∈ maximalIdeal (localTruncation 𝔭 n) := (mem_maximalIdeal _).mpr h
    have h2 : χP x ∈ maximalIdeal (localTruncation q n) := hmapP ▸ Ideal.mem_map_of_mem χP hxm
    rw [← hψχ] at h2
    exact (mem_maximalIdeal _).mp h2 (hx.map ψ')⟩
  have hkP : ∀ c : k, algebraMap k (localTruncation 𝔭 n) c =
      toLocalTruncation 𝔭 n (algebraMap k (MvPolynomial (Fin (t' + d₁)) k) c) := by
    intro c
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (t' + d₁)) k) (localTruncation 𝔭 n)]
    rfl
  have : IsScalarTower k (localTruncation 𝔭 n) D' :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := localTruncation 𝔭 n) (A := D') fun c => by
      show algebraMap k D' c = χ (algebraMap k (localTruncation 𝔭 n) c)
      rw [hkP, hχgen, AlgHom.commutes]
  have : Algebra.EssFiniteType (localTruncation 𝔭 n) D' := .of_comp k _ D'
  -- flatness of `P → D'` by descent along the faithfully flat `D' → Λ_q/qⁿΛ_q`
  let _ : Algebra D' (localTruncation q n) := (ψ' : D' →+* localTruncation q n).toAlgebra
  let _ : Algebra (localTruncation 𝔭 n) (localTruncation q n) := χP.toAlgebra
  have : IsScalarTower (localTruncation 𝔭 n) D' (localTruncation q n) :=
    .of_algebraMap_eq fun z => (hψχ z).symm
  have : Module.Flat D' (localTruncation q n) := hψ'flat
  have : IsLocalHom (algebraMap D' (localTruncation q n)) := ⟨IsLocalHom.map_nonunit (f := ψ')⟩
  have : Module.FaithfullyFlat D' (localTruncation q n) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat (localTruncation 𝔭 n) (localTruncation q n) := hχPflat
  have : Module.Flat (localTruncation 𝔭 n) D' :=
    Langlands.CommutativeAlgebra.flat_of_flat_of_faithfullyFlat
      (localTruncation 𝔭 n) D' (localTruncation q n)
  -- `𝔪_P D' = 𝔪_{D'}`
  have hmaxD : (maximalIdeal (localTruncation 𝔭 n)).map (algebraMap (localTruncation 𝔭 n) D') =
      maximalIdeal D' := by
    rw [← comap_map_of_flat_of_isLocalHom (ψ' : D' →+* localTruncation q n) hψ'flat
      ((maximalIdeal _).map (algebraMap (localTruncation 𝔭 n) D'))]
    rw [Ideal.map_map]
    have : (ψ' : D' →+* localTruncation q n).comp (algebraMap (localTruncation 𝔭 n) D') = χP :=
      RingHom.ext hψχ
    rw [this, hmapP]
    exact maximalIdeal_comap _
  -- separability of the residue field extension
  have hsep : Algebra.IsSeparable (ResidueField (localTruncation 𝔭 n)) (ResidueField D') := by
    have hres : ∀ x : Fin t', ∃ c, algebraMap (ResidueField (localTruncation 𝔭 n))
        (ResidueField D') c = residue D' (gD x) := by
      intro x
      refine ⟨residue _ (toLocalTruncation 𝔭 n (X (Fin.castAdd d₁ x))), ?_⟩
      rw [ResidueField.algebraMap_residue]
      congr 1
      show χ (toLocalTruncation 𝔭 n _) = _
      rw [hχgen]
      simp only [χ₀, gAll, aeval_X, Fin.append_left]
    have hzero : ∀ ω : Ω[ResidueField D'⁄ResidueField (localTruncation 𝔭 n)], ω = 0 := by
      intro ω
      obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective k
        (ResidueField (localTruncation 𝔭 n)) (ResidueField D') ω
      have hω₀ : ω₀ ∈ Submodule.span (ResidueField D')
          (Set.range fun x => KaehlerDifferential.D k (ResidueField D') (residue D' (gD x))) :=
        hsp ▸ Submodule.mem_top
      induction hω₀ using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        rw [KaehlerDifferential.map_D]
        obtain ⟨c, hc⟩ := hres x
        rw [Algebra.algebraMap_self_apply, ← hc, Derivation.map_algebraMap]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul a z _ hz => rw [LinearMap.map_smul, hz, smul_zero]
    have : Subsingleton Ω[ResidueField D'⁄ResidueField (localTruncation 𝔭 n)] :=
      ⟨fun a b => by rw [hzero a, hzero b]⟩
    have : Algebra.FormallyUnramified (ResidueField (localTruncation 𝔭 n)) (ResidueField D') :=
      ⟨this⟩
    have : Algebra.EssFiniteType (ResidueField (localTruncation 𝔭 n)) (ResidueField D') :=
      .of_comp k _ _
    exact Algebra.FormallyUnramified.isSeparable _ _
  have hES := hf (localTruncation 𝔭 n) D' hmaxD hsep
  refine ⟨D', inferInstance, inferInstance, inferInstance, inferInstance,
    (ψ' : D' →+* localTruncation q n), hES, ⟨IsLocalHom.map_nonunit (f := ψ')⟩, hψ'flat,
    fun y => ?_, hE⟩
  show ψ' (χ (toLocalTruncation 𝔭 n y)) = _
  rw [hχgen, hχ₀]

/-- Stacks Lemma 16.11.2 (07FH) from its ingredients: 07E5 (finiteness of `H₁`), 07E6, the
"property (1)" step, Lemma 16.11.1, the refined enlargement of Lemma 16.11.3, and the Artinian
étale criterion. -/
theorem artinianSmoothApproximation_of (ha : GeometricRegularityH1FiniteStatement.{u})
    (hb : GeometricRegularityFlatStatement.{u}) (hb2 : RegularParameterExtensionStatement.{u})
    (hc : ArtinianFlatSubalgebraStatement.{u}) (he : ArtinianUnitEnlargementStatement.{u})
    (hf : ArtinianEtaleCriterionStatement.{u}) :
    ArtinianSmoothApproximationStatement.{u} := by
  intro k Λ _ _ _ p _ _ hreg q _ n hn E
  classical
  have : IsNoetherianRing Λ := hreg.1
  have : IsLocalRing (localTruncation q n) := isLocalRing_localTruncation q hn
  have : IsArtinianRing (localTruncation q n) := isArtinianRing_localTruncation q
  obtain ⟨eL, heL⟩ := exists_residueField_equiv q (n := n) k
  have hH1 := h1_finite_of_algEquiv eL.symm (ha k Λ p hreg q)
  -- generators of `q`
  obtain ⟨d, ν, hν⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian q)
  -- the subalgebra `A` from Lemma 16.11.1
  obtain ⟨A, hAloc, hEA, hAart, hAeft, hAflat, hAmax⟩ := hc k (localTruncation q n) p hH1
    (E ∪ Finset.univ.image fun j => toLocalTruncation q n (ν j))
  have hAlocal : IsLocalHom A.val := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal _).mpr h
    have h2 : algebraMap A (localTruncation q n) a ∈ maximalIdeal (localTruncation q n) :=
      hAmax ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).mp h2 ha⟩
  have hAflat' : (A.val : A →+* localTruncation q n).Flat := by
    have h := (RingHom.flat_algebraMap_iff (R := A) (S := localTruncation q n)).mpr hAflat
    exact h
  -- a differential basis of the residue field of `A`
  obtain ⟨t, b, hbli, hbsp⟩ := exists_kaehler_basis k A
  -- a common denominator `s`
  choose y hy using fun i => Ideal.Quotient.mk_surjective (A.val (b i))
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite q.primeCompl y
  choose lam hlam using hs
  let ℓ := toLocalTruncation q n (s : Λ)
  have hℓ : IsUnit ℓ :=
    (IsLocalization.map_units (Localization.AtPrime q) s).map (Ideal.Quotient.mk _)
  have hlamb : ∀ i, toLocalTruncation q n (lam i) = ℓ * A.val (b i) := by
    intro i
    show Ideal.Quotient.mk _ (algebraMap Λ _ (lam i)) = _
    rw [hlam i, Algebra.smul_def, map_mul, hy]
    rfl
  -- the enlargement absorbing `s`
  obtain ⟨D', _, _, _, _, _, ι, ψ', hψ'loc, hψ'flat, hcomp, ⟨Q, u, hQ, hu, hdu⟩, r, v, hv, hli,
    hsp⟩ := he k A (localTruncation q n) p A.val hAlocal hAflat' ℓ hℓ t b hbli hbsp
  have hιb : ∀ a : A, ψ' (ι a) = A.val a := fun a => AlgHom.congr_fun hcomp a
  have huunit : IsUnit u := isUnit_of_map_unit ψ' u (hu ▸ hℓ.pow Q)
  -- the families `G'` in `Λ` and `gD` in `D'`
  let G' : Fin (t + r) → Λ := fun x =>
    Sum.elim (fun i => lam i * (s : Λ) ^ (Q - 1)) (fun _ => (s : Λ)) (finSumFinEquiv.symm x)
  let gD : Fin (t + r) → D' := fun x =>
    Sum.elim (fun i => ι (b i) * u) v (finSumFinEquiv.symm x)
  have hGD : ∀ x, ψ' (gD x) = toLocalTruncation q n (G' x) := by
    intro x
    obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
    rcases h : finSumFinEquiv.symm x with i | j
    · simp only [gD, G', h, Sum.elim_inl, map_mul, map_pow, hlamb, hιb, hu,
        Nat.add_sub_cancel]
      ring
    · simp only [gD, G', h, Sum.elim_inr, hv]
      rfl
  -- the differential basis for `gD`
  have hD : ∀ a : D', KaehlerDifferential.D k (ResidueField D') (residue D' (a * u)) =
      residue D' u • KaehlerDifferential.D k (ResidueField D') (residue D' a) := by
    intro a
    rw [map_mul, Derivation.leibniz, hdu, smul_zero, zero_add]
  let w : Fin t ⊕ Fin r → Ω[ResidueField D'⁄k] :=
    Sum.elim (fun i => KaehlerDifferential.D k (ResidueField D') (residue D' (ι (b i))))
      (fun j => KaehlerDifferential.D k (ResidueField D') (residue D' (v j)))
  let c : Fin t ⊕ Fin r → ResidueField D' := Sum.elim (fun _ => residue D' u) (fun _ => 1)
  have hc0 : ∀ z, c z ≠ 0 := by
    rintro (i | j)
    · exact (residue_ne_zero_iff_isUnit _).mpr huunit
    · exact one_ne_zero
  obtain ⟨hli₂, hsp₂⟩ := basis_smul w c hc0 hli hsp
  have hfam : (fun z => c z • w z) = fun z => KaehlerDifferential.D k (ResidueField D')
      (residue D' (Sum.elim (fun i => ι (b i) * u) v z)) := by
    funext z
    rcases z with i | j
    · simp only [c, w, Sum.elim_inl, hD]
    · simp only [c, w, Sum.elim_inr, one_smul]
  rw [hfam] at hli₂ hsp₂
  have hli₃ : LinearIndependent (ResidueField D')
      fun x => KaehlerDifferential.D k (ResidueField D') (residue D' (gD x)) :=
    hli₂.comp _ finSumFinEquiv.symm.injective
  have hsp₃ : Submodule.span (ResidueField D')
      (Set.range fun x => KaehlerDifferential.D k (ResidueField D') (residue D' (gD x))) = ⊤ := by
    rw [← hsp₂]
    congr 1
    exact finSumFinEquiv.symm.surjective.range_comp (fun z => KaehlerDifferential.D k
      (ResidueField D') (residue D' (Sum.elim (fun i => ι (b i) * u) v z)))
  -- the generators of `q` inside `D'`
  have hνA : ∀ j, toLocalTruncation q n (ν j) ∈ A := fun j =>
    hEA (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  let aν : Fin d → D' := fun j => ι ⟨_, hνA j⟩
  have hνD : ∀ j, ψ' (aν j) = toLocalTruncation q n (ν j) := fun j => hιb _
  have hE : (E : Set (localTruncation q n)) ⊆ Set.range ψ' := by
    intro e he'
    have heA : e ∈ A := hEA (Finset.mem_union_left _ he')
    exact ⟨ι ⟨e, heA⟩, hιb _⟩
  exact final_step hb hb2 hf p hreg q hn E D' ψ' hψ'flat G' gD hGD hli₃ hsp₃ ν hν aν hνD hE
    eL heL

end SmoothApprox

end Langlands.CommutativeAlgebra.Popescu
