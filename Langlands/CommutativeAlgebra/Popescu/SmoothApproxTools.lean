import Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth
import Mathlib

/-! # Tools for the assembly of Stacks Lemma 16.11.2 (07FH) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace SmoothApprox

open IsLocalRing

section FlatLocal

variable {D E : Type*} [CommRing D] [CommRing E] [IsLocalRing D] [IsLocalRing E]

/-- A flat local homomorphism of local rings is injective. -/
theorem injective_of_flat_of_isLocalHom (ψ : D →+* E) [IsLocalHom ψ] (hψ : ψ.Flat) :
    Function.Injective ψ := by
  let := ψ.toAlgebra
  have : Module.Flat D E := hψ
  have : IsLocalHom (algebraMap D E) := ‹IsLocalHom ψ›
  have : Module.FaithfullyFlat D E := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective D E

/-- Along a flat local homomorphism of local rings, ideals are contracted from their extensions. -/
theorem comap_map_of_flat_of_isLocalHom (ψ : D →+* E) [IsLocalHom ψ] (hψ : ψ.Flat)
    (I : Ideal D) : (I.map ψ).comap ψ = I := by
  let := ψ.toAlgebra
  have : Module.Flat D E := hψ
  have : IsLocalHom (algebraMap D E) := ‹IsLocalHom ψ›
  have : Module.FaithfullyFlat D E := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

end FlatLocal

section Kaehler

variable {k F₁ F₂ : Type*} [Field k] [Field F₁] [Field F₂] [Algebra k F₁] [Algebra k F₂]

/-- A differential basis is transported along a `k`-algebra isomorphism of fields. -/
theorem kaehler_basis_of_algEquiv (e : F₁ ≃ₐ[k] F₂) {ι : Type*} (x : ι → F₁)
    (hli : LinearIndependent F₁ (fun i => KaehlerDifferential.D k F₁ (x i)))
    (hsp : Submodule.span F₁ (Set.range fun i => KaehlerDifferential.D k F₁ (x i)) = ⊤) :
    LinearIndependent F₂ (fun i => KaehlerDifferential.D k F₂ (e (x i))) ∧
      Submodule.span F₂ (Set.range fun i => KaehlerDifferential.D k F₂ (e (x i))) = ⊤ := by
  let : Algebra F₁ F₂ := e.toRingHom.toAlgebra
  let : Algebra F₂ F₁ := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k F₁ F₂ := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower k F₂ F₁ := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have hf : ∀ y, KaehlerDifferential.map k k F₁ F₂ (KaehlerDifferential.D k F₁ y) =
      KaehlerDifferential.D k F₂ (e y) := fun y => KaehlerDifferential.map_D k k F₁ F₂ y
  have hg : ∀ y, KaehlerDifferential.map k k F₂ F₁ (KaehlerDifferential.D k F₂ y) =
      KaehlerDifferential.D k F₁ (e.symm y) := fun y => KaehlerDifferential.map_D k k F₂ F₁ y
  constructor
  · apply LinearIndependent.of_comp (KaehlerDifferential.map k k F₂ F₁)
    have h1 : (KaehlerDifferential.map k k F₂ F₁) ∘
        (fun i => KaehlerDifferential.D k F₂ (e (x i))) =
        fun i => KaehlerDifferential.D k F₁ (x i) := by
      funext i
      simp only [Function.comp_apply, hg, AlgEquiv.symm_apply_apply]
    rw [h1]
    have hinj : Function.Injective fun r : F₂ => r • (1 : F₁) := by
      intro a b hab
      simp only [Algebra.smul_def, mul_one] at hab
      exact e.symm.injective hab
    exact LinearIndependent.restrict_scalars hinj hli
  · rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hmem : ∀ z ∈ Submodule.span F₁ (Set.range fun i => KaehlerDifferential.D k F₁ (x i)),
        KaehlerDifferential.map k k F₁ F₂ z ∈
          Submodule.span F₂ (Set.range fun i => KaehlerDifferential.D k F₂ (e (x i))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [hf]
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [LinearMap.map_smul, ← algebraMap_smul F₂ c]
        exact Submodule.smul_mem _ _ ha
    have := hmem (KaehlerDifferential.D k F₁ (e.symm y)) (hsp ▸ Submodule.mem_top)
    rw [hf, AlgEquiv.apply_symm_apply] at this
    exact this

end Kaehler

/-- Rescaling a basis family by nonzero scalars gives a basis family. -/
theorem basis_smul {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] (w : ι → V)
    (c : ι → F) (hc : ∀ i, c i ≠ 0) (hli : LinearIndependent F w)
    (hsp : Submodule.span F (Set.range w) = ⊤) :
    LinearIndependent F (fun i => c i • w i) ∧
      Submodule.span F (Set.range fun i => c i • w i) = ⊤ := by
  constructor
  · have := hli.units_smul (fun i => Units.mk0 (c i) (hc i))
    convert this using 1
    funext i
    rfl
  · rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : w i = (c i)⁻¹ • (c i • w i) := by rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Finiteness of `H₁` of the naive cotangent complex transfers along an isomorphism of fields. -/
theorem h1_finite_of_algEquiv {k K F : Type u} [Field k] [Field K] [Field F] [Algebra k K]
    [Algebra k F] (e : K ≃ₐ[k] F) (hK : Module.Finite K (Algebra.H1Cotangent k K)) :
    Module.Finite F (Algebra.H1Cotangent k F) := by
  let : Algebra K F := e.toRingHom.toAlgebra
  let : Algebra F K := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k K F := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have hs : Function.Surjective (Algebra.H1Cotangent.map k k K F) := fun x =>
    ⟨(Algebra.H1Cotangent.mapEquiv k K F e).symm x, (Algebra.H1Cotangent.mapEquiv k K F e).apply_symm_apply x⟩
  have : Module.Finite K (Algebra.H1Cotangent k F) := Module.Finite.of_surjective _ hs
  exact Module.Finite.of_restrictScalars_finite K F _

section Truncation

variable {Λ : Type u} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] {n : ℕ}

theorem isLocalRing_localTruncation (hn : 0 < n) : IsLocalRing (localTruncation q n) := by
  have hne : maximalIdeal (Localization.AtPrime q) ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (Ideal.pow_le_self hn.ne')
  have : Nontrivial (localTruncation q n) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

variable [IsLocalRing (localTruncation q n)]

theorem comap_maximalIdeal_localTruncation :
    (maximalIdeal (localTruncation q n)).comap
      (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)) =
      maximalIdeal (Localization.AtPrime q) := by
  have : ((maximalIdeal (localTruncation q n)).comap
      (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  exact IsLocalRing.eq_maximalIdeal this

theorem map_maximalIdeal_localTruncation :
    (maximalIdeal (Localization.AtPrime q)).map
      (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)) =
      maximalIdeal (localTruncation q n) := by
  have h := Ideal.map_comap_of_surjective
    (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)) Ideal.Quotient.mk_surjective
    (maximalIdeal (localTruncation q n))
  rw [comap_maximalIdeal_localTruncation q] at h
  exact h

instance isLocalHom_mk_localTruncation :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n)) := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hxm : x ∈ maximalIdeal (Localization.AtPrime q) := (mem_maximalIdeal _).mpr h
  rw [← comap_maximalIdeal_localTruncation q (n := n)] at hxm
  exact (mem_maximalIdeal _).mp hxm hx

theorem isArtinianRing_localTruncation [IsNoetherianRing Λ] :
    IsArtinianRing (localTruncation q n) := by
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n, ?_⟩
  rw [← map_maximalIdeal_localTruncation q (n := n), ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

/-- The residue field of `Λ_q/qⁿΛ_q` is `κ(q)`. -/
theorem exists_residueField_equiv (k : Type*) [Field k] [Algebra k Λ] :
    ∃ e : ResidueField (localTruncation q n) ≃ₐ[k] q.ResidueField,
      ∀ y : Localization.AtPrime q,
        e (residue _ (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q) ^ n) y)) =
          residue _ y := by
  let π := Ideal.Quotient.mkₐ k (maximalIdeal (Localization.AtPrime q) ^ n)
  have : IsLocalHom π := ⟨(isLocalHom_mk_localTruncation q (n := n)).map_nonunit⟩
  let φR := ResidueField.mapAlgHom π
  have hsurj : Function.Surjective φR := by
    intro z
    obtain ⟨w, rfl⟩ := residue_surjective z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    exact ⟨residue _ y, rfl⟩
  let e := AlgEquiv.ofBijective φR ⟨φR.toRingHom.injective, hsurj⟩
  refine ⟨e.symm, fun y => ?_⟩
  rw [AlgEquiv.symm_apply_eq]
  rfl

end Truncation

/-- A local ring essentially of finite type over a field `k` has elements whose residue classes
have differentials forming a basis of `Ω_{κ/k}`. -/
theorem exists_kaehler_basis (k A : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.EssFiniteType k A] :
    ∃ (t : ℕ) (b : Fin t → A),
      LinearIndependent (ResidueField A)
        (fun i => KaehlerDifferential.D k (ResidueField A) (residue A (b i))) ∧
      Submodule.span (ResidueField A)
        (Set.range fun i => KaehlerDifferential.D k (ResidueField A) (residue A (b i))) = ⊤ := by
  have : Algebra.FiniteType A (ResidueField A) :=
    .of_surjective (IsScalarTower.toAlgHom A A (ResidueField A))
      residue_surjective
  have : Algebra.EssFiniteType k (ResidueField A) := .comp k A (ResidueField A)
  let v : A → Ω[ResidueField A⁄k] := fun a => KaehlerDifferential.D k _ (residue A a)
  have hv : Submodule.span (ResidueField A) (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField A) v
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  let eκ := Fintype.equivFin κ
  refine ⟨Fintype.card κ, a ∘ eκ.symm, ?_, ?_⟩
  · exact hli.comp eκ.symm eκ.symm.injective
  · rw [← hv, ← hsp]
    congr 1
    ext ω
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨eκ.symm i, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨eκ j, by simp [v]⟩

/-- In a Noetherian local ring whose maximal ideal is generated by a finite family, a subfamily
of `spanFinrank` elements generates the maximal ideal. -/
theorem exists_select_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {d : ℕ} (f : Fin d → R) (hf : Ideal.span (Set.range f) = maximalIdeal R) :
    ∃ σ : Fin (maximalIdeal R).spanFinrank → Fin d,
      Ideal.span (Set.range (f ∘ σ)) = maximalIdeal R := by
  have hfm : ∀ i, f i ∈ maximalIdeal R := fun i => hf ▸ Ideal.subset_span ⟨i, rfl⟩
  let g : Fin d → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩
  -- spans of subfamilies of `f` and of `g`
  have key : ∀ (κ : Type) (a : κ → Fin d),
      Submodule.span (ResidueField R) (Set.range (g ∘ a)) = ⊤ ↔
        Ideal.span (Set.range (f ∘ a)) = maximalIdeal R := by
    intro κ a
    have h1 : Set.range (g ∘ a) = (maximalIdeal R).toCotangent ''
        Set.range (fun j => (⟨f (a j), hfm (a j)⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]; rfl
    rw [h1, CotangentSpace.span_image_eq_top_iff]
    constructor
    · intro h
      have h2 := congrArg (Submodule.map (maximalIdeal R).subtype) h
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h2
      exact h2
    · intro h
      apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact h
  have hg : Submodule.span (ResidueField R) (Set.range g) = ⊤ :=
    (key (Fin d) id).mpr hf
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField R) g
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  have hspan : Submodule.span (ResidueField R) (Set.range (g ∘ a)) = ⊤ := hsp.trans hg
  have hcard : Fintype.card κ = (maximalIdeal R).spanFinrank := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge)]
  let eκ : Fin (maximalIdeal R).spanFinrank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ eκ, ?_⟩
  have hfa := (key κ a).mp hspan
  have hr : Set.range (f ∘ a ∘ eκ) = Set.range (f ∘ a) := by
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨eκ i, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨eκ.symm j, by simp⟩
  show Ideal.span (Set.range (f ∘ a ∘ eκ)) = maximalIdeal R
  rw [hr]
  exact hfa

/-- Base change of a flat algebra along a quotient of the base. -/
theorem flat_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

/-- A flat local map `R_𝔭 → Λ_q` with `𝔭Λ_q = qΛ_q` induces a flat map of truncations. -/
theorem exists_flat_truncation_map {R Λ : Type u} [CommRing R] [CommRing Λ] (𝔭 : Ideal R)
    [𝔭.IsPrime] (q : Ideal Λ) [q.IsPrime] (n : ℕ) (φ : R →+* Λ) (h : 𝔭 = q.comap φ)
    (hflat : (Localization.localRingHom 𝔭 q φ h).Flat)
    (hmax : 𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ) =
      maximalIdeal (Localization.AtPrime q)) :
    ∃ χP : localTruncation 𝔭 n →+* localTruncation q n, χP.Flat ∧
      ∀ x, χP (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk _ (Localization.localRingHom 𝔭 q φ h x) := by
  let g := Localization.localRingHom 𝔭 q φ h
  let _ : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime q) := g.toAlgebra
  have : Module.Flat (Localization.AtPrime 𝔭) (Localization.AtPrime q) := hflat
  have hg : g.comp (algebraMap R (Localization.AtPrime 𝔭)) =
      (algebraMap Λ (Localization.AtPrime q)).comp φ := by
    ext x
    exact Localization.localRingHom_to_map 𝔭 q φ h x
  have hI : (maximalIdeal (Localization.AtPrime 𝔭) ^ n).map
      (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) ^ n := by
    rw [Ideal.map_pow, ← Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭)]
    change (Ideal.map g (Ideal.map (algebraMap R _) 𝔭)) ^ n = _
    rw [Ideal.map_map, hg, hmax]
  have hfl := flat_quotient_map (A := Localization.AtPrime 𝔭) (B := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime 𝔭) ^ n)
  refine ⟨(Ideal.quotEquivOfEq hI).toRingHom.comp (algebraMap _ _), ?_, fun x => rfl⟩
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr hfl)
    (RingHom.Flat.of_bijective (Ideal.quotEquivOfEq hI).bijective)

/-- Transport of a generating family of the maximal ideal along an equality of ideals. -/
theorem span_mk_transport {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J)
    [IsLocalRing (R ⧸ I)] [IsLocalRing (R ⧸ J)] {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range fun j => Ideal.Quotient.mk J (f j)) = maximalIdeal (R ⧸ J)) :
    Ideal.span (Set.range fun j => Ideal.Quotient.mk I (f j)) = maximalIdeal (R ⧸ I) := by
  subst h
  exact hf

/-- Transport of the minimal number of generators along an equality of ideals. -/
theorem spanFinrank_transport {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J)
    [IsLocalRing (R ⧸ I)] [IsLocalRing (R ⧸ J)] :
    (maximalIdeal (R ⧸ I)).spanFinrank = (maximalIdeal (R ⧸ J)).spanFinrank := by
  subst h
  rfl

end SmoothApprox

end Langlands.CommutativeAlgebra.Popescu
