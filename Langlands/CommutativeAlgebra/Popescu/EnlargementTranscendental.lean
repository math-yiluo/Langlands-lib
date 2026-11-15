import Langlands.CommutativeAlgebra.Popescu.EnlargementAlgebraic
import Langlands.CommutativeAlgebra.Popescu.EnlargementKaehler

/-! # The transcendental case of the unit enlargement -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Enlargement

open IsLocalRing Polynomial

/-- **The transcendental case** of the unit enlargement: the residue `α` of `ℓ` is
transcendental over `κ_D`. Then `D' = D[X]_𝔐`, `𝔐 = 𝔪_D D[X]` the preimage of `𝔪_L` under
`X ↦ ℓ`, with residue field `κ_D(α)`, and `v = X` maps to `ℓ`. -/
theorem caseB {k D L : Type u} [Field k] [CommRing D] [CommRing L] [Algebra k D] [Algebra k L]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsLocalRing D] [IsArtinianRing D] [IsLocalRing L]
    [IsArtinianRing L] [Algebra.EssFiniteType k D] [Algebra D L] [IsScalarTower k D L]
    [IsLocalHom (algebraMap D L)] [Module.Flat D L] (ℓ : L) (_hℓ : IsUnit ℓ)
    (htr : Transcendental (ResidueField D) (residue L ℓ)) (t : ℕ) (b : Fin t → D)
    (hli : LinearIndependent (ResidueField D)
      (fun i => KaehlerDifferential.D k (ResidueField D) (residue D (b i))))
    (hsp : Submodule.span (ResidueField D)
      (Set.range fun i => KaehlerDifferential.D k (ResidueField D) (residue D (b i))) = ⊤) :
    ∃ (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (_ : Algebra k D') (_ : Algebra.EssFiniteType k D') (ι : D →ₐ[k] D') (ψ' : D' →ₐ[k] L),
      IsLocalHom ψ' ∧ (ψ' : D' →+* L).Flat ∧ ψ'.comp ι = IsScalarTower.toAlgHom k D L ∧
      (∃ (Q : ℕ) (u : D'), 0 < Q ∧ ψ' u = ℓ ^ Q ∧
        KaehlerDifferential.D k (ResidueField D') (residue D' u) = 0) ∧
      ∃ (r : ℕ) (v : Fin r → D'), (∀ j, ψ' (v j) = ℓ) ∧
        LinearIndependent (ResidueField D')
          (Sum.elim (fun i => KaehlerDifferential.D k (ResidueField D') (residue D' (ι (b i))))
            (fun j => KaehlerDifferential.D k (ResidueField D') (residue D' (v j)))) ∧
        Submodule.span (ResidueField D') (Set.range
          (Sum.elim (fun i => KaehlerDifferential.D k (ResidueField D') (residue D' (ι (b i))))
            (fun j => KaehlerDifferential.D k (ResidueField D') (residue D' (v j))))) = ⊤ := by
  classical
  -- the prime `𝔐 = 𝔪_D D[X]`
  let φX : D[X] →+* L := ((aeval ℓ : D[X] →ₐ[D] L) : D[X] →+* L)
  have hφX : ∀ f : D[X], φX f = aeval ℓ f := fun _ => rfl
  let 𝔐 : Ideal D[X] := (maximalIdeal L).comap φX
  have : 𝔐.IsPrime := Ideal.comap_isPrime _ _
  have h𝔐 : 𝔐 = (maximalIdeal D).map (algebraMap D D[X]) := by
    apply le_antisymm
    · intro f hf
      rw [Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
      have h1 : residue L (aeval ℓ f) = 0 := (residue_eq_zero_iff _).mpr hf
      rw [residue_aeval] at h1
      have h2 : f.map (residue D) = 0 :=
        transcendental_iff_injective.mp htr (by rw [h1, map_zero])
      intro m
      have h3 := congrArg (fun g => g.coeff m) h2
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h3
      exact (residue_eq_zero_iff _).mp h3
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      show φX (algebraMap D D[X] d) ∈ maximalIdeal L
      rw [hφX, (aeval ℓ).commutes]
      exact map_nonunit (algebraMap D L) d hd
  -- `D' = D[X]_𝔐` is Artinian local with `𝔪_{D'} = 𝔪_D D'`
  let D' := Localization.AtPrime 𝔐
  have hmaxD' : (maximalIdeal D).map (algebraMap D D') = maximalIdeal D' := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := 𝔐),
      IsScalarTower.algebraMap_eq D D[X] D', ← Ideal.map_map]
    exact congrArg (Ideal.map (algebraMap D[X] D')) h𝔐.symm
  have hlocDD' : IsLocalHom (algebraMap D D') := ⟨fun x hx => by
    by_contra h
    have h1 : x ∈ maximalIdeal D := (mem_maximalIdeal _).mpr h
    have h2 : algebraMap D D' x ∈ maximalIdeal D' := hmaxD' ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).mp h2 hx⟩
  have hnilD' : IsNilpotent (maximalIdeal D') := by
    obtain ⟨N, hN⟩ := isNilpotent_maximalIdeal D
    refine ⟨N, ?_⟩
    rw [← hmaxD', ← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  have : IsArtinianRing D' := (isArtinianRing_iff_isNilpotent_maximalIdeal D').mpr hnilD'
  -- the map `ψ' : D' → L`, `X ↦ ℓ`
  have hunits : ∀ y : 𝔐.primeCompl, IsUnit (φX y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let ψR : D' →+* L := IsLocalization.lift (M := 𝔐.primeCompl) (g := φX) hunits
  have hψR : ∀ f, ψR (algebraMap D[X] D' f) = aeval ℓ f := fun f => IsLocalization.lift_eq hunits f
  have hψRD : ∀ d, ψR (algebraMap D D' d) = algebraMap D L d := by
    intro d
    rw [IsScalarTower.algebraMap_apply D D[X] D', hψR, (aeval ℓ).commutes]
  let ψ' : D' →ₐ[k] L :=
    { toRingHom := ψR
      commutes' := fun c => by
        show ψR (algebraMap k D' c) = algebraMap k L c
        rw [IsScalarTower.algebraMap_apply k D[X] D', hψR,
          IsScalarTower.algebraMap_apply k D D[X], (aeval ℓ).commutes,
          ← IsScalarTower.algebraMap_apply] }
  have hmapin : (maximalIdeal D').map ψR ≤ maximalIdeal L := by
    rw [← hmaxD', Ideal.map_map]
    have : ψR.comp (algebraMap D D') = algebraMap D L := RingHom.ext hψRD
    rw [this]
    exact map_maximalIdeal_le _
  have hψloc : IsLocalHom ψR := ⟨fun x hx => by
    by_contra h
    have h1 : x ∈ maximalIdeal D' := (mem_maximalIdeal _).mpr h
    have h2 : ψR x ∈ maximalIdeal L := hmapin (Ideal.mem_map_of_mem ψR h1)
    exact (mem_maximalIdeal _).mp h2 hx⟩
  let _ : Algebra D' L := ψR.toAlgebra
  have : IsScalarTower D D' L := .of_algebraMap_eq fun d => (hψRD d).symm
  have : IsLocalHom (algebraMap D' L) := hψloc
  have hflat : Module.Flat D' L := flat_of_map_maximalIdeal hmaxD'
  have : IsLocalHom ψ' := ⟨hψloc.map_nonunit⟩
  have : Algebra.EssFiniteType k D[X] := .comp k D D[X]
  have : Algebra.EssFiniteType k D' := inferInstance
  have : CharP (ResidueField D') p :=
    charP_of_injective_algebraMap (algebraMap k (ResidueField D')).injective p
  -- the element `v = X`
  let v₀ : D' := algebraMap D[X] D' X
  have hv₀ : ψ' v₀ = ℓ := by
    show ψR (algebraMap D[X] D' X) = ℓ
    rw [hψR, aeval_X]
  -- the residue field of `D'` is `κ_D(T)`, `T = v̄₀` transcendental
  let T : ResidueField D' := residue D' v₀
  have hresD' : ∀ f : D[X], residue D' (algebraMap D[X] D' f) = aeval T (f.map (residue D)) := by
    intro f
    have h1 : algebraMap D[X] D' f = aeval v₀ f := by
      rw [show v₀ = IsScalarTower.toAlgHom D D[X] D' X from rfl, Polynomial.aeval_algHom_apply,
        Polynomial.aeval_X_left_apply]
      rfl
    rw [h1, residue_aeval]
  have hT : Transcendental (ResidueField D) T := by
    rw [transcendental_iff_injective, injective_iff_map_eq_zero]
    intro g hg
    obtain ⟨f, rfl⟩ := Polynomial.map_surjective (residue D) residue_surjective g
    rw [← hresD', residue_eq_zero_iff] at hg
    have hf : f ∈ 𝔐 := (IsLocalization.AtPrime.to_map_mem_maximal_iff D' 𝔐 f).mp hg
    rw [h𝔐, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff] at hf
    ext m
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (residue_eq_zero_iff _).mpr (hf m)
  have hfrac : ∀ z : ResidueField D', ∃ f g : (ResidueField D)[X],
      z = aeval T f / aeval T g := by
    intro z
    obtain ⟨y, rfl⟩ := residue_surjective z
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔐.primeCompl y
    refine ⟨f.map (residue D), (s : D[X]).map (residue D), ?_⟩
    have hs : IsUnit (algebraMap D[X] D' s) := IsLocalization.map_units D' s
    have hs' : residue D' (algebraMap D[X] D' s) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr hs
    rw [← hresD', ← hresD', eq_div_iff hs', ← map_mul, IsLocalization.mk'_spec]
  obtain ⟨hli', hsp'⟩ := kaehler_basis_adjoin_transcendental (k := k) T hT hfrac
    (fun i => residue D (b i)) hli hsp
  refine ⟨D', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom k D D', ψ', inferInstance, hflat, ?_,
    ⟨p, v₀ ^ p, (Fact.out : p.Prime).pos, by rw [map_pow, hv₀], by rw [map_pow, D_pow_char]⟩,
    1, fun _ => v₀, fun _ => hv₀, hli', hsp'⟩
  ext d
  exact hψRD d

end Enlargement

end Langlands.CommutativeAlgebra.Popescu
