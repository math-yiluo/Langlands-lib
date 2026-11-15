import Langlands.CommutativeAlgebra.Popescu.EnlargementTools

/-! # The algebraic case of the unit enlargement -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Enlargement

open IsLocalRing Polynomial

/-- If `H` reduces to an irreducible polynomial over the residue field, then `𝔪_D · D[X]/(H)` is a
maximal ideal. -/
theorem isMaximal_map_adjoinRoot {D : Type*} [CommRing D] [IsLocalRing D] (H : D[X])
    (hirr : Irreducible (H.map (residue D))) :
    ((maximalIdeal D).map (AdjoinRoot.of H)).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  have hmax : (Ideal.span {H.map (residue D)} : Ideal ((ResidueField D)[X])).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  have hf := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
  exact MulEquiv.isField hf
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal D) H).toMulEquiv

/-- If moreover `𝔪_D` is nilpotent, `D[X]/(H)` is local with maximal ideal `𝔪_D · D[X]/(H)`. -/
theorem isLocalRing_adjoinRoot {D : Type*} [CommRing D] [IsLocalRing D]
    (hnil : IsNilpotent (maximalIdeal D)) (H : D[X]) (hirr : Irreducible (H.map (residue D))) :
    IsLocalRing (AdjoinRoot H) := by
  have hJ := isMaximal_map_adjoinRoot H hirr
  obtain ⟨N, hN⟩ := hnil
  have hJle : ∀ M : Ideal (AdjoinRoot H), M.IsMaximal →
      (maximalIdeal D).map (AdjoinRoot.of H) ≤ M := by
    intro M hM
    have hpow : ((maximalIdeal D).map (AdjoinRoot.of H)) ^ N ≤ M := by
      rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
      exact bot_le
    exact Ideal.IsPrime.le_of_pow_le hpow
  exact IsLocalRing.of_unique_max_ideal
    ⟨_, hJ, fun M hM => (hJ.eq_of_le hM.ne_top (hJle M hM)).symm⟩


/-- Residues of polynomial expressions along a local map `D → L`. -/
theorem residue_aeval {D L : Type*} [CommRing D] [CommRing L] [IsLocalRing D] [IsLocalRing L]
    [Algebra D L] [IsLocalHom (algebraMap D L)] (F : D[X]) (x : L) :
    residue L (aeval x F) = aeval (residue L x) (F.map (residue D)) := by
  have h1 : residue L (aeval x F) = IsScalarTower.toAlgHom D L (ResidueField L) (aeval x F) := rfl
  rw [h1, ← Polynomial.aeval_algHom_apply]
  have h2 : (residue D : D →+* ResidueField D) = algebraMap D (ResidueField D) := rfl
  rw [h2, Polynomial.aeval_map_algebraMap]
  rfl

/-- **The algebraic case** of the unit enlargement: the residue `α` of `ℓ` is algebraic over `κ_D`.
A `p`-power `β = α^{p^n}` is separable; `D' = D[X]/(H)` for a monic lift `H` of its minimal
polynomial, mapped to `L` by a Hensel root of `H` lifting `β`. -/
theorem caseA {k D L : Type u} [Field k] [CommRing D] [CommRing L] [Algebra k D] [Algebra k L]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsLocalRing D] [IsArtinianRing D] [IsLocalRing L]
    [IsArtinianRing L] [Algebra.EssFiniteType k D] [Algebra D L] [IsScalarTower k D L]
    [IsLocalHom (algebraMap D L)] [Module.Flat D L] (ℓ : L) (hℓ : IsUnit ℓ)
    (halg : IsAlgebraic (ResidueField D) (residue L ℓ)) (t : ℕ) (b : Fin t → D)
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
  have : CharP (ResidueField D) p :=
    charP_of_injective_algebraMap (algebraMap k (ResidueField D)).injective p
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  -- a `p`-power of `α` is separable
  obtain ⟨n, hsep⟩ : ∃ n : ℕ, IsSeparable (ResidueField D) (residue L ℓ ^ (p ^ n)) := by
    have hirr := minpoly.irreducible halg.isIntegral
    obtain ⟨n, g, hg, hgf⟩ := exists_separable_of_irreducible p hirr (Fact.out : p.Prime).ne_zero
    refine ⟨n, ?_⟩
    have h0 : aeval (residue L ℓ ^ (p ^ n)) g = 0 := by
      have := minpoly.aeval (ResidueField D) (residue L ℓ)
      rw [← hgf, Polynomial.expand_aeval] at this
      exact this
    exact hg.of_dvd (minpoly.dvd _ _ h0)
  let β := residue L ℓ ^ (p ^ n)
  have hβint : IsIntegral (ResidueField D) β := hsep.isIntegral
  have hhmonic := minpoly.monic hβint
  have hhirr := minpoly.irreducible hβint
  have hh0 : aeval β (minpoly (ResidueField D) β) = 0 := minpoly.aeval _ _
  -- a monic lift `H`
  have hlifts : minpoly (ResidueField D) β ∈ Polynomial.lifts (residue D) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    exact residue_surjective _
  obtain ⟨H, hHmap, -, hHmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hhmonic
  -- a Hensel root `θ ∈ L` of `H` lifting `β`
  have : IsAdicComplete (maximalIdeal L) L :=
    isAdicComplete_of_isNilpotent (isNilpotent_maximalIdeal L)
  have hres0 : residue L (ℓ ^ (p ^ n)) = β := map_pow _ _ _
  have hev : (H.map (algebraMap D L)).eval (ℓ ^ (p ^ n)) ∈ maximalIdeal L := by
    rw [Polynomial.eval_map_algebraMap, ← residue_eq_zero_iff, residue_aeval, hres0, hHmap, hh0]
  have hder : IsUnit (Ideal.Quotient.mk (maximalIdeal L)
      ((H.map (algebraMap D L)).derivative.eval (ℓ ^ (p ^ n)))) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    change IsUnit (residue L _)
    rw [residue_aeval, hres0, ← Polynomial.derivative_map, hHmap, isUnit_iff_ne_zero]
    exact hsep.aeval_derivative_ne_zero hh0
  obtain ⟨θ, hθroot, hθ⟩ := HenselianRing.is_henselian (H.map (algebraMap D L))
    (hHmonic.map _) (ℓ ^ (p ^ n)) hev hder
  have hroot : aeval θ H = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact hθroot
  have hθres : residue L θ = β := by
    have h1 : residue L (θ - ℓ ^ (p ^ n)) = 0 := (residue_eq_zero_iff _).mpr hθ
    rw [map_sub, sub_eq_zero] at h1
    rw [h1, hres0]
  -- `D' = D[X]/(H)`
  have hirrH : Irreducible (H.map (residue D)) := by rw [hHmap]; exact hhirr
  have : IsLocalRing (AdjoinRoot H) :=
    isLocalRing_adjoinRoot (isNilpotent_maximalIdeal D) H hirrH
  have hmaxD' : (maximalIdeal D).map (algebraMap D (AdjoinRoot H)) =
      maximalIdeal (AdjoinRoot H) :=
    IsLocalRing.eq_maximalIdeal (isMaximal_map_adjoinRoot H hirrH)
  have : Module.Finite D (AdjoinRoot H) := (AdjoinRoot.powerBasis' hHmonic).finite
  have : IsArtinianRing (AdjoinRoot H) := IsArtinianRing.of_finite D (AdjoinRoot H)
  have : Algebra.FiniteType D (AdjoinRoot H) := inferInstance
  have : Algebra.EssFiniteType k (AdjoinRoot H) := .comp k D (AdjoinRoot H)
  have hlocDD' : IsLocalHom (algebraMap D (AdjoinRoot H)) := ⟨fun x hx => by
    by_contra h
    have h1 : x ∈ maximalIdeal D := (mem_maximalIdeal _).mpr h
    have h2 : algebraMap D (AdjoinRoot H) x ∈ maximalIdeal (AdjoinRoot H) :=
      hmaxD' ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).mp h2 hx⟩
  -- the map `ψ' : D' → L`, `root ↦ θ`
  let ψD : AdjoinRoot H →ₐ[D] L := AdjoinRoot.liftAlgHom H (Algebra.ofId D L) θ (by
    have h := hroot
    rw [Polynomial.aeval_def] at h
    exact h)
  have hψroot : ψD (AdjoinRoot.root H) = θ := AdjoinRoot.liftAlgHom_root _ _ _ _
  let ψ' : AdjoinRoot H →ₐ[k] L := ψD.restrictScalars k
  have hmapin : (maximalIdeal (AdjoinRoot H)).map (ψD : AdjoinRoot H →+* L) ≤
      maximalIdeal L := by
    rw [← hmaxD', Ideal.map_map, ψD.comp_algebraMap]
    exact map_maximalIdeal_le _
  have hψloc : IsLocalHom ψD := ⟨fun x hx => by
    by_contra h
    have h1 : x ∈ maximalIdeal (AdjoinRoot H) := (mem_maximalIdeal _).mpr h
    have h2 : ψD x ∈ maximalIdeal L :=
      hmapin (Ideal.mem_map_of_mem (ψD : AdjoinRoot H →+* L) h1)
    exact (mem_maximalIdeal _).mp h2 hx⟩
  let _ : Algebra (AdjoinRoot H) L := (ψD : AdjoinRoot H →+* L).toAlgebra
  have : IsScalarTower D (AdjoinRoot H) L := .of_algebraMap_eq fun d => (ψD.commutes d).symm
  have : IsLocalHom (algebraMap (AdjoinRoot H) L) := ⟨hψloc.map_nonunit⟩
  have hflat : Module.Flat (AdjoinRoot H) L := flat_of_map_maximalIdeal hmaxD'
  have : IsLocalHom ψ' := ⟨hψloc.map_nonunit⟩
  -- the element `u`
  obtain ⟨Q, w, hQ, hw⟩ := exists_pth_power_preimage p (isNilpotent_maximalIdeal L)
    (ψ' : AdjoinRoot H →+* L) hℓ (x := AdjoinRoot.root H) (e := p ^ n)
    (pow_pos (Fact.out : p.Prime).pos _) (by
      rw [← residue_eq_zero_iff, map_sub]
      show residue L (ψD (AdjoinRoot.root H)) - residue L (ℓ ^ (p ^ n)) = 0
      rw [hψroot, hθres, hres0, sub_self])
  have : CharP (ResidueField (AdjoinRoot H)) p :=
    charP_of_injective_algebraMap (algebraMap k (ResidueField (AdjoinRoot H))).injective p
  refine ⟨AdjoinRoot H, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, IsScalarTower.toAlgHom k D (AdjoinRoot H), ψ', inferInstance, hflat, ?_,
    ⟨Q, w ^ p, hQ, hw, by rw [map_pow, D_pow_char]⟩, 0, Fin.elim0, fun j => j.elim0, ?_⟩
  · ext d
    exact ψD.commutes d
  -- the residue field extension is finite separable, so the differential basis persists
  let γ := residue (AdjoinRoot H) (AdjoinRoot.root H)
  have hγ0 : aeval γ (minpoly (ResidueField D) β) = 0 := by
    rw [← hHmap, show γ = residue (AdjoinRoot H) (AdjoinRoot.root H) from rfl, ← residue_aeval,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hγsep : IsSeparable (ResidueField D) γ :=
    hsep.of_dvd (minpoly.dvd _ _ hγ0)
  have hadj : IntermediateField.adjoin (ResidueField D) {γ} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := residue_surjective z
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [← AdjoinRoot.aeval_eq, residue_aeval]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  have : Algebra.IsSeparable (ResidueField D) (ResidueField (AdjoinRoot H)) := by
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (ResidueField D)
      (ResidueField (AdjoinRoot H))).mpr hγsep
    refine ⟨fun z => ?_⟩
    exact IntermediateField.isSeparable_of_mem_isSeparable (ResidueField D)
      (ResidueField (AdjoinRoot H)) (L := IntermediateField.adjoin (ResidueField D) {γ})
      (by rw [hadj]; trivial)
  have : Algebra.FormallyEtale (ResidueField D) (ResidueField (AdjoinRoot H)) :=
    .of_isSeparable _ _
  obtain ⟨hli', hsp'⟩ := kaehler_basis_of_formallyEtale (k := k) (F' := ResidueField (AdjoinRoot H))
    (fun i => residue D (b i)) hli hsp
  have hfam : (Sum.elim (fun i => KaehlerDifferential.D k (ResidueField (AdjoinRoot H))
      (residue (AdjoinRoot H) (IsScalarTower.toAlgHom k D (AdjoinRoot H) (b i))))
      (fun j : Fin 0 => KaehlerDifferential.D k (ResidueField (AdjoinRoot H))
        (residue (AdjoinRoot H) (Fin.elim0 j)))) =
      (fun i => KaehlerDifferential.D k (ResidueField (AdjoinRoot H))
        (algebraMap (ResidueField D) (ResidueField (AdjoinRoot H)) (residue D (b i)))) ∘
        (Equiv.sumEmpty (Fin t) (Fin 0)) := by
    funext z
    rcases z with i | j
    · rfl
    · exact j.elim0
  rw [hfam]
  refine ⟨hli'.comp _ (Equiv.sumEmpty (Fin t) (Fin 0)).injective, ?_⟩
  rw [(Equiv.sumEmpty (Fin t) (Fin 0)).surjective.range_comp]
  exact hsp'

end Enlargement

end Langlands.CommutativeAlgebra.Popescu
