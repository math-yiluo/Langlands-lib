import Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothEnlargementStatement
import Langlands.CommutativeAlgebra.Popescu.EnlargementAlgebraic
import Langlands.CommutativeAlgebra.Popescu.SmoothApproxTools

/-! # Enlarging an essentially smooth approximation by a power of a unit -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open IsLocalRing Polynomial

private theorem formallySmooth_essFiniteType_of_essentiallySmooth
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : EssentiallySmooth R S) :
    Algebra.FormallySmooth R S ∧ Algebra.EssFiniteType R S := by
  obtain ⟨T, _, _, _, _, M, hSmooth, hLoc⟩ := h
  have : Algebra.FormallySmooth T S := .of_isLocalization M
  have : Algebra.EssFiniteType T S := .of_isLocalization S M
  exact ⟨Algebra.FormallySmooth.comp R T S, Algebra.EssFiniteType.comp R T S⟩

/-- For a local algebra over a Noetherian base, the finite-type model has a smooth basic open
through the prime corresponding to the maximal ideal of the algebra. -/
private theorem essentiallySmooth_of_formallySmooth
    (R S : Type u) [CommRing R] [IsNoetherianRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.FormallySmooth R S] [Algebra.EssFiniteType R S] :
    EssentiallySmooth R S := by
  let T := Algebra.EssFiniteType.subalgebra R S
  let P : Ideal T := (maximalIdeal S).comap (algebraMap T S)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid R S = P.primeCompl := by
    ext t
    change IsUnit (algebraMap T S t) ↔ ¬ ¬ IsUnit (algebraMap T S t)
    exact not_not.symm
  have : IsLocalization P.primeCompl S := hM ▸ Algebra.EssFiniteType.isLocalization R S
  have : Algebra.IsSmoothAt R P :=
    Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).restrictScalars R)
  have : Algebra.FinitePresentation R T :=
    Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType R T)
  obtain ⟨f, hf, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R P
  let A := Localization.Away f
  have hle : Submonoid.powers f ≤ P.primeCompl := Submonoid.powers_le.mpr hf
  let : Algebra A S := IsLocalization.localizationAlgebraOfSubmonoidLe A S _ _ hle
  have : IsScalarTower T A S :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A S _ _ hle
  have : IsScalarTower R A S := .to₁₃₄ R T A S
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    P.primeCompl.map (algebraMap T A), hs,
    IsLocalization.isLocalization_of_submonoid_le A S _ _ hle⟩

section Enlargement

variable {D L : Type u} [CommRing D] [CommRing L]
  [IsLocalRing D] [IsLocalRing L] [IsArtinianRing L]
  [Algebra D L] [IsLocalHom (algebraMap D L)] [Module.Flat D L]

private theorem local_flat_of_map_maximalIdeal {E : Type u} [CommRing E] [IsLocalRing E]
    [IsArtinianRing E] [Algebra D E] (f : E →ₐ[D] L)
    (hm : (maximalIdeal D).map (algebraMap D E) = maximalIdeal E) :
    IsLocalHom (f : E →+* L) ∧ (f : E →+* L).Flat := by
  have hlocal : IsLocalHom (f : E →+* L) :=
    ((local_hom_TFAE (f : E →+* L)).out 1 3).mpr (by
      rw [← hm, Ideal.map_map, f.comp_algebraMap]
      exact map_maximalIdeal_le _)
  let : Algebra E L := f.toRingHom.toAlgebra
  have : IsScalarTower D E L := IsScalarTower.of_algHom f
  have : IsLocalHom (algebraMap E L) := hlocal
  have hflat : Module.Flat E L := Enlargement.flat_of_map_maximalIdeal hm
  exact ⟨hlocal, hflat⟩

variable [IsArtinianRing D]

/-- The transcendental residue gives a prime localization of the polynomial algebra. -/
private theorem enlarge_of_transcendental (ℓ : L)
    (htr : Transcendental (ResidueField D) (residue L ℓ)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : IsLocalRing E) (_ : IsArtinianRing E)
      (_ : Algebra D E) (f : E →ₐ[D] L),
      Algebra.FormallySmooth D E ∧ Algebra.EssFiniteType D E ∧
      IsLocalHom (f : E →+* L) ∧ (f : E →+* L).Flat ∧
      ∃ e > 0, ℓ ^ e ∈ Set.range (f : E →+* L) := by
  let ev : D[X] →+* L := (aeval ℓ : D[X] →ₐ[D] L).toRingHom
  let P := (maximalIdeal L).comap ev
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P = (maximalIdeal D).map (algebraMap D D[X]) := by
    apply le_antisymm
    · intro F hF
      rw [Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
      have hz : residue L (aeval ℓ F) = 0 := (residue_eq_zero_iff _).mpr hF
      rw [Enlargement.residue_aeval] at hz
      have hzero : F.map (residue D) = 0 :=
        transcendental_iff_injective.mp htr (by rw [hz, map_zero])
      intro j
      have hj := congrArg (fun G => G.coeff j) hzero
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hj
      exact (residue_eq_zero_iff _).mp hj
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      change aeval ℓ (algebraMap D D[X] d) ∈ maximalIdeal L
      rw [(aeval ℓ).commutes]
      exact map_nonunit (algebraMap D L) d hd
  let E := Localization.AtPrime P
  have hm : (maximalIdeal D).map (algebraMap D E) = maximalIdeal E := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P),
      IsScalarTower.algebraMap_eq D D[X] E, ← Ideal.map_map, ← hP]
  have hnil : IsNilpotent (maximalIdeal E) := by
    obtain ⟨N, hN⟩ := Enlargement.isNilpotent_maximalIdeal D
    refine ⟨N, ?_⟩
    rw [← hm, ← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  have : IsArtinianRing E := (isArtinianRing_iff_isNilpotent_maximalIdeal E).mpr hnil
  have hunits : ∀ x : P.primeCompl, IsUnit (ev x) := by
    intro x
    by_contra hx
    exact x.prop ((mem_maximalIdeal _).mpr hx)
  let f : E →ₐ[D] L :=
    { toRingHom := IsLocalization.lift hunits
      commutes' := fun d => by
        change IsLocalization.lift hunits (algebraMap D E d) = algebraMap D L d
        rw [IsScalarTower.algebraMap_apply D D[X] E, IsLocalization.lift_eq]
        exact (aeval ℓ).commutes d }
  obtain ⟨hlocal, hflat⟩ := local_flat_of_map_maximalIdeal f hm
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, f, ?_, ?_,
    hlocal, hflat, 1, Nat.one_pos, algebraMap D[X] E X, ?_⟩
  · exact Algebra.FormallySmooth.comp D D[X] E
  · exact Algebra.EssFiniteType.comp D D[X] E
  · change IsLocalization.lift hunits (algebraMap D[X] E X) = ℓ ^ 1
    rw [IsLocalization.lift_eq, pow_one]
    exact aeval_X ℓ

/-- For an algebraic residue, a separable power determines a finite étale extension. -/
private theorem enlarge_of_algebraic (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField D) p] [CharP L p] (ℓ : L) (hℓ : IsUnit ℓ)
    (halg : IsAlgebraic (ResidueField D) (residue L ℓ)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : IsLocalRing E) (_ : IsArtinianRing E)
      (_ : Algebra D E) (f : E →ₐ[D] L),
      Algebra.FormallySmooth D E ∧ Algebra.EssFiniteType D E ∧
      IsLocalHom (f : E →+* L) ∧ (f : E →+* L).Flat ∧
      ∃ e > 0, ℓ ^ e ∈ Set.range (f : E →+* L) := by
  obtain ⟨r, hsep⟩ : ∃ r : ℕ, IsSeparable (ResidueField D) (residue L ℓ ^ (p ^ r)) := by
    obtain ⟨r, G, hG, hGmin⟩ := exists_separable_of_irreducible p
      (minpoly.irreducible halg.isIntegral) (Fact.out : p.Prime).ne_zero
    have hz := minpoly.aeval (ResidueField D) (residue L ℓ)
    rw [← hGmin, Polynomial.expand_aeval] at hz
    exact ⟨r, hG.of_dvd (minpoly.dvd _ _ hz)⟩
  let β := residue L ℓ ^ (p ^ r)
  have hβint : IsIntegral (ResidueField D) β := hsep.isIntegral
  let G := minpoly (ResidueField D) β
  have hGzero : aeval β G = 0 := minpoly.aeval _ _
  have hlift : G ∈ Polynomial.lifts (residue D) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    exact residue_surjective _
  obtain ⟨H, hHmap, -, hHmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hβint)
  have hderβ : aeval β (derivative (H.map (residue D))) ≠ 0 := by
    rw [hHmap]
    exact hsep.aeval_derivative_ne_zero hGzero
  -- Lift the root inside the target Artinian local ring.
  have hnilL := Enlargement.isNilpotent_maximalIdeal L
  have : IsAdicComplete (maximalIdeal L) L := Enlargement.isAdicComplete_of_isNilpotent hnilL
  have hres : residue L (ℓ ^ (p ^ r)) = β := map_pow _ _ _
  have hev : (H.map (algebraMap D L)).eval (ℓ ^ (p ^ r)) ∈ maximalIdeal L := by
    rw [Polynomial.eval_map_algebraMap, ← residue_eq_zero_iff,
      Enlargement.residue_aeval, hres, hHmap, hGzero]
  have hder : IsUnit (Ideal.Quotient.mk (maximalIdeal L)
      ((H.map (algebraMap D L)).derivative.eval (ℓ ^ (p ^ r)))) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    change IsUnit (residue L _)
    rw [Enlargement.residue_aeval, hres, ← Polynomial.derivative_map, isUnit_iff_ne_zero]
    exact hderβ
  obtain ⟨θ, hθroot, hθ⟩ := HenselianRing.is_henselian (H.map (algebraMap D L))
    (hHmonic.map _) (ℓ ^ (p ^ r)) hev hder
  have hθres : residue L θ = β := by
    rw [← hres, ← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr hθ
  have hirr : Irreducible (H.map (residue D)) := by
    rw [hHmap]
    exact minpoly.irreducible hβint
  have : IsLocalRing (AdjoinRoot H) :=
    Enlargement.isLocalRing_adjoinRoot (Enlargement.isNilpotent_maximalIdeal D) H hirr
  have hm : (maximalIdeal D).map (algebraMap D (AdjoinRoot H)) = maximalIdeal (AdjoinRoot H) :=
    IsLocalRing.eq_maximalIdeal (Enlargement.isMaximal_map_adjoinRoot H hirr)
  have : Module.Finite D (AdjoinRoot H) := (AdjoinRoot.powerBasis' hHmonic).finite
  have : IsArtinianRing (AdjoinRoot H) := IsArtinianRing.of_finite D (AdjoinRoot H)
  let f : AdjoinRoot H →ₐ[D] L := AdjoinRoot.liftAlgHom H (Algebra.ofId D L) θ (by
    change eval₂ (algebraMap D L) θ H = 0
    rw [← Polynomial.aeval_def, ← Polynomial.eval_map_algebraMap]
    exact hθroot)
  have hroot : f (AdjoinRoot.root H) = θ := AdjoinRoot.liftAlgHom_root _ _ _ _
  obtain ⟨hlocal, hflat⟩ := local_flat_of_map_maximalIdeal f hm
  -- The derivative is already invertible in the adjoined-root ring.
  have hunit : IsUnit (AdjoinRoot.mk H (derivative H)) := by
    apply isUnit_of_map_unit (f : AdjoinRoot H →+* L)
    change IsUnit (f (AdjoinRoot.mk H (derivative H)))
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, hroot,
      ← residue_ne_zero_iff_isUnit, Enlargement.residue_aeval, hθres,
      ← Polynomial.derivative_map]
    exact hderβ
  let P : StandardEtalePair D := ⟨H, hHmonic, derivative H, 1, 0, 1, by simp⟩
  let A := Localization.Away (AdjoinRoot.mk H (derivative H))
  let eqv : AdjoinRoot H ≃ₐ[AdjoinRoot H] A :=
    IsLocalization.atUnits (AdjoinRoot H) (Submonoid.powers (AdjoinRoot.mk H (derivative H)))
      (Submonoid.powers_le.mpr hunit)
  have : Algebra.Etale D (AdjoinRoot H) :=
    Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans (eqv.restrictScalars D).symm)
  obtain ⟨e, w, he, hw⟩ := Enlargement.exists_pth_power_preimage p hnilL
    (f : AdjoinRoot H →+* L) hℓ (x := AdjoinRoot.root H) (e := p ^ r)
    (pow_pos (Fact.out : p.Prime).pos _) (by
      change f (AdjoinRoot.root H) - ℓ ^ (p ^ r) ∈ maximalIdeal L
      rwa [hroot])
  exact ⟨AdjoinRoot H, inferInstance, inferInstance, inferInstance, inferInstance, f,
    inferInstance, inferInstance, hlocal, hflat, e, he, w ^ p, hw⟩

end Enlargement

/-- Stacks 07FI, with essential smoothness also over the truncated polynomial base. -/
theorem artinianSmoothEnlargement : ArtinianSmoothEnlargementStatement.{u} := by
  intro k Λ _ _ _ p _ _ hgeom q _ n hn m φ 𝔭 _ _ _ _ D _ _ _ _ ψ hsm hlocal hflat _
    l hl
  let R := localTruncation 𝔭 n
  let L := localTruncation q n
  have : IsNoetherianRing Λ := hgeom.1
  have : IsLocalRing L := SmoothApprox.isLocalRing_localTruncation q hn
  have : IsArtinianRing L := SmoothApprox.isArtinianRing_localTruncation q
  let : Algebra D L := ψ.toAlgebra
  have : IsLocalHom (algebraMap D L) := hlocal
  have : Module.Flat D L := hflat
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  let : Algebra k D := ((algebraMap R D).comp (algebraMap k R)).toAlgebra
  have : CharP (ResidueField D) p :=
    charP_of_injective_algebraMap (algebraMap k (ResidueField D)).injective p
  let ℓ := toLocalTruncation q n l
  have hℓ : IsUnit ℓ :=
    (IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨l, hl⟩).map
      (Ideal.Quotient.mk _)
  have hE : ∃ (E : Type u) (_ : CommRing E) (_ : IsLocalRing E) (_ : IsArtinianRing E)
      (_ : Algebra D E) (f : E →ₐ[D] L),
      Algebra.FormallySmooth D E ∧ Algebra.EssFiniteType D E ∧
      IsLocalHom (f : E →+* L) ∧ (f : E →+* L).Flat ∧
      ∃ e > 0, ℓ ^ e ∈ Set.range (f : E →+* L) := by
    by_cases halg : IsAlgebraic (ResidueField D) (residue L ℓ)
    · exact enlarge_of_algebraic p ℓ hℓ halg
    · exact enlarge_of_transcendental ℓ halg
  obtain ⟨E, _, _, _, _, f, hsmDE, hftDE, hlocalE, hflatE, e, he, hpow⟩ := hE
  have : IsNoetherianRing R := inferInstance
  let : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
  have : IsScalarTower R D E := .of_algebraMap_eq' rfl
  obtain ⟨hsmRD, hftRD⟩ := formallySmooth_essFiniteType_of_essentiallySmooth hsm
  have : Algebra.FormallySmooth R E := .comp R D E
  have : Algebra.EssFiniteType R E := .comp R D E
  exact ⟨e, he, E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, f.toRingHom, essentiallySmooth_of_formallySmooth D E,
    essentiallySmooth_of_formallySmooth R E, hlocalE, hflatE, f.comp_algebraMap, hpow⟩

end Langlands.CommutativeAlgebra.Popescu
