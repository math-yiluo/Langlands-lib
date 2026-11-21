import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.TwistedCharacterCornerDensity

/-! # Separation by twisted characters for finite-order automorphisms -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory

universe uG uV uW

section Subgroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact open subgroup contains a compact open subgroup invariant under
a continuous automorphism of finite order. -/
theorem exists_invariantCompactOpen_le (α : MulAut G) (hα : Continuous α)
    {d : ℕ} (hd : 0 < d) (horder : α ^ d = 1) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ J ≤ K ∧
      ∀ g : G, α g ∈ J ↔ g ∈ J := by
  let H : Subgroup G := ⨅ i : Fin d, K.toSubgroup.comap (α ^ (i : ℕ)).toMonoidHom
  have hcont (i : ℕ) : Continuous (α ^ i) := by
    induction i with
    | zero => simpa only [pow_zero, MulAut.coe_one] using (continuous_id : Continuous (id : G → G))
    | succ i hi =>
      rw [pow_succ', MulAut.coe_mul]
      exact hα.comp hi
  have hH : IsOpen (H : Set G) := by
    rw [show H = _ from rfl, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => K.isOpen.preimage (hcont i)
  let J : OpenSubgroup G := ⟨H, hH⟩
  have hmem (g : G) : g ∈ J ↔ ∀ i : Fin d, (α ^ (i : ℕ)) g ∈ K :=
    Subgroup.mem_iInf
  have hJK : J ≤ K := fun g hg => by
    simpa only [Fin.val_mk, pow_zero, MulAut.one_apply] using (hmem g).mp hg ⟨0, hd⟩
  refine ⟨J, hK.of_isClosed_subset J.isClosed hJK, hJK, fun g => ?_⟩
  have hforward (x : G) (hx : x ∈ J) : α x ∈ J := by
    apply (hmem (α x)).mpr
    intro i
    rw [← MulAut.mul_apply, ← pow_succ]
    by_cases hi : (i : ℕ) + 1 < d
    · exact (hmem x).mp hx ⟨(i : ℕ) + 1, hi⟩
    · have he : (i : ℕ) + 1 = d := by omega
      rw [he, horder, MulAut.one_apply]
      exact hJK hx
  refine ⟨fun hg => ?_, hforward g⟩
  have hiter (i : ℕ) : (α ^ i) (α g) ∈ J := by
    induction i with
    | zero => simpa only [pow_zero, MulAut.one_apply] using hg
    | succ i hi => exact pow_succ' α i ▸ hforward _ hi
  have hh := hiter (d - 1)
  rw [← MulAut.mul_apply, ← pow_succ, show d - 1 + 1 = d by omega, horder, MulAut.one_apply] at hh
  exact hh

end Subgroup

section FixedSpaces

variable {G : Type uG} [Group G] {α : MulAut G}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {K : Subgroup G}

/-- The twist intertwiner restricts to an automorphism of the fixed vectors
of each subgroup preserved by the twist. -/
def fixedVectorsTwistEquiv (hK : ∀ g : G, α g ∈ K ↔ g ∈ K)
    (A : ρ.Equiv (ρ.comp α.toMonoidHom)) :
    fixedVectors ρ K ≃ₗ[ℂ] fixedVectors ρ K := by
  have hpres (x : fixedVectors ρ K) : A x.val ∈ fixedVectors ρ K := by
    intro k
    let g := α.symm k.val
    have hg : g ∈ K := (hK g).mp (by simpa only [g, MulEquiv.apply_symm_apply] using k.property)
    have hi := LinearMap.congr_fun (A.isIntertwining' g) x.val
    change A (ρ g x.val) = ρ (α g) (A x.val) at hi
    have hfix : ρ g x.val = x.val := x.property ⟨g, hg⟩
    rw [hfix, show α g = k.val from α.apply_symm_apply _] at hi
    exact hi.symm
  let a := (A.toLinearMap.comp (fixedVectors ρ K).subtype).codRestrict (fixedVectors ρ K) hpres
  refine LinearEquiv.ofBijective a ⟨fun x y h => Subtype.ext
    (A.toLinearEquiv.injective (congrArg Subtype.val h)), ?_⟩
  intro y
  let x := A.toLinearEquiv.symm y.val
  have hAx : A x = y.val := A.toLinearEquiv.apply_symm_apply y.val
  have hx : x ∈ fixedVectors ρ K := by
    intro k
    apply A.toLinearEquiv.injective
    change A (ρ k.val x) = A x
    have hi := LinearMap.congr_fun (A.isIntertwining' k.val) x
    change A (ρ k.val x) = ρ (α k.val) (A x) at hi
    rw [hi, hAx]
    exact y.property ⟨α k.val, (hK k.val).mpr k.property⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hAx⟩

@[simp]
theorem fixedVectorsTwistEquiv_coe (hK : ∀ g : G, α g ∈ K ↔ g ∈ K)
    (A : ρ.Equiv (ρ.comp α.toMonoidHom)) (x : fixedVectors ρ K) :
    (fixedVectorsTwistEquiv hK A x : V) = A x.val := rfl

end FixedSpaces

section Trace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ) {α : MulAut G}
  (A : ρ.Equiv (ρ.comp α.toMonoidHom))

/-- The finite-rank twisted distribution on a corner element is the trace
of its corner action composed with the fixed-space twist. -/
theorem twistedDistribution_corner (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hαK : ∀ g : G, α g ∈ K ↔ g ∈ K) (r : Hecke.HeckeAlgebra.Corner μ K hK) :
    twistedDistribution μ ρ hρ A.toLinearMap
        (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK r)) =
      LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup)
        ((Hecke.cornerAction μ ρ hρ.1 K hK r).comp (fixedVectorsTwistEquiv hαK A).toLinearMap) := by
  let := hρ.2 K
  let f := Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK r)
  have hrange : ((Hecke.integratedAction μ ρ hρ.1 f).comp A.toLinearMap).range ≤
      fixedVectors ρ K.toSubgroup := by
    rintro _ ⟨x, rfl⟩
    exact Hecke.integratedAction_mem_fixedVectors μ ρ hρ.1 r.property (A x)
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ _ hrange]
  rfl

end Trace

/-- Two irreducible admissible representations with proportional twisted
distributions for a continuous finite-order twist are equivalent. -/
def TwistedCharacterSeparationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (α : MulAut G), Continuous α → ∀ d : ℕ, 0 < d → α ^ d = 1 →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
      (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ), ρ.IsIrreducible → σ.IsIrreducible →
    ∀ (A : ρ.Equiv (ρ.comp α.toMonoidHom)) (B : σ.Equiv (σ.comp α.toMonoidHom)) (c : ℂ),
      (∀ f : SchwartzBruhat G,
        twistedDistribution μ ρ hρ A.toLinearMap f = c * twistedDistribution μ σ hσ B.toLinearMap f) →
      Nonempty (ρ.Equiv σ)

theorem twistedCharacterSeparation : TwistedCharacterSeparationStatement.{uG, uV, uW} := by
  intro G _ _ _ _ _ _ _ _ μ _ α hα d hd hpow V _ _ W _ _ ρ σ hρ hσ hρi hσi A B c hdist
  let := CharacterSeparation.nontrivial_of_isIrreducible hρi
  let := CharacterSeparation.nontrivial_of_isIrreducible hσi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨K, hK, hvK, hwK⟩ := CharacterSeparation.exists_compactOpen_fixed hρ.1 hσ.1 v w
  obtain ⟨J, hJ, hJK, hαJ⟩ := exists_invariantCompactOpen_le α hα hd hpow K hK
  have hvJ : v ∈ fixedVectors ρ J.toSubgroup := fun g => hvK ⟨g.val, hJK g.property⟩
  have hwJ : w ∈ fixedVectors σ J.toSubgroup := fun g => hwK ⟨g.val, hJK g.property⟩
  let := Hecke.cornerModule μ ρ hρ.1 J hJ
  let := Hecke.cornerModule μ σ hσ.1 J hJ
  have := Hecke.cornerModule_isScalarTower μ ρ hρ.1 J hJ
  have := Hecke.cornerModule_isScalarTower μ σ hσ.1 J hJ
  have := hρ.2 J
  have := hσ.2 J
  let M := fixedVectors ρ J.toSubgroup
  let N := fixedVectors σ J.toSubgroup
  let R := Hecke.HeckeAlgebra.Corner μ J hJ
  have hneρ : M ≠ ⊥ := fun h => hv ((Submodule.mem_bot ℂ).mp (h ▸ hvJ))
  have hneσ : N ≠ ⊥ := fun h => hw ((Submodule.mem_bot ℂ).mp (h ▸ hwJ))
  have := CompactCoefficientClass.isSimpleModule_fixedVectors μ ρ hρ.1 J hJ hρi hneρ
  have := CompactCoefficientClass.isSimpleModule_fixedVectors μ σ hσ.1 J hJ hσi hneσ
  by_contra hne
  have hneCorner : ¬ Nonempty (M ≃ₗ[R] N) := by
    rintro ⟨e⟩
    let a : M := ⟨v, hvJ⟩
    have ha : (a : V) ≠ 0 := hv
    have hb : (e a : W) ≠ 0 := fun h => ha (congrArg Subtype.val (e.map_eq_zero_iff.mp (Subtype.ext h)))
    apply hne
    refine Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff μ J hJ hρ.1 hρi hσ.1 hσi
      a (e a) ha hb fun r => ?_
    have her : e (Hecke.cornerAction μ ρ hρ.1 J hJ r a) =
        Hecke.cornerAction μ σ hσ.1 J hJ r (e a) := e.map_smul r a
    rw [← her, e.map_eq_zero_iff]
  let U := fixedVectorsTwistEquiv hαJ A
  obtain ⟨r, hrM, hrN⟩ := exists_actions_of_nonisomorphic_simpleModules hneCorner U.symm.toLinearMap
  change Hecke.cornerAction μ ρ hρ.1 J hJ r = U.symm.toLinearMap at hrM
  change Hecke.cornerAction μ σ hσ.1 J hJ r = 0 at hrN
  have htrace := hdist (Hecke.HeckeAlgebra.toTestFunction μ
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ J hJ r))
  rw [twistedDistribution_corner μ hρ A J hJ hαJ r,
    twistedDistribution_corner μ hσ B J hJ hαJ r, hrM, hrN] at htrace
  have he : U.symm.toLinearMap.comp (fixedVectorsTwistEquiv hαJ A).toLinearMap =
      (LinearMap.id : Module.End ℂ M) := by
    exact LinearMap.ext U.symm_apply_apply
  rw [he, LinearMap.zero_comp, map_zero, mul_zero, LinearMap.trace_id, Nat.cast_eq_zero] at htrace
  have : Nontrivial M := IsSimpleModule.nontrivial R M
  exact Module.finrank_pos.ne' htrace

section GeneralLinear

variable {F : Type*} [Field F] [TopologicalSpace F]
  {E : Type*} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ}
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The two-character separation theorem for the entrywise twist of a cyclic algebra. -/
theorem nonempty_equiv_of_sigmaTwistedDistributions_proportional
    {α : E ≃ₐ[F] E} {d : ℕ} (hcyc : IsCyclicAlgebra α d)
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
    {ρ : Representation ℂ (GeneralLinear n E) V} {σ : Representation ℂ (GeneralLinear n E) W}
    (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ) (hρi : ρ.IsIrreducible) (hσi : σ.IsIrreducible)
    (A : SigmaIntertwiner α n ρ) (B : SigmaIntertwiner α n σ) (c : ℂ)
    (h : ∀ f : SchwartzBruhat (GeneralLinear n E),
      twistedDistribution μ ρ hρ A.toLinearMap f = c * twistedDistribution μ σ hσ B.toLinearMap f) :
    Nonempty (ρ.Equiv σ) := by
  let action : (E ≃ₐ[F] E) →* MulAut (GeneralLinear n E) :=
    { toFun := fun γ => entrywiseAut γ n
      map_one' := MulEquiv.ext entrywiseAut_one_apply
      map_mul' := fun γ δ => MulEquiv.ext (entrywiseAut_mul_apply γ δ) }
  have hc : Continuous (entrywiseAut α n) := (GeneralLinear.mapContinuous α.toRingHom
    (IsModuleTopology.continuous_of_linearMap α.toLinearMap)).continuous
  have hp : (action α) ^ d = 1 := by rw [← map_pow, hcyc.pow_eq_one, map_one]
  exact twistedCharacterSeparation _ μ (action α) hc d hcyc.pos hp V W ρ σ hρ hσ hρi hσi A B c h

end GeneralLinear

end Langlands.BaseChange
