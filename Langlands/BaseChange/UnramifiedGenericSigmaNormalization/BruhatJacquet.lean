import Langlands.BaseChange.UnramifiedGenericSigmaNormalization.PrincipalSeries
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.GroupScheme.Unipotent.CharZeroPeriodic
import Langlands.Representation.Geometric.OpenSupportOrbitQuotient
import Langlands.Representation.Geometric.ParabolicSupportTransport
import Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Whittaker.UnipotentOrbitProof

/-!
# The canonical action on the principal-series Jacquet quotient

On an upper-unipotent orbit, compact induction identifies the coinvariant map with
quotient integration. Finite-order pullback preserves that integral. Successive orbit
restrictions then make the action unipotent, so finite order forces the identity.
-/

noncomputable section

namespace Langlands.BaseChange.UnramifiedSigma

open MeasureTheory MeasureTheory.Measure CategoryTheory
open Representation (Coinvariants)
open scoped NNReal

universe uG uW uF uE

section CompactOrbit

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [T2Space Γ] [LocallyCompactSpace Γ]

private def iterateAut (α : Γ ≃ₜ* Γ) : ℕ → Γ ≃ₜ* Γ
  | 0 => ContinuousMulEquiv.refl Γ
  | k + 1 => α.trans (iterateAut α k)

omit [T2Space Γ] in
private theorem haarChar_eq_one_of_periodic [MeasurableSpace Γ] [BorelSpace Γ]
    (α : Γ ≃ₜ* Γ) {l : ℕ} (hl : l ≠ 0) (hα : ∀ g : Γ, (⇑α)^[l] g = g) :
    mulEquivHaarChar α = 1 := by
  have hiter (k : ℕ) (x : Γ) : iterateAut α k x = (⇑α)^[k] x := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih => exact ih (α x)
  have hpow (k : ℕ) : mulEquivHaarChar (iterateAut α k) = mulEquivHaarChar α ^ k := by
    induction k with
    | zero => exact mulEquivHaarChar_refl
    | succ k ih =>
      change mulEquivHaarChar (α.trans (iterateAut α k)) = _
      rw [mulEquivHaarChar_trans, ih, pow_succ']
  have h := hpow l
  have he : iterateAut α l = ContinuousMulEquiv.refl Γ :=
    DFunLike.ext _ _ fun x => (hiter l x).trans (hα x)
  rw [he, mulEquivHaarChar_refl] at h
  exact (pow_eq_one_iff_of_nonneg (show 0 ≤ mulEquivHaarChar α by positivity) hl).mp h.symm

/-- A periodic group automorphism preserving the inducing subgroup leaves the class of
an actual compact section unchanged under pullback with unchanged coefficient values. -/
private theorem compactCoinvariant_eq_of_precompose
    (hBasis : ∀ O : Set Γ, IsOpen O → (1 : Γ) ∈ O →
      ∃ J : OpenSubgroup Γ, IsCompact (J : Set Γ) ∧ (J : Set Γ) ⊆ O)
    (hCover : ∀ g : Γ, ∃ J : OpenSubgroup Γ, IsCompact (J : Set Γ) ∧ g ∈ J)
    (H : Subgroup Γ) (hH : IsClosed (H : Set Γ)) (α : Γ ≃ₜ* Γ)
    (hHα : ∀ g, α g ∈ H ↔ g ∈ H) {l : ℕ} (hl : l ≠ 0)
    (hα : ∀ g : Γ, (⇑α)^[l] g = g)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ H W) (hτ : IsSmooth τ)
    (f f' : Induction.CompactFunctions H τ)
    (hf : ∀ g : Γ, Induction.eval H τ f'.val g = Induction.eval H τ f.val (α g)) :
    Coinvariants.mk (Induction.compactInduced H τ) f' =
      Coinvariants.mk (Induction.compactInduced H τ) f := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  borelize Γ
  borelize ↥H
  borelize (QuotientIntegration.LeftQuotient H)
  let μΓ : Measure Γ := haar
  let μH : Measure H := haar
  have hr := Haar.compactOpenCoverUnimodularity hCover
  let : IsMulRightInvariant μΓ := hr.1 μΓ
  let : IsMulRightInvariant μH := hr.2 H hH μH
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists H hH μΓ μH
  let : ν.Regular := hν.regular
  let β := QuotientIntegration.subgroupAutomorphism H α hHα
  have hβ : Function.Semiconj (H.subtype : H → Γ) (⇑β) (⇑α) := fun _ => rfl
  have hm : Measure.map (QuotientIntegration.quotientAutomorphism H α hHα) ν = ν := by
    rw [hν.map_quotientAutomorphism H hH α hHα, haarChar_eq_one_of_periodic α hl hα,
      haarChar_eq_one_of_periodic β hl (fun x => Subtype.ext ((hβ.iterate_right l x).trans (hα x)))]
    simp
  apply (Induction.compactCoinvariantIntegralBijective hBasis H hH μΓ μH ν hν W τ hτ).1
  rw [Induction.compactCoinvariantDesc_mk, Induction.compactCoinvariantDesc_mk]
  let e := QuotientIntegration.quotientAutomorphism H α hHα
  have hsimple : Induction.quotientCoinvariantSimple H τ f' =
      (Induction.quotientCoinvariantSimple H τ f).comp e e.continuous.measurable := by
    ext q
    induction q using Quotient.inductionOn with
    | h g =>
      change Coinvariants.mk τ (Induction.eval H τ f'.val g) =
        Coinvariants.mk τ (Induction.eval H τ f.val (α g))
      rw [hf]
  rw [Induction.compactCoinvariantIntegral_apply, Induction.compactCoinvariantIntegral_apply,
    hsimple, HarmonicAnalysis.AlgebraicIntegral.integral_comp, hm]

end CompactOrbit

section Matrices

open GeneralLinear Correspondence Unramified SphericalExistence Geometric

variable {p : ℕ} [Fact p.Prime]

local instance bruhatFieldTopology (L : PadicField.{u} p) : TopologicalSpace L.Carrier :=
  L.canonicalTopologicalData.topology

variable (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) {r : ℕ} (z : Fin (r + 1) → ℂˣ)

local notation "K" => E.Carrier
local notation "G" => GeneralLinear (r + 1) K
local notation "B" => borelShape r
set_option quotPrecheck false in
local notation "P" => (B).parabolic K
local notation "U" => upperUnipotent (r + 1) K
local notation "I" => principalSeriesOfTuple E z
local notation "τ" => borelInducing E z
local notation "T" => E.canonicalTopologicalData

local instance bruhatGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n K) :=
  (T).generalLinearTopology n

local instance bruhatGLTopologicalGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n K) :=
  (T).generalLinearTopologicalGroup n

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
/-- Entrywise field action preserves the full upper-unipotent subgroup. -/
theorem entrywiseAut_mem_upperUnipotent_iff (g : G) :
    entrywiseAut σ (r + 1) g ∈ U ↔ g ∈ U := by
  change (∀ i j : Fin (r + 1), j < i → σ (g i j) = 0) ∧
    (∀ i : Fin (r + 1), σ (g i i) = 1) ↔
    (∀ i j : Fin (r + 1), j < i → g i j = 0) ∧ (∀ i : Fin (r + 1), g i i = 1)
  simp only [map_eq_zero_iff _ σ.injective, map_eq_one_iff _ σ.injective]

private def matrixAut : G ≃ₜ* G := by
  let : ValuativeRel K := (T).valuativeRel
  let : IsNonarchimedeanLocalField K := (T).localField
  let : IsModuleTopology F.Carrier K := PadicField.padicTowerModuleTopology p F E
  exact
    { toMulEquiv := entrywiseAut σ (r + 1)
      continuous_toFun := continuous_entrywiseAut σ (r + 1)
      continuous_invFun := continuous_entrywiseAut_symm σ (r + 1) }

/-- Entrywise field action as a continuous automorphism of the full upper unipotent. -/
def upperUnipotentAut : U ≃ₜ* U :=
  QuotientIntegration.subgroupAutomorphism U (matrixAut F E σ)
    (entrywiseAut_mem_upperUnipotent_iff F E σ)

@[simp]
theorem upperUnipotentAut_coe (u : U) :
    ((upperUnipotentAut F E σ u : U) : G) = entrywiseAut σ (r + 1) u := rfl

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem entrywiseAut_permutation (w : Equiv.Perm (Fin (r + 1))) :
    entrywiseAut σ (r + 1) (permutation (r + 1) K w) = permutation (r + 1) K w := by
  ext i j
  rw [entrywiseAut_apply_apply, permutation_entry]
  split <;> simp

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem iterate_entrywiseAut (k : ℕ) (g : G) :
    (⇑(entrywiseAut σ (r + 1)))^[k] g = entrywiseAut (σ ^ k) (r + 1) g := by
  induction k with
  | zero => exact (entrywiseAut_one_apply g).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', entrywiseAut_mul_apply]

private theorem iterate_upperUnipotentAut {l : ℕ} (hσ : σ ^ l = 1) (u : U) :
    (⇑(upperUnipotentAut F E σ))^[l] u = u := by
  have hs : Function.Semiconj ((U).subtype : U → G) (⇑(upperUnipotentAut F E σ))
      (⇑(entrywiseAut σ (r + 1))) := fun _ => rfl
  apply Subtype.ext
  rw [show (↑((⇑(upperUnipotentAut F E σ))^[l] u) : G) = _ from hs.iterate_right l u,
    iterate_entrywiseAut F E σ, hσ, entrywiseAut_one_apply]
  rfl

private theorem orbit_stabilizer_aut (w : G) (hw : entrywiseAut σ (r + 1) w = w) (u : U) :
    upperUnipotentAut F E σ u ∈ orbitStabilizer P U w ↔ u ∈ orbitStabilizer P U w := by
  change w⁻¹ * entrywiseAut σ (r + 1) u * w ∈ P ↔ w⁻¹ * (u : G) * w ∈ P
  have h := entrywiseAut_mem_parabolic_iff σ B (w⁻¹ * (u : G) * w)
  rwa [map_mul, map_mul, map_inv, hw] at h

private theorem isSmooth_borelInducing : IsSmooth τ := by
  let : ValuativeRel K := (T).valuativeRel
  let : IsNonarchimedeanLocalField K := (T).localField
  exact (B).isSmooth_inducingRepresentation ((T).leviHalfCharacter B)
    (SmoothRep.of ((B).blockTensor (blockCharacters E z))
      (FiniteTensor.isSmooth_external _ (fun i => (blockCharacters_isAdmissible E z i).1)))

set_option maxHeartbeats 800000 in
private theorem orbitCoinvariant_eq_of_eval {l : ℕ} (hl : l ≠ 0) (hσ : σ ^ l = 1)
    (w : G) (hw : entrywiseAut σ (r + 1) w = w)
    (f f' : Induction.CompactFunctions (orbitStabilizer P U w)
      ((τ).comp (stabilizerToInducing P U w)))
    (hf : ∀ u : U, Induction.eval _ _ f'.val u =
      Induction.eval _ _ f.val (upperUnipotentAut F E σ u)) :
    Coinvariants.mk (Induction.compactInduced _ _) f' =
      Coinvariants.mk (Induction.compactInduced _ _) f := by
  let : ValuativeRel K := (T).valuativeRel
  let : IsNonarchimedeanLocalField K := (T).localField
  let : T2Space U := E.canonicalUpperUnipotentT2Space (r + 1)
  let : LocallyCompactSpace U := E.canonicalUpperUnipotentLocallyCompactSpace (r + 1)
  refine compactCoinvariant_eq_of_precompose ?_ (RankinSelberg.unipotent_exists_compact_open K r)
    _ (isClosed_orbitStabilizer P U w ((B).isClosed_parabolic K)) (upperUnipotentAut F E σ)
    (orbit_stabilizer_aut F E σ w hw) hl (iterate_upperUnipotentAut F E σ hσ) _ ?_ f f' hf
  · intro O hO h1
    exact ⟨(E.canonicalUpperUnipotentCompactOpen (r + 1) O (hO.mem_nhds h1)).val,
      (E.canonicalUpperUnipotentCompactOpen (r + 1) O (hO.mem_nhds h1)).property⟩
  · apply isSmooth_comp _ _ (isSmooth_borelInducing E z)
    exact ((continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const).subtype_mk _

/-- The actual Borel Jacquet quotient as coinvariants for the full upper-unipotent
matrix subgroup. The linear equivalence is the identity on vector classes. -/
def borelCoinvariantsEquiv {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) :
    (B).JacquetModule ρ ≃ₗ[ℂ] Coinvariants (ρ.comp (U).subtype) :=
  ((B).jacquetModuleEquiv ρ).trans (Submodule.quotEquivOfEq _ _
    (congrArg (Jacquet.relations ρ) (BlockShape.singletons_unipotentSubgroup K)))

@[simp]
theorem borelCoinvariantsEquiv_mk {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (x : X) :
    borelCoinvariantsEquiv E ρ ((B).jacquetMk ρ x) =
      Coinvariants.mk (ρ.comp (U).subtype) x := rfl

private theorem support_principalIntertwiner {m : ℕ} (s : OrderedDoubleCosets P U m)
    (hw : ∀ i, entrywiseAut σ (r + 1) (s.representative i) = s.representative i)
    (i : Fin (m + 1)) (f : Induction.SmoothFunctions P τ)
    (hf : ∀ x, Induction.eval P τ f x ≠ 0 → Induction.quotientMap P x ∈ s.initialOrbits i) :
    ∀ x, Induction.eval P τ (principalIntertwiner F E σ z f) x ≠ 0 →
      Induction.quotientMap P x ∈ s.initialOrbits i := by
  intro x hx
  rw [eval_principalIntertwiner] at hx
  obtain ⟨j, hj, u, hu⟩ := hf _ hx
  let α := matrixAut (r := r) F E σ
  let q := QuotientIntegration.quotientAutomorphism P α (entrywiseAut_mem_parabolic_iff σ B)
  have he := congrArg q hu
  change Induction.quotientMap P
    (α ((s.representative j)⁻¹ * (u : G))) = Induction.quotientMap P (α (α.symm x)) at he
  rw [map_mul, map_inv, show α (s.representative j) = _ from hw j, α.apply_symm_apply] at he
  exact ⟨j, hj, upperUnipotentAut F E σ u, he⟩

set_option maxHeartbeats 1800000 in
private theorem principal_difference_lowers_support {l m : ℕ} (hl : l ≠ 0) (hσ : σ ^ l = 1)
    (s : OrderedDoubleCosets P U m)
    (hw : ∀ i, entrywiseAut σ (r + 1) (s.representative i) = s.representative i)
    (i : Fin m) (f : Induction.SmoothFunctions P τ)
    (hf : ∀ x, Induction.eval P τ f x ≠ 0 → Induction.quotientMap P x ∈ s.initialOrbits i.succ) :
    ∃ f' : Induction.SmoothFunctions P τ,
      (∀ x, Induction.eval P τ f' x ≠ 0 → Induction.quotientMap P x ∈
        s.initialOrbits i.castSucc) ∧
      (B).jacquetMk I (principalIntertwiner F E σ z f - f) = (B).jacquetMk I f' := by
  let : ValuativeRel K := (T).valuativeRel
  let : IsNonarchimedeanLocalField K := (T).localField
  let : T2Space G := (T).generalLinearT2Space (r + 1)
  let : NonarchimedeanGroup G := (T).generalLinearNonarchimedean (r + 1)
  let : LocallyCompactSpace G := (T).generalLinearLocallyCompactSpace (r + 1)
  let : SigmaCompactSpace G := (T).generalLinearSigmaCompactSpace (r + 1)
  let : CompactSpace (Induction.LeftQuotient P) := Parabolic.parabolicQuotientCompact E (T) B
  have hP : IsClosed (P : Set G) := (B).isClosed_parabolic K
  have hU : IsClosed (U : Set G) := UpperUnipotent.isClosed
  let A : Induction.SmoothRep ℂ P := SmoothRep.of τ (isSmooth_borelInducing E z)
  let w := s.representative i
  let pair : OpenOrbitSupportPair P U w :=
    { lower := s.initialOrbits i.castSucc
      upper := s.initialOrbits i.succ
      lower_invariant := fun u _ h => s.initialOrbits_right_invariant _ u h
      upper_invariant := fun u _ h => s.initialOrbits_right_invariant _ u h
      lower_open := s.initial_open _
      upper_open := s.initial_open _
      lower_subset_upper := s.initialOrbits_monotone (Fin.castSucc_le_succ i)
      difference := s.initialOrbits_succ_diff i }
  let S := supportSubfunctor (R := ℂ) P U pair.upper pair.upper_invariant
  let ψ := S.representation A
  let H := orbitStabilizer P U w
  let πw := Induction.compactInduced H ((τ).comp (stabilizerToInducing P U w))
  let res : ψ.ρ.IntertwiningMap πw := ((pair.restriction hP hU).app A).hom
  have hsurj : Function.Surjective res := pair.restriction_surjective hP hU A
  let f₁ : ψ := ⟨⟨f, (Induction.isClosed_quotientSupport P τ f).isCompact⟩, hf⟩
  let f₂' := principalIntertwiner F E σ z f
  let f₂ : ψ := ⟨⟨f₂', (Induction.isClosed_quotientSupport P τ f₂').isCompact⟩,
    support_principalIntertwiner F E σ z s hw i.succ f hf⟩
  have hpw : entrywiseAut σ.symm (r + 1) w = w := by
    change (entrywiseAut σ (r + 1)).symm w = w
    apply (entrywiseAut σ (r + 1)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (hw i).symm
  have hpow : σ.symm ^ l = 1 := by
    change (σ⁻¹) ^ l = 1
    rw [inv_pow, hσ, inv_one]
  have hmk : Coinvariants.mk πw (res f₂) = Coinvariants.mk πw (res f₁) := by
    apply orbitCoinvariant_eq_of_eval F E σ.symm z hl hpow w hpw
    intro u
    change Induction.eval P τ f₂' (w⁻¹ * (u : G)) =
      Induction.eval P τ f (w⁻¹ * (upperUnipotentAut F E σ.symm u : G))
    rw [eval_principalIntertwiner, map_mul, map_inv, hpw, upperUnipotentAut_coe]
  have hker : res (f₂ - f₁) ∈ Coinvariants.ker πw :=
    (Coinvariants.mk_eq_zero πw).mp (by rw [map_sub, map_sub, hmk, sub_self])
  rw [← coinvariants_ker_map_of_surjective res hsurj] at hker
  obtain ⟨t, ht, hres⟩ := hker
  let j : ψ.ρ.IntertwiningMap ((I).comp (U).subtype) :=
    { toLinearMap := (Induction.compactInclusion P τ).toLinearMap ∘ₗ
        (S.inclusion.app A).hom.toLinearMap
      isIntertwining' := fun _ => rfl }
  have hqt : (B).jacquetMk I (j t) = 0 := by
    apply (borelCoinvariantsEquiv E I).injective
    rw [borelCoinvariantsEquiv_mk, map_zero]
    exact (congrArg (Coinvariants.map ψ.ρ ((I).comp (U).subtype) j)
      ((Coinvariants.mk_eq_zero ψ.ρ).mpr ht)).trans (map_zero _)
  let h := f₂ - f₁ - t
  have hzero : res h = 0 := by
    change res (f₂ - f₁ - t) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hres.symm
  have hsupp := (pair.restriction_kernel hP hU A h).mpr hzero
  refine ⟨j h, hsupp, ?_⟩
  change (B).jacquetMk I (f₂' - f) = (B).jacquetMk I ((f₂' - f) - j t)
  rw [map_sub ((B).jacquetMk I) (f₂' - f) (j t), hqt, sub_zero]

set_option maxHeartbeats 2200000 in
/-- The canonical pullback fixes the class of every vector in the actual principal-series
Borel Jacquet quotient. -/
theorem principalIntertwiner_jacquet {l : ℕ} (hcyc : IsCyclicAlgebra σ l)
    (f : Induction.SmoothFunctions P τ) :
    (B).jacquetMk I (principalIntertwiner F E σ z f) = (B).jacquetMk I f := by
  let A := principalIntertwiner F E σ z
  let A₀ := A.toLinearMap
  let J := jacquetSigmaIntertwiner σ B A
  let J₀ := J.toLinearMap
  let Δ := J₀ - 1
  let q := (B).jacquetMk I
  have hΔ (v : Induction.SmoothFunctions P τ) : Δ (q v) = q (A v - v) := by
    rw [map_sub]
    rfl
  obtain ⟨_, m, s, e, he⟩ := Whittaker.unipotentOrbit p E r B
  have hw (i : Fin m) : entrywiseAut σ (r + 1) (s.representative i) = s.representative i := by
    rw [he i, entrywiseAut_permutation F E σ]
  have hnil (i : Fin (m + 1)) : ∀ v : Induction.SmoothFunctions P τ,
      (∀ x, Induction.eval P τ v x ≠ 0 → Induction.quotientMap P x ∈ s.initialOrbits i) →
      (Δ ^ i.val) (q v) = 0 := by
    induction i using Fin.induction with
    | zero =>
      intro v hv
      have hzero : v = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change Induction.eval P τ v g = 0
        by_contra h
        simpa [s.initialOrbits_zero] using hv g h
      rw [hzero, map_zero, map_zero]
    | succ i ih =>
      intro v hv
      obtain ⟨v', hv', hq⟩ := principal_difference_lowers_support F E σ z (l := l) hcyc.pos.ne'
        hcyc.pow_eq_one s hw i v hv
      calc
        (Δ ^ i.succ.val) (q v) = (Δ ^ i.val) (Δ (q v)) :=
          congrArg (fun L : Module.End ℂ ((B).JacquetModule I) => L (q v)) (pow_succ Δ i.val)
        _ = (Δ ^ i.val) (q v') :=
          congrArg (fun x => (Δ ^ i.val) x) ((hΔ v).trans hq)
        _ = 0 := ih v' hv'
  have hpowJ (k : ℕ) (v : Induction.SmoothFunctions P τ) :
      (J₀ ^ k) (q v) = q ((A₀ ^ k) v) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        (J₀ ^ (k + 1)) (q v) = J₀ ((J₀ ^ k) (q v)) :=
          congrArg (fun L : Module.End ℂ ((B).JacquetModule I) => L (q v)) (pow_succ' J₀ k)
        _ = J₀ (q ((A₀ ^ k) v)) := congrArg J₀ ih
        _ = q ((A₀ ^ (k + 1)) v) :=
          congrArg (fun L : Module.End ℂ (Induction.SmoothFunctions P τ) => q (L v))
            (pow_succ' A₀ k).symm
  have hpowA (k : ℕ) (v : Induction.SmoothFunctions P τ) (g : G) :
      Induction.eval P τ ((A₀ ^ k) v) g =
        Induction.eval P τ v ((⇑(entrywiseAut σ.symm (r + 1)))^[k] g) := by
    induction k generalizing g with
    | zero => rfl
    | succ k ih =>
      calc
        Induction.eval P τ ((A₀ ^ (k + 1)) v) g =
            Induction.eval P τ (A ((A₀ ^ k) v)) g :=
          congrArg (fun L : Module.End ℂ (Induction.SmoothFunctions P τ) =>
            Induction.eval P τ (L v) g) (pow_succ' A₀ k)
        _ = _ := (eval_principalIntertwiner F E σ z ((A₀ ^ k) v) g).trans
          (ih (entrywiseAut σ.symm (r + 1) g))
  have hinv : σ.symm ^ l = 1 := by
    change (σ⁻¹) ^ l = 1
    rw [inv_pow, hcyc.pow_eq_one, inv_one]
  have hperiod : (J₀ ^ l) (q f) = q f := by
    rw [hpowJ]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change Induction.eval P τ ((A₀ ^ l) f) g = Induction.eval P τ f g
    rw [hpowA, iterate_entrywiseAut F E σ.symm, hinv, entrywiseAut_one_apply]
  have hz : (Δ ^ m) (q f) = 0 :=
    hnil (Fin.last m) f (fun x _ => by rw [s.initialOrbits_top]; trivial)
  exact GroupScheme.Unipotent.apply_eq_self_of_periodic_of_pow_sub_one_eq_zero
    hcyc.pos.ne' hperiod hz

end Matrices

end Langlands.BaseChange.UnramifiedSigma
