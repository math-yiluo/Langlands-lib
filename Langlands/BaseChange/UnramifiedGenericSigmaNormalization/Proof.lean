import Langlands.BaseChange.UnramifiedGenericSigmaNormalization.BruhatJacquet
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Whittaker.PadicCharacterIndependence
import Langlands.Representation.Whittaker.SubquotientCoefficientModelInclusionProof
import Langlands.Representation.Whittaker.CoefficientMapNonvanishing
import Langlands.Representation.Whittaker.ModelGenericSocleProof

/-!
# The normalized σ-action on a generic unramified constituent

A trace character gives a σ-invariant Whittaker character. The coefficient quotient of the
principal series is σ-stable and its least nonzero subrepresentation realizes the generic
constituent. Coinvariant exactness and compact fixed-vector exactness transfer both identities
through this quotient and inclusion.
-/

noncomputable section

namespace Langlands.BaseChange

open Correspondence GeneralLinear Unramified Whittaker HarmonicAnalysis
open Representation (Coinvariants IntertwiningMap)
open UnramifiedSigma

universe uF uE uV uW

section TwistedMaps

variable {F : Type uF} [Field F] {E : Type uE} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GeneralLinear n E) V} {τ : Representation ℂ (GeneralLinear n E) W}

local notation "α" => entrywiseAut σ n

private theorem sigma_on_quotient (A : SigmaIntertwiner σ n ρ)
    (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (hker : ∀ v, q (A v) = 0 ↔ q v = 0) :
    ∃ D : SigmaIntertwiner σ n τ, ∀ v, D (q v) = q (A v) := by
  have hle : LinearMap.ker q.toLinearMap ≤ LinearMap.ker (q.toLinearMap ∘ₗ A.toLinearMap) :=
    fun v hv => (hker v).mpr hv
  let D := q.toLinearMap.liftOfSurjective hq ⟨q.toLinearMap ∘ₗ A.toLinearMap, hle⟩
  have hD (v : V) : D (q v) = q (A v) := LinearMap.equivOfSurjective_apply hq hle
  have hD0 (w : W) (hz : D w = 0) : w = 0 := by
    obtain ⟨v, rfl⟩ := hq w
    exact (hker v).mp ((hD v).symm.trans hz)
  have hb : Function.Bijective D := by
    refine ⟨fun x y he => sub_eq_zero.mp (hD0 (x - y) (by rw [map_sub, he, sub_self])), ?_⟩
    intro w
    obtain ⟨v, rfl⟩ := hq w
    obtain ⟨v', rfl⟩ := A.surjective v
    exact ⟨q v', hD v'⟩
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective D hb) (fun g => ?_), hD⟩
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hq w
  change D (τ g (q v)) = τ (α g) (D (q v))
  rw [← q.isIntertwining, hD, hD, show A (ρ g v) = ρ (α g) (A v) from
    LinearMap.congr_fun (A.comp_apply_eq g) v, q.isIntertwining]

private theorem least_stable_forward (S : Subrepresentation ρ)
    (hS : S ≠ ⊥) (hmin : ∀ T : Subrepresentation ρ, T ≠ ⊥ → S ≤ T)
    (β : GeneralLinear n E ≃* GeneralLinear n E) (D : V ≃ₗ[ℂ] V)
    (hD : ∀ g v, D (ρ g v) = ρ (β g) (D v)) : ∀ v ∈ S, D v ∈ S := by
  let preimage : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap D.toLinearMap
      apply_mem_toSubmodule := fun g {v} hv => by
        change D v ∈ S at hv
        change D (ρ g v) ∈ S
        rw [hD]
        exact S.apply_mem_toSubmodule _ hv }
  have hne : preimage ≠ ⊥ := by
    obtain ⟨w, hw⟩ := exists_ne_zero_of_subrepresentation_ne_bot S hS
    intro hbot
    have hm : D.symm w.val ∈ preimage := by
      change D (D.symm w.val) ∈ S
      rw [D.apply_symm_apply]
      exact w.property
    rw [hbot] at hm
    exact hw (Subtype.ext (D.symm.map_eq_zero_iff.mp ((Submodule.mem_bot ℂ).mp hm)))
  exact hmin preimage hne

private theorem least_stable (S : Subrepresentation ρ)
    (hS : S ≠ ⊥) (hmin : ∀ T : Subrepresentation ρ, T ≠ ⊥ → S ≤ T)
    (A : SigmaIntertwiner σ n ρ) (v : V) : A v ∈ S ↔ v ∈ S := by
  have hA (g : GeneralLinear n E) (x : V) : A (ρ g x) = ρ (α g) (A x) :=
    LinearMap.congr_fun (A.comp_apply_eq g) x
  have hA' (g : GeneralLinear n E) (x : V) :
      A.toLinearEquiv.symm (ρ g x) = ρ ((α).symm g) (A.toLinearEquiv.symm x) := by
    apply A.toLinearEquiv.injective
    change A.toLinearEquiv (A.toLinearEquiv.symm (ρ g x)) =
      A (ρ ((α).symm g) (A.toLinearEquiv.symm x))
    rw [LinearEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
    exact congrArg (ρ g) (A.toLinearEquiv.apply_symm_apply x).symm
  refine ⟨fun hv => ?_, least_stable_forward S hS hmin α A.toLinearEquiv hA v⟩
  have h := least_stable_forward S hS hmin (α).symm A.toLinearEquiv.symm hA' (A v) hv
  change A.toLinearEquiv.symm (A.toLinearEquiv v) ∈ S at h
  simpa only [LinearEquiv.symm_apply_apply] using h

private theorem sigma_on_injection (D : SigmaIntertwiner σ n τ)
    (j : ρ.IntertwiningMap τ) (hj : Function.Injective j)
    (hstable : ∀ w, D w ∈ j.range ↔ w ∈ j.range) :
    ∃ A : SigmaIntertwiner σ n ρ, ∀ v, j (A v) = D (j v) := by
  let e := LinearEquiv.ofInjective j.toLinearMap hj
  let B := (D.toLinearMap ∘ₗ j.toLinearMap).codRestrict (LinearMap.range j.toLinearMap)
    (fun v => (hstable (j v)).mpr ⟨v, rfl⟩)
  let A := e.symm.toLinearMap ∘ₗ B
  have hA (v : V) : j (A v) = D (j v) :=
    congrArg Subtype.val (e.apply_symm_apply (B v))
  have hb : Function.Bijective A := by
    refine ⟨fun v w he => hj (D.injective ((hA v).symm.trans ((congrArg j he).trans (hA w)))), ?_⟩
    intro v
    have hm : D.toLinearEquiv.symm (j v) ∈ j.range := by
      apply (hstable _).mp
      change D.toLinearEquiv (D.toLinearEquiv.symm (j v)) ∈ j.range
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hm
    change j w = D.toLinearEquiv.symm (j v) at hw
    refine ⟨w, hj ?_⟩
    rw [hA, hw]
    exact D.toLinearEquiv.apply_symm_apply (j v)
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective A hb) (fun g => ?_), hA⟩
  apply LinearMap.ext
  intro v
  change A (ρ g v) = ρ (α g) (A v)
  apply hj
  rw [hA, j.isIntertwining, j.isIntertwining, hA]
  exact LinearMap.congr_fun (D.comp_apply_eq g) (j v)

private theorem range_eq_least (j : ρ.IntertwiningMap τ) [ρ.IsIrreducible]
    (hj : j.range ≠ ⊥) (S : Subrepresentation τ) (hS : S ≠ ⊥)
    (hmin : ∀ T : Subrepresentation τ, T ≠ ⊥ → S ≤ T) : j.range = S := by
  have hle := hmin j.range hj
  let preimage : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap j.toLinearMap
      apply_mem_toSubmodule := fun g {v} hv => by
        change j v ∈ S at hv
        change j (ρ g v) ∈ S
        rw [j.isIntertwining]
        exact S.apply_mem_toSubmodule g hv }
  have hpre : preimage ≠ ⊥ := by
    obtain ⟨w, hw⟩ := exists_ne_zero_of_subrepresentation_ne_bot S hS
    obtain ⟨v, hv⟩ := hle w.property
    change j v = w.val at hv
    have hvpre : v ∈ preimage := by
      change j v ∈ S
      rw [hv]
      exact w.property
    intro hbot
    rw [hbot] at hvpre
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).mp hvpre
    apply hw
    apply Subtype.ext
    rw [← hv, hv0, map_zero]
    rfl
  have htop : preimage = ⊤ := (eq_bot_or_eq_top preimage).resolve_left hpre
  refine le_antisymm ?_ hle
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ preimage := htop ▸ (show v ∈ (⊤ : Subrepresentation ρ) from trivial)
  exact hv

end TwistedMaps

section PadicFields

variable {p : ℕ} [Fact p.Prime]

local instance normalizationFieldTopology (L : PadicField.{u} p) : TopologicalSpace L.Carrier :=
  L.canonicalTopologicalData.topology

variable (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) {r : ℕ}

local notation "K" => E.Carrier
local notation "G" => GeneralLinear (r + 1) K
local notation "U" => upperUnipotent (r + 1) K
local notation "T" => E.canonicalTopologicalData
local notation "α" => entrywiseAut σ (r + 1)

local instance normalizationGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n K) :=
  (T).generalLinearTopology n

local instance normalizationGLTopologicalGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n K) :=
  (T).generalLinearTopologicalGroup n

private theorem exists_sigmaInvariant_additiveCharacter :
    ∃ χ : UnitaryAdditiveCharacter K, ∀ x : K, χ (σ x) = χ x := by
  obtain ⟨ψ⟩ := padicUnitaryAdditiveCharacterExists F F.canonicalTopologicalData
  refine ⟨F.canonicalTopologicalData.traceCharacter (T) ψ, fun x => ?_⟩
  rw [PadicField.TopologicalData.traceCharacter_apply, PadicField.TopologicalData.traceCharacter_apply,
    Algebra.trace_eq_of_algEquiv σ]

private theorem standardCharacter_upperUnipotentAut (χ : UnitaryAdditiveCharacter K)
    (hχ : ∀ x : K, χ (σ x) = χ x) (u : U) :
    standardCharacter χ r (upperUnipotentAut F E σ u) = standardCharacter χ r u := by
  apply Units.ext
  rw [standardCharacter_apply, standardCharacter_apply]
  simp only [upperUnipotentAut_coe, entrywiseAut_apply_apply, ← map_sum]
  exact congrArg (fun z : Circle => (z : ℂ)) (hχ _)

set_option maxHeartbeats 850000 in
private theorem modelMap_kernel_sigma
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G W}
    (χ : UnitaryAdditiveCharacter K) (hχ : ∀ x : K, χ (σ x) = χ x)
    (A : SigmaIntertwiner σ (r + 1) ρ) (L : glFunctionals χ r ρ) (hL : L.val ≠ 0)
    (e : glFunctionals χ r ρ ≃ₗ[ℂ] ℂ) (v : W) :
    modelMap ρ L (A v) = 0 ↔ modelMap ρ L v = 0 := by
  let L' : glFunctionals χ r ρ :=
    ⟨L.val.comp A.toLinearMap, fun u x => by
      have hA := LinearMap.congr_fun (A.comp_apply_eq (u : G)) x
      change A (ρ (u : G) x) = ρ (α u) (A x) at hA
      change L.val (A (ρ (u : G) x)) = (standardCharacter χ r u : ℂ) * L.val (A x)
      rw [hA]
      have h := L.property (upperUnipotentAut F E σ u) (A x)
      rw [standardCharacter_upperUnipotentAut F E σ χ hχ u] at h
      exact h⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_injective_line (LinearMap.id (R := ℂ))
    (fun _ _ h => h) e L' L (fun h => hL (congrArg Subtype.val h))
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    apply hL
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := A.surjective x
    exact congrArg (fun L₀ : glFunctionals χ r ρ => L₀.val y) hc
  have hcoeff (g : G) : L.val (ρ g (A v)) = c * L.val (ρ ((α).symm g) v) := by
    have hA := LinearMap.congr_fun (A.comp_apply_eq ((α).symm g)) v
    change A (ρ ((α).symm g) v) = ρ (α ((α).symm g)) (A v) at hA
    rw [MulEquiv.apply_symm_apply] at hA
    rw [← hA]
    exact congrArg (fun L₀ : glFunctionals χ r ρ => L₀.val (ρ ((α).symm g) v)) hc
  have hzero (x : W) : modelMap ρ L x = 0 ↔ ∀ g : G, L.val (ρ g x) = 0 := by
    constructor
    · intro h g
      exact congrArg (fun w : (coefficientModel ρ L).toSubmodule => w.val.val g) h
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact h g
  rw [hzero, hzero]
  constructor
  · intro h g
    have hh := h (α g)
    rw [hcoeff, MulEquiv.symm_apply_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc0
  · intro h g
    rw [hcoeff, h, mul_zero]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem normalization_of_ambient
    {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (I : Representation ℂ G X) (A₀ : SigmaIntertwiner σ (r + 1) I)
    (hJac : ∀ x, (borelShape r).jacquetMk I (A₀ x) = (borelShape r).jacquetMk I x)
    (hSph : ∀ x ∈ fixedVectors I (sphericalSubgroup E r), A₀ x = x)
    (χ : UnitaryAdditiveCharacter K) (hχ : ∀ x : K, χ (σ x) = χ x)
    (htype : RankinSelberg.IsOfWhittakerType r (standardCharacter χ r) I)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (hχgen : IsGeneric χ r π) (hsub : IsSubquotientOf I π) :
    ∃ A : SigmaIntertwiner σ (r + 1) π,
      (∀ v, jacquetSigmaIntertwiner σ (borelShape r) A ((borelShape r).jacquetMk π v) =
        (borelShape r).jacquetMk π v) ∧
      ∀ v ∈ fixedVectors π (sphericalSubgroup E r), A v = v := by
  let : π.IsIrreducible := hχgen.1
  obtain ⟨ℓ, hℓ⟩ := hχgen.2.2
  obtain ⟨S₀, q₀, hq₀⟩ := hsub
  have hlim := upperUnipotent_isLimitOfCompactSubgroups E (T) (r + 1)
  have hloc := RankinSelberg.UnequalRankAssembly.character_locallyConstant_of_whittakerType E (T) r
    (standardCharacter χ r) I htype
  obtain ⟨L, _, hL, hmodel⟩ := subquotientCoefficientModelInclusion G U hlim
    (standardCharacter χ r) hloc I π htype.1.1 S₀ q₀ hq₀ ℓ
  have hL0 := hL hℓ
  let C := (glCoefficientModel χ r I L).toSubmodule
  let Y : Type uE := ↥C
  let addY : AddCommGroup Y := C.addCommGroup
  let moduleY : Module ℂ Y := C.module
  let M : Representation ℂ G Y := glModelRepresentation χ r I L
  let q : I.IntertwiningMap M := modelMap I L
  have hq : Function.Surjective q := modelMap_surjective I L
  have hker (x : _) : q (A₀ x) = 0 ↔ q x = 0 :=
    modelMap_kernel_sigma F E σ χ hχ A₀ L hL0 (Classical.choice htype.2.2) x
  have hdesc : ∃ D : SigmaIntertwiner σ (r + 1) M, ∀ x, D (q x) = q (A₀ x) := by
    exact @sigma_on_quotient F.Carrier _ E.Carrier _ _ σ (r + 1)
      X _ _ Y addY moduleY I M A₀ q hq hker
  obtain ⟨D, hD⟩ := hdesc
  let j : π.IntertwiningMap M :=
    coefficientMapCompToSubrepresentation (IntertwiningMap.id π) ℓ (coefficientModel I L) hmodel
  have hjne : j.range ≠ ⊥ :=
    coefficientMapCompToSubrepresentation_range_ne_bot (IntertwiningMap.id π) ℓ
      (coefficientModel I L) hmodel hℓ
  have hj : Function.Injective j := by
    refine (Representation.IsIrreducible.injective_or_eq_zero (W := Y) (ρ := π) (σ := M) j).resolve_right ?_
    intro h
    apply hjne
    apply Subrepresentation.toSubmodule_injective
    change LinearMap.range j.toLinearMap = ⊥
    exact LinearMap.range_eq_bot.mpr (congrArg (fun f : π.IntertwiningMap M => f.toLinearMap) h)
  obtain ⟨S, hS, _, hmin, _⟩ := modelGenericSocle p inferInstance E χ r X I htype L hL0
  have hjS := range_eq_least (W := Y) (ρ := π) (τ := M) j hjne S hS hmin
  have hstable (w : _) : D w ∈ j.range ↔ w ∈ j.range := by
    rw [hjS]
    exact least_stable (V := Y) (ρ := M) S hS hmin D w
  obtain ⟨A, hA⟩ := sigma_on_injection (W := Y) (ρ := π) (τ := M) D j hj hstable
  have hMsmooth : IsSmooth M := model_isSmooth I htype.1.1 L
  refine ⟨A, ?_, ?_⟩
  · intro v
    rw [jacquetSigmaIntertwiner_mk]
    apply (borelCoinvariantsEquiv E π).injective
    simp only [borelCoinvariantsEquiv_mk]
    let jU := Jacquet.restrictMap j U
    have hfin (s : Finset U) : ∃ C : OpenSubgroup U, IsCompact (C : Set U) ∧
        ∀ g ∈ s, g ∈ C := by
      obtain ⟨C, hC, hs⟩ := upperUnipotentCompactContainment p inferInstance E (T) (r + 1)
        (s : Set U) s.finite_toSet.isCompact
      exact ⟨C, hC, hs⟩
    have hjc := coinvariants_map_injective_of_smooth hfin jU hj
      (isSmooth_comp (U).subtype continuous_subtype_val hMsmooth)
    apply hjc
    change Coinvariants.mk (M.comp (U).subtype) (j (A v)) =
      Coinvariants.mk (M.comp (U).subtype) (j v)
    obtain ⟨x, hx⟩ := hq (j v)
    rw [hA, ← hx, hD]
    have hAx := congrArg (borelCoinvariantsEquiv E I)
      (hJac x)
    simp only [borelCoinvariantsEquiv_mk] at hAx
    exact congrArg (Coinvariants.map (I.comp (U).subtype) (M.comp (U).subtype)
      (Jacquet.restrictMap q U)) hAx
  · intro v hv
    apply hj
    have hfix : j v ∈ fixedVectors M (sphericalSubgroup E r) := by
      intro k
      have he : j (π (k : G) v) = M (k : G) (j v) :=
        LinearMap.congr_fun (j.isIntertwining' (k : G)) v
      exact he.symm.trans (congrArg j (hv k))
    obtain ⟨x, hx⟩ := Compact.fixedVectorSurjectivity G X Y I M htype.1.1 hMsmooth
      (sphericalOpenSubgroup E r) (sphericalOpenSubgroup_isCompact E r) q hq ⟨j v, hfix⟩
    have hxj : q x.val = j v := congrArg Subtype.val hx
    calc
      j (A v) = D (j v) := hA v
      _ = D (q x.val) := congrArg D hxj.symm
      _ = q (A₀ x.val) := hD x.val
      _ = q x.val := congrArg q (hSph x.val x.property)
      _ = j v := hxj

end PadicFields

set_option maxHeartbeats 1000000 in
/-- Henniart–Lemaire's normalized σ-action on the actual Borel Jacquet quotient
and the spherical vectors of a generic irreducible unramified constituent. -/
theorem unramifiedGenericSigmaNormalization :
    UnramifiedGenericSigmaNormalizationStatement.{uF, uE, uV} := by
  intro p hp F E _ _ σ l r hcyc _he z V _ _ π ψ hgen hsub
  let T := E.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  obtain ⟨χ, hχ⟩ := exists_sigmaInvariant_additiveCharacter F E σ
  have hχgen := (T.isGeneric_iff_character π ψ χ).mp hgen
  exact normalization_of_ambient F E σ (principalSeriesOfTuple E z)
    (principalIntertwiner F E σ z) (principalIntertwiner_jacquet F E σ z hcyc)
    (principalIntertwiner_spherical F E σ z) χ hχ
    (principalSeries_whittakerType E z χ) π hχgen hsub

end Langlands.BaseChange
