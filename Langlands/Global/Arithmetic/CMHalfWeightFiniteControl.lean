import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Global.CompletionPadic
import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Finite neighborhoods separating CM conjugation ratios -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped NumberField
open Langlands.ClassField.Global Langlands.Global.AdelicFunctoriality

namespace Langlands.Global.CMHalfWeight

universe u

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

/-- The conjugation ratio of a nonzero global element. -/
def conjugationRatio (a : Kˣ) : Kˣ :=
  a / Units.mapEquiv (IsCMField.complexConj K).toMulEquiv a

/-- The conjugation ratio on actual ideles. -/
def ideleConjugationRatio : Ideles K →ₜ* Ideles K :=
  (ContinuousMonoidHom.id (Ideles K)) /
    { toMonoidHom := (ideleEquiv (IsCMField.complexConj K).toRingEquiv).toMonoidHom
      continuous_toFun := (ideleEquiv (IsCMField.complexConj K).toRingEquiv).continuous }

@[simp]
theorem ideleConjugationRatio_apply (x : Ideles K) :
    ideleConjugationRatio x =
      x / ideleEquiv (IsCMField.complexConj K).toRingEquiv x := rfl

@[simp]
theorem ideleConjugationRatio_diagonal (a : Kˣ) :
    ideleConjugationRatio (diagonalUnits K a) =
      diagonalUnits K (conjugationRatio a) := by
  simp only [ideleConjugationRatio_apply, ideleEquiv_diagonal, conjugationRatio, map_div]

/-- An integral principal conjugation ratio is a global root of unity. -/
theorem exists_torsion_of_integral_conjugationRatio (a : Kˣ)
    (ha : diagonalUnits K (conjugationRatio a) ∈ integralIdeles K) :
    ∃ ζ : NumberField.Units.torsion K,
      Units.map (algebraMap (𝓞 K) K).toMonoidHom ζ.val = conjugationRatio a := by
  obtain ⟨ε, hε⟩ := (principalIdeleUnitCriterion K (conjugationRatio a)).mp ha
  refine ⟨⟨ε, (NumberField.Units.mem_torsion K).mpr ?_⟩, hε⟩
  intro w
  have he : (ε : K) = (conjugationRatio a : K) := congrArg Units.val hε
  rw [he]
  simp only [conjugationRatio, Units.val_div_eq_div_val, Units.coe_mapEquiv]
  change w ((a : K) / IsCMField.complexConj K (a : K)) = 1
  rw [map_div₀, IsCMField.infinitePlace_complexConj, div_self]
  exact (map_ne_zero w).mpr a.ne_zero

omit [IsCMField K] in
/-- An open local subgroup can exclude every nontrivial global root of unity. -/
theorem exists_openSubgroup_separating_torsion (w : FinitePlace K) :
    ∃ V : OpenSubgroup (FiniteCompletion K w)ˣ,
      ∀ ζ : NumberField.Units.torsion K,
        Units.map (algebraMap (𝓞 K) (FiniteCompletion K w)).toMonoidHom ζ.val ∈ V →
          ζ = 1 := by
  classical
  let : ValuativeRel (FiniteCompletion K w) :=
    (CompletionPadic.topologicalData w).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion K w) :=
    (CompletionPadic.topologicalData w).localField
  let : TotallyDisconnectedSpace (FiniteCompletion K w) := inferInstance
  let : TotallyDisconnectedSpace (FiniteCompletion K w)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let f : NumberField.Units.torsion K →* (FiniteCompletion K w)ˣ :=
    (Units.map (algebraMap (𝓞 K) (FiniteCompletion K w)).toMonoidHom).comp
      (NumberField.Units.torsion K).subtype
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply RingOfIntegers.coe_injective
    apply (algebraMap K (FiniteCompletion K w)).injective
    have h := congrArg Units.val hab
    change algebraMap (𝓞 K) (FiniteCompletion K w) (a.val : 𝓞 K) =
      algebraMap (𝓞 K) (FiniteCompletion K w) (b.val : 𝓞 K) at h
    simpa only [← IsScalarTower.algebraMap_apply (𝓞 K) K (FiniteCompletion K w)] using h
  let T : Set (FiniteCompletion K w)ˣ := f '' {ζ | ζ ≠ 1}
  have hT : T.Finite := Set.toFinite _
  have h1 : (1 : (FiniteCompletion K w)ˣ) ∈ Tᶜ := by
    rintro ⟨ζ, hζ, he⟩
    exact hζ (hf (he.trans f.map_one.symm))
  obtain ⟨V, _, hV⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 Tᶜ
      (hT.isClosed.isOpen_compl.mem_nhds h1)
  refine ⟨V, fun ζ hζ => ?_⟩
  by_contra hne
  exact hV hζ ⟨ζ, hne, rfl⟩

/-- Membership of the conjugation ratio in the integral ideles is preserved by
the actual CM involution. -/
theorem integral_ideleConjugationRatio {x : Ideles K} (hx : x ∈ integralIdeles K) :
    ideleConjugationRatio x ∈ integralIdeles K :=
  by
    change x / ideleEquiv (IsCMField.complexConj K).toRingEquiv x ∈ integralIdeles K
    apply (integralIdeles K).div_mem hx
    intro w
    exact (finiteCompletionEquiv_valuation (IsCMField.complexConj K).toRingEquiv w _).trans
      (hx _)

/-- At a finite place outside the support and its conjugate, the conjugation
ratio of a supported idele is one. -/
theorem finiteCoordinate_conjugationRatio_eq_one (S : Finset (FinitePlace K))
    (s : Ideles K) (hs : ∀ w ∉ S, ideleCoordinate w s = 1)
    (w : FinitePlace K) (hw : w ∉ S)
    (hcw : finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv w ∉ S) :
    (finiteIdeleProjection K w) (ideleConjugationRatio s) = 1 := by
  rw [ideleConjugationRatio_apply, map_div]
  change ideleCoordinate w s /
    ideleCoordinate w (ideleEquiv (IsCMField.complexConj K).toRingEquiv s) = 1
  rw [hs w hw]
  have hc :
      ideleCoordinate w (ideleEquiv (IsCMField.complexConj K).toRingEquiv s) = 1 := by
    apply Units.ext
    change finiteCompletionEquiv (IsCMField.complexConj K).toRingEquiv w
      (ideleCoordinate (finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv w) s) = 1
    rw [hs _ hcw, Units.val_one, map_one]
  simp only [hc, div_self']

/-- There is an open integral-idele subgroup containing every infinity idele
such that a principal factor, modulo a conjugation-fixed idele and an integral
idele supported on `S`, is real whenever the product lies in the subgroup. -/
theorem exists_open_integral_subgroup_forcing_real (S : Finset (FinitePlace K)) :
    ∃ H : OpenSubgroup (Ideles K),
      H.toSubgroup ≤ integralIdeles K ∧
      (∀ x : (InfiniteAdeles K)ˣ, infiniteIdelesInclusion K x ∈ H) ∧
      ∀ (a : Kˣ) (b s : Ideles K),
        ideleEquiv (IsCMField.complexConj K).toRingEquiv b = b →
        s ∈ integralIdeles K →
        (∀ w ∉ S, ideleCoordinate w s = 1) →
        diagonalUnits K a * b * s ∈ H →
        IsCMField.complexConj K (a : K) = a := by
  classical
  let c := finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv
  let : Infinite (FinitePlace K) := numberField_finitePlaces_infinite K
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (S ∪ S.preimage c c.injective.injOn)
  have hwS : w ∉ S := fun h => hw (Finset.mem_union_left _ h)
  have hcwS : c w ∉ S := fun h => hw (Finset.mem_union_right _ (Finset.mem_preimage.mpr h))
  obtain ⟨V, hV⟩ := exists_openSubgroup_separating_torsion (K := K) w
  let f := ((finiteIdeleProjection K w)).comp (ideleConjugationRatio (K := K))
  let H : OpenSubgroup (Ideles K) :=
    ⟨integralIdeles K, CMUnramifiedInfinity.isOpen_integralIdeles⟩ ⊓
      V.comap f.toMonoidHom f.continuous
  refine ⟨H, fun _ hx => hx.1, ?_, ?_⟩
  · intro x
    constructor
    · intro v
      change Valued.v (1 : FiniteCompletion K v) = 1
      exact map_one _
    · change (finiteIdeleProjection K w) (ideleConjugationRatio (infiniteIdelesInclusion K x)) ∈ V
      have h : (finiteIdeleProjection K w)
          (ideleConjugationRatio (infiniteIdelesInclusion K x)) = 1 := by
        rw [ideleConjugationRatio_apply, map_div]
        apply Units.ext
        rw [Units.val_div_eq_div_val]
        change (1 : FiniteCompletion K w) /
          finiteCompletionEquiv (IsCMField.complexConj K).toRingEquiv w 1 = 1
        simp
      rw [h]
      exact V.one_mem
  · intro a b s hb hs hsS hx
    have hb1 : ideleConjugationRatio b = 1 := by
      rw [ideleConjugationRatio_apply, hb, div_self']
    have he :
        ideleConjugationRatio (diagonalUnits K a * b * s) =
          diagonalUnits K (conjugationRatio a) * ideleConjugationRatio s := by
      rw [map_mul, map_mul, ideleConjugationRatio_diagonal, hb1, mul_one]
    have ha : diagonalUnits K (conjugationRatio a) ∈ integralIdeles K := by
      have hprod := integral_ideleConjugationRatio hx.1
      rw [he] at hprod
      exact (integralIdeles K).mul_mem_cancel_right
        (integral_ideleConjugationRatio hs) |>.mp hprod
    obtain ⟨ζ, hζ⟩ := exists_torsion_of_integral_conjugationRatio a ha
    have hs1 : (finiteIdeleProjection K w) (ideleConjugationRatio s) = 1 :=
      finiteCoordinate_conjugationRatio_eq_one S s hsS w hwS hcwS
    have hlocal :
        Units.map (algebraMap (𝓞 K) (FiniteCompletion K w)).toMonoidHom ζ.val ∈ V := by
      have hh := hx.2
      change (finiteIdeleProjection K w)
        (ideleConjugationRatio (diagonalUnits K a * b * s)) ∈ V at hh
      rw [he, map_mul, hs1, mul_one, ← hζ] at hh
      exact hh
    have hz := hV ζ hlocal
    have har : conjugationRatio a = 1 := by
      rw [← hζ, hz]
      exact map_one _
    have hfix : a = Units.mapEquiv (IsCMField.complexConj K).toMulEquiv a :=
      div_eq_one.mp har
    exact (congrArg Units.val hfix).symm

end Langlands.Global.CMHalfWeight
