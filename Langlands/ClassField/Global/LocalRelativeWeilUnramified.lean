import Langlands.ClassField.Global.RelativeWeilLocalCosets
import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm

/-! # Local relative Weil maps at places of ramification index one

At a place `w` of `E` above a finite place `z` of `F` with ramification index one, the image
of `W_{E_w}` in `W_{F_z}` consists of the elements whose degree is divisible by the residue
degree of `E_w / F_z`. For a homomorphism `ι : W_{F_z} → W_{E/F}` compatible with the
embedding `E → E_w → \bar{F_z}`, the inverse image of `C_E` under `ι` is the image of
`W_{E_w}`.
-/

noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField WithZero

universe u v

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- If absolute inertia of `F` lies in the image of `G_E`, an element of `W_F` lies in the
image of `W_E` exactly when its degree is divisible by the residue degree of `E / F`. -/
theorem mem_extensionWeilMap_range_iff_dvd
    (hI : F.absoluteInertia F.canonicalTopologicalData ≤
      (extensionGaloisMap F E f).toMonoidHom.range)
    (g : localWeilGroup F) :
    g ∈ (extensionWeilMap F E f).toMonoidHom.range ↔
      (extensionResidueDegree F E f : ℤ) ∣ localDegreeInt F g := by
  constructor
  · rintro ⟨x, rfl⟩
    change (extensionResidueDegree F E f : ℤ) ∣ localDegreeInt F (extensionWeilMap F E f x)
    rw [localDegreeInt_extensionWeilMap]
    exact dvd_mul_right _ _
  · rintro ⟨m, hm⟩
    obtain ⟨x, hx⟩ := localDegree_surjective E (Multiplicative.ofAdd m)
    set g' := g * (extensionWeilMap F E f x)⁻¹ with hg'
    have hdeg : localDegree F g' = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hg', map_mul, map_inv, localDegree_extensionWeilMap, hx, toAdd_mul, toAdd_inv,
        toAdd_pow, toAdd_ofAdd, toAdd_one, nsmul_eq_mul]
      change localDegreeInt F g + -((extensionResidueDegree F E f : ℤ) * m) = 0
      rw [hm]
      ring
    have hin : localProjection F g' ∈ F.absoluteInertia F.canonicalTopologicalData := by
      rw [← localResidueDegree_ker, MonoidHom.mem_ker]
      have hw : localResidueDegree F (localProjection F g') = Weil.frobenius (localDegree F g') :=
        g'.property
      rw [hdeg, map_one] at hw
      exact hw
    rw [extensionWeilMap_range, Subgroup.mem_comap]
    have hsplit : localProjection F g =
        localProjection F g' * extensionGaloisMap F E f (localProjection E x) := by
      rw [hg', map_mul, map_inv, ← localProjection_extensionWeilMap, inv_mul_cancel_right]
    change localProjection F g ∈ _
    rw [hsplit]
    exact Subgroup.mul_mem _ (hI hin) ⟨localProjection E x, rfl⟩

end Langlands.Weil.Local

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

section Valuation

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The normalized valuation of the canonical topological data of `K_w` is the valuation of
the completion. -/
theorem discreteValuation_padicField :
    (padicField w).canonicalTopologicalData.discreteValuation =
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) :=
  discreteValuation_eq_of_vle (padicField w).canonicalTopologicalData
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) (topologicalData_vle w)
    (w.valuedAdicCompletion_surjective K)

/-- The same for the package transported to an equal residue prime. -/
theorem discreteValuation_padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (padicFieldAt w h).canonicalTopologicalData.discreteValuation =
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) := by
  subst h
  exact discreteValuation_padicField w

end Valuation

section Unramified

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal]

/-- At ramification index one, the canonical absolute ramification indices of `F_z` and `E_w`
agree. -/
theorem ramificationIndex_eq_of_ramificationIdx_eq_one
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    (padicField z).canonicalTopologicalData.ramificationIndex =
      (towerPadicField z w).canonicalTopologicalData.ramificationIndex := by
  unfold PadicField.TopologicalData.ramificationIndex PadicField.TopologicalData.ord
  rw [discreteValuation_padicField z, discreteValuation_padicFieldAt w]
  have hcast : ((residuePrime z : ℕ) : (towerPadicField z w).Carrier) =
      FiniteExtension.completionMap z w ((residuePrime z : ℕ) : (padicField z).Carrier) :=
    (map_natCast (FiniteExtension.completionMap z w) _).symm
  rw [hcast, FiniteExtension.valuation_completionMap, he, pow_one]

/-- At ramification index one, absolute inertia of `F_z` lies in the image of `G_{E_w}`. -/
theorem absoluteInertia_le_completionGaloisRange
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    (padicField z).absoluteInertia (padicField z).canonicalTopologicalData ≤
      (Weil.Local.extensionGaloisMap (padicField z) (towerPadicField z w)
        (completionPadicAlgHom z w)).toMonoidHom.range :=
  (PadicField.absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq _ _ _).mpr
    (ramificationIndex_eq_of_ramificationIdx_eq_one z w he)

/-- At ramification index one, an element of `W_{F_z}` lies in the image of `W_{E_w}` exactly
when its degree is divisible by the residue degree of `E_w / F_z`. -/
theorem mem_completionWeilMap_range_iff
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (g : Weil.Local.localWeilGroup (padicField z)) :
    g ∈ (completionWeilMap z w).toMonoidHom.range ↔
      (Weil.Local.extensionResidueDegree (padicField z) (towerPadicField z w)
          (completionPadicAlgHom z w) : ℤ) ∣ Weil.Local.localDegreeInt (padicField z) g :=
  Weil.Local.mem_extensionWeilMap_range_iff_dvd _ _ _
    (absoluteInertia_le_completionGaloisRange z w he) g

end Unramified

section Inverse

attribute [local instance] relativeGaloisTopology

variable (c : FundamentalClass.ClassFamily.{u}) {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal] (h : FundamentalClass.Restriction c)

/-- The image of `W_{E/E}` in `W_{E/F}` is the idele-class subgroup. -/
theorem mem_range_restrictionInclusion_self_iff (t : RelativeWeilGroup c F E) :
    t ∈ (restrictionInclusion c F E E h).toMonoidHom.range ↔ t ∈ ideleClassSubgroup c F E := by
  rw [range_restrictionInclusion, Subgroup.mem_comap, mem_range_restrictScalarsHom_iff,
    ideleClassSubgroup, RelativeWeilGroup.exact, MonoidHom.mem_ker, AlgEquiv.ext_iff]
  rfl

include h in
/-- For `ι : W_{F_z} → W_{E/F}` compatible with `E → E_w → \bar{F_z}`, the elements of
`W_{F_z}` sent into `C_E` are exactly those in the image of `W_{E_w}`. -/
theorem mem_ideleClassSubgroup_iff
    (ι : Weil.Local.localWeilGroup (padicField z) →* RelativeWeilGroup c F E)
    (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
      closurePlaceEmbedding z w (projection c F E (ι g) x) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w x))
    (ℓ : Weil.Local.localWeilGroup (padicField z)) :
    ι ℓ ∈ ideleClassSubgroup c F E ↔ ℓ ∈ (completionWeilMap z w).toMonoidHom.range := by
  have key := conj_mem_range_restrictionInclusion_iff c E z w h ι hι ⟨w, ‹_›⟩ 1 (fun k => by
    rw [cosetEmbedding_apply, map_one, inv_one, AlgEquiv.one_apply]
    rfl) ℓ
  rw [one_mul, inv_one, mul_one, mem_range_restrictionInclusion_self_iff] at key
  exact key

end Inverse

end Langlands.ClassField.Global.RelativeWeilGroup
