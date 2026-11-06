import Langlands.Representation.Filtration.InvariantBilinearSmoothDual
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.SmoothProof

/-! # Covariant bilinear pairings and smooth contragredient equivalences -/

noncomputable section

namespace Langlands.RankinSelberg

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ G V) (σ : Representation ℂ G W)
  (χ : G →* ℂˣ)

/-- A nonzero bilinear form with simultaneous covariance given by `χ`. -/
def HasNonzeroCovariantPairing : Prop :=
  ∃ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, β ≠ 0 ∧
    ∀ g v w, β (π g v) (σ g w) = (χ g : ℂ) * β v w

/-- A nonzero covariant bilinear form between irreducible representations
identifies the inverse twist of the smooth input with the smooth dual of
the admissible input. The equivalence retains the given evaluation form. -/
theorem exists_contragredient_equiv_of_covariant_pairing
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπs : IsSmooth π) (hσa : IsAdmissible σ)
    (hχ : IsOpen (χ.ker : Set G))
    (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : β ≠ 0)
    (hinv : ∀ g v w, β (π g v) (σ g w) = (χ g : ℂ) * β v w) :
    ∃ e : (Langlands.twist χ⁻¹ π).Equiv (smoothContragredient σ),
      ∀ v w, smoothDualPairing σ (e v) w = β v w := by
  have hχinv : IsOpen ((χ⁻¹).ker : Set G) := by
    have hker : (χ⁻¹).ker = χ.ker := by
      ext g
      simp
    rwa [hker]
  have htwists : IsSmooth (Langlands.twist χ⁻¹ π) :=
    (isSmooth_twist_iff χ⁻¹ π hχinv).mpr hπs
  let B : InvariantBilinear.forms σ (Langlands.twist χ⁻¹ π) (fun _ => 1) :=
    ⟨β.flip, by
      intro g w v
      change β ((χ⁻¹ g : ℂ) • π g v) (σ g w) = 1 * β v w
      rw [map_smul, LinearMap.smul_apply, hinv]
      simp [smul_eq_mul]⟩
  have hB : B ≠ 0 := by
    intro h
    apply hβ
    ext v w
    exact congrArg
      (fun b : InvariantBilinear.forms σ (Langlands.twist χ⁻¹ π) (fun _ => 1) =>
        b.val w v) h
  let q := InvariantBilinear.smoothDualQuotientOfNonzeroForm
    hcofinal hσa hσ htwists B hB
  have hq : q.val ≠ 0 :=
    InvariantBilinear.rightSmoothDualMap_ne_zero htwists B hB
  let : (Langlands.twist χ⁻¹ π).IsIrreducible :=
    (isIrreducible_twist_iff χ⁻¹ π).mpr hπ
  have hinjective : Function.Injective q.val :=
    (Representation.IsIrreducible.injective_or_eq_zero q.val).resolve_right hq
  exact ⟨q.val.ofBijective ⟨hinjective, q.property⟩, fun _ _ => rfl⟩

/-- A nonzero covariant pairing supplies the required contragredient
equivalence, without adding an analytic assertion. -/
theorem HasNonzeroCovariantPairing.contragredient_equiv
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπs : IsSmooth π) (hσa : IsAdmissible σ)
    (hχ : IsOpen (χ.ker : Set G))
    (h : HasNonzeroCovariantPairing π σ χ) :
    Nonempty ((Langlands.twist χ⁻¹ π).Equiv (smoothContragredient σ)) := by
  obtain ⟨β, hβ, hinv⟩ := h
  obtain ⟨e, _⟩ := exists_contragredient_equiv_of_covariant_pairing
    π σ χ hcofinal hπ hσ hπs hσa hχ β hβ hinv
  exact ⟨e⟩

end Langlands.RankinSelberg
