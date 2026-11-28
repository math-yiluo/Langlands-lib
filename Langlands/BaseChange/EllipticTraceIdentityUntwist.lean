import Langlands.BaseChange.EllipticTraceIdentityTransport
import Langlands.BaseChange.CyclicAlgebraDeterminant
import Langlands.BaseChange.SigmaLiftNormTwist
import Langlands.BaseChange.TwistedCharacter.TwistRegularity

/-! # Removing compatible determinant twists from an elliptic trace identity -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory

private theorem characterMultiplyTest_inv_cancel {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (f : SchwartzBruhat G) :
    characterMultiplyTest χ hχ (characterMultiplyTest χ⁻¹ (isOpen_ker_inv hχ) f) = f := by
  ext g
  simp only [characterMultiplyTest_apply, MonoidHom.inv_apply, ← mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

section Local

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type uE} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  {σ : E ≃ₐ[F] E} {n l : ℕ}
  [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (GeneralLinear n F) V} {τ : Representation ℂ (GeneralLinear n E) W}
  {hπ : IsAdmissible π}

/-- An elliptic trace identity passes through equivalences of the two representations. -/
theorem HasEllipticTraceIdentity.of_equiv
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {π' : Representation ℂ (GeneralLinear n F) V'}
    {τ' : Representation ℂ (GeneralLinear n E) W'}
    {hπ' : IsAdmissible π'} (h : HasEllipticTraceIdentity σ l π hπ τ)
    (eF : π.Equiv π') (eE : τ.Equiv τ') : HasEllipticTraceIdentity σ l π' hπ' τ' := by
  obtain ⟨hτ, A, c, hc, hid⟩ := h
  have hτ' := (isAdmissible_iff_of_equiv eE).mp hτ
  refine ⟨hτ', A.transport eE, c, hc, ?_⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF _ μE _ φ f hφ hf hn hcon
  rw [SigmaIntertwiner.transport_toLinearMap, twistedDistribution_eq_of_equivalent μE hτ hτ' eE,
    ← Character.distribution_eq_of_equivariant μF π hπ π' hπ' eF.toLinearEquiv
      (Representation.IntertwiningMap.isIntertwining _ _ eF.toIntertwiningMap)]
  exact hid μF μE φ f hφ hf hn hcon

/-- Characters invariant upstairs and equal on associated pairs can be removed from
an elliptic trace identity by multiplying the tests by the inverse characters. -/
theorem HasEllipticTraceIdentity.of_twist
    (χF : GeneralLinear n F →* ℂˣ) (χE : GeneralLinear n E →* ℂˣ)
    (hχF : IsOpen (χF.ker : Set (GeneralLinear n F)))
    (hχE : IsOpen (χE.ker : Set (GeneralLinear n E)))
    (hE : ∀ g, χE (entrywiseAut σ n g) = χE g)
    (hN : ∀ δ γ, IsNormAssociated σ l δ γ → χE δ = χF γ)
    (hπχ : IsAdmissible (twist χF π))
    (h : HasEllipticTraceIdentity σ l (twist χF π) hπχ (twist χE τ)) :
    HasEllipticTraceIdentity σ l π hπ τ := by
  obtain ⟨hτχ, Aχ, c, hc, hid⟩ := h
  have hτ := (isAdmissible_twist_iff χE τ hχE).mp hτχ
  let A : SigmaIntertwiner σ n τ := Representation.Equiv.mk Aχ.toLinearEquiv fun g => by
    apply LinearMap.ext
    intro x
    have ha := LinearMap.congr_fun (Aχ.comp_apply_eq g) x
    change Aχ.toLinearEquiv ((χE g : ℂ) • τ g x) =
      (χE (entrywiseAut σ n g) : ℂ) • τ (entrywiseAut σ n g) (Aχ.toLinearEquiv x) at ha
    rw [map_smul, hE] at ha
    have hcancel := congrArg (fun y : W => (↑((χE g)⁻¹) : ℂ) • y) ha
    change Aχ.toLinearEquiv (τ g x) = τ (entrywiseAut σ n g) (Aχ.toLinearEquiv x)
    simpa only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] using hcancel
  refine ⟨hτ, A, c, hc, ?_⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF _ μE _ φ f hφ hf hn hcon
  let φ' := characterMultiplyTest χE⁻¹ (isOpen_ker_inv hχE) φ
  let f' := characterMultiplyTest χF⁻¹ (isOpen_ker_inv hχF) f
  have hcon' : AreConcordant σ l μF μE φ' f' :=
    hcon.mul_characters χF⁻¹ χE⁻¹
      (fun g => congrArg Inv.inv (hE g)) (fun δ γ ha => congrArg Inv.inv (hN δ γ ha))
  have hid' := hid μF μE φ' f'
    (fun g hg => hφ g (right_ne_zero_of_mul hg))
    (fun g hg => hf g (right_ne_zero_of_mul hg))
    (fun g hg => hn g (right_ne_zero_of_mul hg)) hcon'
  rw [twistedDistribution_twist_eq_comp μE τ hτ Aχ.toLinearMap χE hχE hτχ,
    ← twistedDistribution_one μF (twist χF π) hπχ,
    twistedDistribution_twist_eq_comp μF π hπ 1 χF hχF hπχ,
    LinearMap.comp_apply, LinearMap.comp_apply,
    characterMultiplyTest_inv_cancel, characterMultiplyTest_inv_cancel,
    twistedDistribution_one] at hid'
  exact hid'

/-- An elliptic trace identity for twists by a determinant character and its norm
pullback gives the same identity for the original representations. -/
theorem HasEllipticTraceIdentity.of_determinantNormTwist
    (hcyc : IsCyclicAlgebra σ l) (ω : Fˣ →* ℂˣ)
    (hF : IsOpen ((ω.comp (determinant (n := n))).ker : Set (GeneralLinear n F)))
    (hE : IsOpen (((ω.comp (Units.map (Algebra.norm F : E →* F))).comp
      (determinant (n := n))).ker : Set (GeneralLinear n E)))
    (hπχ : IsAdmissible (twist (ω.comp determinant) π))
    (h : HasEllipticTraceIdentity σ l (twist (ω.comp determinant) π) hπχ
      (twist ((ω.comp (Units.map (Algebra.norm F : E →* F))).comp determinant) τ)) :
    HasEllipticTraceIdentity σ l π hπ τ := by
  refine h.of_twist _ _ hF hE (fun g => congrArg ω ?_)
    (fun _ _ ha => congrArg ω (ha.norm_determinant_units_eq hcyc)) hπχ
  change Units.map (Algebra.norm F : E →* F)
    (determinant (Matrix.GeneralLinearGroup.map σ.toRingHom g)) = _
  rw [Matrix.GeneralLinearGroup.map_det]
  exact Units.ext (Algebra.norm_eq_of_algEquiv σ (determinant g : E))

end Local

/-- Removing determinant norm twists preserves the elliptic trace identity. -/
def EllipticTraceIdentityDeterminantUntwistStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (E : Type uE) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    (n l : ℕ) (σ : E ≃ₐ[F] E),
    IsCyclicAlgebra σ l →
    ∀ [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
      [TotallyDisconnectedSpace (GeneralLinear n F)]
      [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
      [TotallyDisconnectedSpace (GeneralLinear n E)]
      (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (τ : Representation ℂ (GeneralLinear n E) W)
      (ω : Fˣ →* ℂˣ),
      let χF := ω.comp (determinant (n := n))
      let χE := (ω.comp (Units.map (Algebra.norm F : E →* F))).comp (determinant (n := n))
      IsOpen (χF.ker : Set (GeneralLinear n F)) →
      IsOpen (χE.ker : Set (GeneralLinear n E)) →
      ∀ (hπ : IsAdmissible π) (hπχ : IsAdmissible (twist χF π)),
        HasEllipticTraceIdentity σ l (twist χF π) hπχ (twist χE τ) →
        HasEllipticTraceIdentity σ l π hπ τ

theorem ellipticTraceIdentityDeterminantUntwist :
    EllipticTraceIdentityDeterminantUntwistStatement.{uF, uE, uV, uW} := by
  intro F _ _ _ E _ _ _ _ n l σ hcyc _ _ _ _ _ _ V _ _ W _ _ π τ ω χF χE hF hE hπ hπχ h
  exact h.of_determinantNormTwist hcyc ω hF hE hπχ

end Langlands.BaseChange
