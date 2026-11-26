import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.Group.GL.BlockDeterminant
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences

/-! # Proper induction and the unramified orbit of a σ-discrete series -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear Induction

universe u v z

variable {F : Type u} [CommRing F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E]
  {n : ℕ} (σ : E ≃ₐ[F] E)
  {V : Type z} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GeneralLinear n E) V)

/-- Invariant unramified twists of a σ-discrete series are outside the classes of
actual proper smooth inductions from smooth σ-stable Levi representations. -/
def SigmaDiscreteOrbitNoninductionStatement : Prop :=
  IsSigmaDiscreteSeries σ n τ →
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GeneralLinear n E) W),
      IsUnramifiedTwistOf (entrywiseAut σ n) τ π →
      ∀ B : BlockShape n, 2 ≤ B.length →
        ∀ (X : Type z) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
          IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
          IsEmpty (π.Equiv (smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))

/-- An equivalence to a proper induction would remain such an equivalence after
undoing the global twist, contradicting σ-discreteness. -/
theorem sigmaDiscreteOrbitNoninduction : SigmaDiscreteOrbitNoninductionStatement σ τ := by
  intro hτ W _ _ π hπ B hB X _ _ Ξ hΞ hΞσ
  obtain ⟨ψ, hψ, hψσ, ⟨e⟩⟩ := hπ
  let χ := ψ⁻¹
  have hχ : IsUnramifiedCharacter χ := hψ.inv
  have hχσ (g : GeneralLinear n E) : χ (entrywiseAut σ n g) = χ g :=
    congrArg Inv.inv (hψσ g)
  let : T2Space (GeneralLinear n E) := LocalFieldTopology.generalLinear_t2Space E n
  let : LocallyCompactSpace (GeneralLinear n E) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let : TotallyDisconnectedSpace (GeneralLinear n E) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  let P := B.parabolic E
  let p := B.leviProjection E
  let η := χ.comp (B.leviEmbedding E)
  have hη : IsOpen (η.ker : Set (B.Levi E)) :=
    hχ.isOpen_ker.preimage (B.leviEmbeddingContinuous E).continuous
  have hησ (m : B.Levi E) : η (leviAut σ B m) = η m := by
    change χ (B.leviEmbedding E (leviAut σ B m)) = χ (B.leviEmbedding E m)
    rw [← entrywiseAut_leviEmbedding, hχσ]
  have hηp (x : P) : χ x = η (p x) := by
    have hn : 0 < n := (show 0 < B.length by omega).trans_le B.length_le
    change χ (x : GeneralLinear n E) = χ (B.leviEmbedding E (p x))
    have hdet : determinant (x : GeneralLinear n E) = determinant (B.leviEmbedding E (p x)) := by
      let y : B.parabolic E := B.leviInParabolic E (p x)
      change determinant x.val = determinant y.val
      rw [determinant_blockParabolic B x, determinant_blockParabolic B y]
      simp only [y, B.leviProjection_section, p]
    rw [eq_detOrderCharacter_of_isUnramified E ⟨0, hn⟩ χ hχ]
    simp only [determinantOrderHom, MonoidHom.comp_apply, hdet]
  let eLevi : (twist (χ.comp P.subtype) (Ξ.comp p)).Equiv ((twist η Ξ).comp p) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ X) (fun q => by
      ext x
      change (χ (q : GeneralLinear n E) : ℂ) • Ξ (p q) x = (η (p q) : ℂ) • Ξ (p q) x
      rw [hηp q])
  let eInd := (smoothInductionTwistEquiv P ⟨χ, hχ.isOpen_ker⟩ (Ξ.comp p)).trans
    (smoothInducedEquiv P eLevi)
  obtain ⟨A⟩ := hΞσ
  have hΞ' := (isSmooth_twist_iff η Ξ hη).mpr hΞ
  have hStable' : IsLeviSigmaStable σ B (twist η Ξ) :=
    ⟨twistTwistedIntertwiner (leviAut σ B) η hησ A⟩
  refine ⟨fun h => (hτ.2.2.2.2 B hB X (twist η Ξ) hΞ' hStable').false ?_⟩
  have eTw := twistEquiv χ (e.symm.trans h)
  have eUntwist : τ.Equiv (twist χ (smoothInduced P (Ξ.comp p))) := by
    dsimp only [χ] at eTw
    rwa [twist_inv_twist] at eTw
  exact eUntwist.trans eInd

end Langlands.BaseChange
