import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.RepresentationTheory.Irreducible

/-!
# Matrix coefficients in actual smooth induction from the center

The central character is retained in the complex-valued functions on the group.
Only their absolute values descend to the central quotient.
-/

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace Induction

/-- The actual smooth scalar functions transforming under a central character. -/
abbrev CentralFunctions (χ : Subgroup.center G →* ℂˣ) :=
  SmoothFunctions (Subgroup.center G) (characterRepresentation χ)

/-- Smooth induction from the center, with its positive character and right translation. -/
abbrev centralInduced (χ : Subgroup.center G →* ℂˣ) :
    Representation ℂ G (CentralFunctions χ) :=
  smoothInduced (Subgroup.center G) (characterRepresentation χ)

/-- The norm of an actual centrally covariant function on the central quotient. -/
def centralNorm (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (f : CentralFunctions χ) :
    G ⧸ Subgroup.center G → ℝ :=
  Quotient.lift (fun g => ‖eval _ _ f g‖) (by
    intro a b hab
    have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hab
    let z : Subgroup.center G := ⟨a⁻¹ * b, hz⟩
    have hzb : (z : G) * a = b := by
      rw [z.property.comm a]
      simp [z]
    have hc := eval_covariant (Subgroup.center G) (characterRepresentation χ) f z a
    change eval _ _ f ((z : G) * a) = (χ z : ℂ) * eval _ _ f a at hc
    rw [hzb] at hc
    rw [hc, norm_mul, hχ, one_mul])

omit [IsTopologicalGroup G] in
@[simp]
theorem centralNorm_mk (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (f : CentralFunctions χ) (g : G) :
    centralNorm χ hχ f (QuotientGroup.mk g) = ‖eval _ _ f g‖ := rfl

/-- Descending the norm preserves local constancy. -/
theorem centralNorm_isLocallyConstant (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (f : CentralFunctions χ) :
    IsLocallyConstant (centralNorm χ hχ f) := by
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.leftRel (Subgroup.center G))).isCoinducing.isOpen_preimage.mp
  exact (eval_isLocallyConstant _ _ f).comp (fun z : ℂ => ‖z‖) s

/-- The descended norm translates on the actual quotient by right multiplication. -/
theorem centralNorm_translate (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (f : CentralFunctions χ) (g : G)
    (q : G ⧸ Subgroup.center G) :
    centralNorm χ hχ (centralInduced χ g f) q =
      centralNorm χ hχ f (q * QuotientGroup.mk g) := by
  induction q using Quotient.inductionOn
  rfl

end Induction

namespace UnitaryCentralCharacter

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ)

/-- Matrix coefficients of a smooth representation form actual smooth central
induced functions, equivariantly in the vector variable. -/
def coefficientIntertwiner (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V) :
    ρ.IntertwiningMap (Induction.centralInduced c.character) where
  toLinearMap :=
    { toFun := fun v =>
        ⟨⟨matrixCoefficient ρ ℓ v, by
          intro z g
          change ℓ (ρ ((z : G) * g) v) = (c.character z : ℂ) * ℓ (ρ g v)
          rw [map_mul, Module.End.mul_apply, c.acts, map_smul]
          rfl⟩, by
          obtain ⟨K, hK⟩ := hρ v
          refine ⟨K, ?_⟩
          intro k
          apply Subtype.ext
          funext g
          change ℓ (ρ (g * (k : G)) v) = ℓ (ρ g v)
          have hk : ρ (k : G) v = v := hK k
          rw [map_mul, Module.End.mul_apply, hk]⟩
      map_add' v w := by
        ext g
        exact congrFun ((matrixCoefficient ρ ℓ).map_add v w) g
      map_smul' a v := by
        ext g
        exact congrFun ((matrixCoefficient ρ ℓ).map_smul a v) g }
  isIntertwining' g := by
    ext v x
    change ℓ (ρ x (ρ g v)) = ℓ (ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

@[simp]
theorem coefficientIntertwiner_eval (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V)
    (v : V) (g : G) :
    Induction.eval _ _ (c.coefficientIntertwiner hρ ℓ v) g =
      matrixCoefficient ρ ℓ v g := rfl

/-- Evaluation at the identity recovers the original linear functional. -/
@[simp]
theorem coefficientIntertwiner_eval_one (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V)
    (v : V) :
    Induction.eval _ _ (c.coefficientIntertwiner hρ ℓ v) 1 = ℓ v := by
  change ℓ (ρ 1 v) = ℓ v
  rw [map_one, Module.End.one_apply]

/-- A nonzero functional produces a nonzero actual intertwiner. -/
theorem coefficientIntertwiner_ne_zero (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) :
    c.coefficientIntertwiner hρ ℓ ≠ 0 := by
  intro h
  apply hℓ
  ext v
  have hv := congrArg
    (fun f : ρ.IntertwiningMap (Induction.centralInduced c.character) =>
      Induction.eval _ _ (f v) 1) h
  rw [coefficientIntertwiner_eval_one] at hv
  change ℓ v = 0 at hv
  exact hv

/-- For an irreducible source, every nonzero coefficient functional gives an
injective map into actual smooth central induction. -/
theorem coefficientIntertwiner_injective [Representation.IsIrreducible ρ]
    (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) :
    Function.Injective (c.coefficientIntertwiner hρ ℓ) :=
  (Representation.IsIrreducible.injective_or_eq_zero
    (c.coefficientIntertwiner hρ ℓ)).resolve_right
      (c.coefficientIntertwiner_ne_zero hρ ℓ hℓ)

/-- The actual induced function has exactly the Library's descended coefficient
norm. The complex-valued coefficient itself is not made a quotient function. -/
theorem coefficientIntertwiner_norm (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V)
    (v : V) :
    Induction.centralNorm c.character c.norm_eq_one (c.coefficientIntertwiner hρ ℓ v) =
      c.coefficientNorm ℓ v := by
  funext q
  induction q using Quotient.inductionOn
  rfl

/-- In particular, the two actual quotient functions have identical `MemLp`
criteria for every measure and exponent. -/
theorem coefficientIntertwiner_memLp_iff
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    (hρ : IsSmooth ρ) (ℓ : Module.Dual ℂ V) (v : V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)) (r : ENNReal) :
    MeasureTheory.MemLp
      (Induction.centralNorm c.character c.norm_eq_one (c.coefficientIntertwiner hρ ℓ v))
      r μ ↔ MeasureTheory.MemLp (c.coefficientNorm ℓ v) r μ := by
  rw [coefficientIntertwiner_norm]

end UnitaryCentralCharacter
end Langlands
