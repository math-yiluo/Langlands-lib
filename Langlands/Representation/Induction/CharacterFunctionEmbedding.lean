import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Classification.ConstituentRelations

/-! Scalar character functions inside actual smooth induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (P : Subgroup G) (σ : Representation R P V)
  (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
  (hσ : ∀ (p : P) (v : V), σ p v = (χ (p : G) : R) • v)

/-- A vector extends to the covariant character function `g ↦ χ(g) • v`. -/
def characterFunction (v : V) : SmoothFunctions P σ :=
  smoothFunctionOf P σ (fun g => (χ g : R) • v)
    (by
      intro p x
      rw [hσ, map_mul, Units.val_mul, mul_smul])
    ⟨χ.ker, hχ⟩ (by
      intro k x
      have hk : χ (k : G) = 1 := k.property
      simp [map_mul, hk])

omit [IsTopologicalGroup G] in
@[simp]
theorem eval_characterFunction (v : V) (g : G) :
    eval P σ (characterFunction P σ χ hχ hσ v) g = (χ g : R) • v := rfl

/-- Character functions intertwine the scalar action with right translation. -/
def characterFunctionEmbedding :
    (twist χ (Representation.trivial R G V)).IntertwiningMap (smoothInduced P σ) where
  toLinearMap :=
    { toFun := characterFunction P σ χ hχ hσ
      map_add' v w := by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        exact smul_add (χ g : R) v w
      map_smul' c v := by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        exact smul_comm (χ g : R) c v }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (χ x : R) • ((χ g : R) • v) = (χ (x * g) : R) • v
    rw [map_mul, Units.val_mul, mul_smul]

/-- Evaluation at one is a left inverse, so the map is injective. -/
theorem characterFunctionEmbedding_injective :
    Function.Injective (characterFunctionEmbedding P σ χ hχ hσ) := by
  intro v w hvw
  have h := congrArg (fun f => eval P σ f 1) hvw
  change (χ 1 : R) • v = (χ 1 : R) • w at h
  simpa only [map_one, Units.val_one, one_smul] using h

end Langlands.Induction
