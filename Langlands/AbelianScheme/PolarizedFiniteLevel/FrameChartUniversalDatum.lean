import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartRepresentabilityStatement

/-! # Frame charts from a universal frame datum -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{0}} {g d n : ℕ}

/-- A datum `U` over a level base `X` is a universal frame datum for `ρ` when every datum
over a level base `T` with frame locus `⊤` is isomorphic to the pullback of `U` along some
morphism `T ⟶ X`, pullbacks along different morphisms are never isomorphic, and data
isomorphic to pullbacks of `U` have frame locus `⊤`. -/
structure IsUniversalFrameDatum {m : ℕ} (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (X : LevelBase n) (U : Datum P X.obj g d n) : Prop where
  injective : ∀ (T : LevelBase n) (f f' : T ⟶ X),
    Nonempty (PolarizedIso (U.pullback f.hom) (U.pullback f'.hom)) → f = f'
  exists_pullback : ∀ (T : LevelBase n) (b : Datum P T.obj g d n), b.frameLocus ρ = ⊤ →
    ∃ f : T ⟶ X, Nonempty (PolarizedIso b (U.pullback f.hom))
  frameLocus_eq_top : ∀ (T : LevelBase n) (f : T ⟶ X) (b : Datum P T.obj g d n),
    Nonempty (PolarizedIso b (U.pullback f.hom)) → b.frameLocus ρ = ⊤

/-- A universal frame datum represents the frame chart: the natural transformation
classifying it is injective, and its image consists of the classes of data with frame
locus `⊤`. -/
theorem frameChart_of_isUniversalFrameDatum (hd : 0 < d) (hn : 3 ≤ n) {m : ℕ}
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (X : LevelBase n) (U : Datum P X.obj g d n)
    (hU : IsUniversalFrameDatum ρ X U) :
    ∃ a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn,
      (∀ T : (LevelBase n)ᵒᵖ, Function.Injective (a.app T)) ∧
        ∀ (T : LevelBase n) (b : Datum P T.obj g d n),
          b.classOf ∈ Set.range (a.app (op T)) ↔ b.frameLocus ρ = ⊤ := by
  let a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn :=
    uliftYonedaEquiv.symm (U.classOf : Moduli P X.obj g d n)
  have ha : ∀ (T : LevelBase n) (f : T ⟶ X),
      a.app (op T) (ULift.up f) = (U.pullback f.hom).classOf := fun T f => rfl
  refine ⟨a, ?_, ?_⟩
  · intro T
    rintro ⟨f⟩ ⟨f'⟩ h
    rw [ha T.unop f, ha T.unop f'] at h
    exact congrArg ULift.up (hU.injective T.unop f f' (Quotient.exact h))
  · intro T b
    constructor
    · rintro ⟨⟨f⟩, hf⟩
      rw [ha T f] at hf
      obtain ⟨e⟩ : Nonempty (PolarizedIso (U.pullback f.hom) b) := Quotient.exact hf
      exact hU.frameLocus_eq_top T f b ⟨e.symm⟩
    · intro hb
      obtain ⟨f, ⟨e⟩⟩ := hU.exists_pullback T b hb
      exact ⟨ULift.up f, by rw [ha T f]; exact (Datum.classOf_eq e).symm⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
