import Langlands.Representation.Parabolic.FiniteLengthGrothendieckStatement
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.Parabolic.InductionExactnessProof
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof

/-!
# Canonical Grothendieck maps for the actual normalized parabolic functors

Both actual normalized parabolic functors preserve actual short exact sequences,
by the published exactness theorems, and preserve finite length, by the published
finite-length theorem at the saturated carrier universe. The published generic
construction then gives the integer-linear maps with the required generator
formula. Uniqueness among maps with the generator property holds because two maps
agreeing on all finite-length classes are equal; the output-length witness of a
competing map is a proof of the same proposition.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Parabolic.FiniteLengthGrothendieckAssembly

universe uR uG uV uS uH uW

open SmoothRep SmoothRep.FiniteLengthGrothendieckGroup

section Generic

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  {S : Type uS} {H : Type uH} [CommRing S] [Group H] [TopologicalSpace H]

/-- A functor preserving finite length and short exact sequences of finite-length
objects induces the unique integer-linear map whose value at each finite-length
class is the class of the functor's output, with a finite-length witness for that
output. Any witness chosen by a competing map is a proof of the same proposition. -/
theorem existsUnique_functorMap
    (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    ∃! l : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{uS, uH, uW} S H,
      ∀ (A : SmoothRep.{uR, uG, uV} R G) (hA : A.HasFiniteLength),
        ∃ hOut : (Φ.obj A).HasFiniteLength,
          l (ofRepresentation A hA) = ofRepresentation (Φ.obj A) hOut := by
  refine ⟨map Φ hl hx, fun A hA => ⟨hl A hA, map_ofRepresentation Φ hl hx A hA⟩, ?_⟩
  intro l hgen
  apply hom_ext_object R G
  intro A
  obtain ⟨hOut, h⟩ := hgen A.val A.property
  exact h.trans (map_ofRepresentation Φ hl hx A.val A.property).symm

end Generic

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual normalized parabolic induction preserves every actual short exact
sequence of smooth product-Levi representations, read on the underlying
intertwiners; in particular every sequence of finite-length terms. -/
theorem normalizedInductionFunctor_preservesShortExact {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedParabolicInductionFunctor.{uF, uV} B) := by
  let := T.topology
  intro A₁ A₂ A₃ f g _ _ _ h
  obtain ⟨hi, hq, hex⟩ := h
  obtain ⟨hi', hex', hq'⟩ := normalizedInductionExactness F T B A₁ A₂ A₃
    A₁.representation A₂.representation A₃.representation (hom f) (hom g)
    A₁.isSmooth A₂.isSmooth A₃.isSmooth hi hq hex
  exact ⟨hi', hq', hex'⟩

/-- The actual normalized Jacquet functor preserves every actual short exact
sequence of smooth `GL_n` representations, read on the underlying intertwiners;
in particular every sequence of finite-length terms. -/
theorem normalizedJacquetFunctor_preservesShortExact {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor.{uF, uV} B) := by
  let := T.topology
  intro A₁ A₂ A₃ f g _ _ _ h
  obtain ⟨hi, hq, hex⟩ := h
  obtain ⟨hi', hex', hq'⟩ := T.normalizedJacquetFunctor_map_exact B f g hi hq hex
  exact ⟨hi', hq', hex'⟩

/-- The induction clause at the saturated carrier universe. -/
theorem normalizedInductionGrothendieck :
    NormalizedInductionGrothendieckStatement.{uF, uV} F T := by
  let := T.topology
  intro n B
  exact existsUnique_functorMap (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B)
    ((normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n B)
    (normalizedInductionFunctor_preservesShortExact F T B)

/-- The Jacquet clause at the saturated carrier universe. -/
theorem normalizedJacquetGrothendieck :
    NormalizedJacquetGrothendieckStatement.{uF, uV} F T := by
  let := T.topology
  intro n B
  exact existsUnique_functorMap (T.normalizedJacquetFunctor.{uF, max uF uV} B)
    ((normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n B)
    (normalizedJacquetFunctor_preservesShortExact F T B)

end Langlands.Parabolic.FiniteLengthGrothendieckAssembly

namespace Langlands.Parabolic

universe uF uV

/-- Both actual normalized parabolic functors induce unique integer-linear maps
of the exact finite-length smooth Grothendieck groups, in every rank and block
shape, for arbitrary supplied topological data. -/
theorem normalizedParabolicGrothendieck
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedParabolicGrothendieckStatement.{uF, uV} F T :=
  ⟨FiniteLengthGrothendieckAssembly.normalizedInductionGrothendieck F T,
    FiniteLengthGrothendieckAssembly.normalizedJacquetGrothendieck F T⟩

end Langlands.Parabolic
