import Langlands.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Parabolic.LeviBridges

/-! Actual normalized radical coinvariants of a compactly induced orbit piece. -/

noncomputable section
open CategoryTheory
open scoped NNReal

namespace Langlands.Parabolic

universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Normalized radical coinvariants for representations of the parabolic itself.
The Levi acts through its section, twisted by the inverse positive half modulus. -/
def normalizedCoinvariantsFunctor (δ : B.Levi F →* ℝ≥0ˣ) :
    Rep.{uV} ℂ (B.parabolic F) ⥤ Rep.{uV} ℂ (B.Levi F) where
  obj A := Rep.of (twist (Jacquet.inverseHalfCharacter δ) (leviCoinvariants B A.ρ))
  map f := Rep.ofHom (twistIntertwining (Jacquet.inverseHalfCharacter δ)
    (leviCoinvariantsMap B f.hom))
  map_id A := by
    ext v
    rfl
  map_comp f g := by
    ext v
    rfl

@[simp]
theorem normalizedCoinvariantsFunctor_map_mk (δ : B.Levi F →* ℝ≥0ˣ)
    {A A' : Rep.{uV} ℂ (B.parabolic F)} (f : A ⟶ A') (v : A) :
    ((normalizedCoinvariantsFunctor B δ).map f).hom
      (Jacquet.mk A.ρ (B.unipotentRadical F) v) =
        Jacquet.mk A'.ρ (B.unipotentRadical F) (f.hom v) := rfl

end Langlands.Parabolic

namespace Langlands.Geometric

universe uR uG uF uV

section RawOrbit

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugated restriction and compact induction with arbitrary algebraic
covariance data. Restricting inputs to smooth representations gives `orbitPiece`. -/
def rawOrbitPiece (P Q : Subgroup G) (w : G) :
    Rep.{uV} R P ⥤ Rep.{max uG uV} R Q :=
  Rep.resFunctor (stabilizerToInducing P Q w) ⋙
    Induction.compactInductionFunctor (orbitStabilizer P Q w) ⋙
    ObjectProperty.ι (fun A : Rep.{max uG uV} R Q => IsSmooth A.ρ)

@[simp]
theorem orbitPiece_eq_rawOrbitPiece (P Q : Subgroup G) (w : G) :
    orbitPiece.{uR, uG, uV} (R := R) P Q w =
      ObjectProperty.ι (fun A : Rep.{uV} R P => IsSmooth A.ρ) ⋙
        rawOrbitPiece P Q w := rfl

end RawOrbit

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The actual compact orbit piece for normalized parabolic induction, followed
by normalized radical coinvariants for the target parabolic. The orbit is
`P_B * w⁻¹ * P_C`, so the stabilizer representation uses conjugation by `w⁻¹`. -/
def parabolicOrbitJacquetFunctor (w : Equiv.Perm (Fin n)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      Rep.{max uF uV} ℂ (C.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.inducingFunctor (T.leviHalfCharacter B) ⋙
    rawOrbitPiece (B.parabolic F.Carrier) (C.parabolic F.Carrier)
      (permutation n F.Carrier w) ⋙
    Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)

end Langlands.Geometric
