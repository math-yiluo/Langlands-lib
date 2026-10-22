import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
import Langlands.ClassFieldTheory.Local.Units
import Langlands.LocalFactor.Ramification.Galois
import Langlands.HarmonicAnalysis.Conductor
import Langlands.Representation.Twist.Definitions

/-!
# Finite-character conductor transport under local reciprocity

These propositions compare the existing principal-unit conductor with the
actual finite-Galois Artin sum. Reciprocity existence is a separate target;
no conductor equality or ramification compatibility is part of its relation.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- The actual one-dimensional representation associated to a complex
unit-valued character: the group acts on the complex line by multiplication. -/
def rankOneCharacterRepresentation {G : Type u} [Group G]
    (χ : G →* ℂˣ) : Representation ℂ G ℂ :=
  Langlands.characterRepresentation χ

@[simp]
theorem rankOneCharacterRepresentation_apply {G : Type u} [Group G]
    (χ : G →* ℂˣ) (g : G) (z : ℂ) :
    rankOneCharacterRepresentation χ g z = (χ g : ℂ) * z := rfl

/-- The quotient-kernel unit filtration and the valuation principal-unit
filtration describe the same actual subgroups, including level zero. -/
def UnitFiltrationComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (n : ℕ),
    T.unitFiltration n = T.principalUnits n

/-- The normalized finite reciprocity maps carry units to actual inertia,
and principal units to the actual first lower ramification group. -/
def FiniteReciprocityInertiaImages : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          (T.unitSubgroup.map (finiteFamilyOfHom r L).toMonoidHom =
            Ramification.Padic.inertia S F.Carrier) ∧
          ((T.unitFiltration 1).map (finiteFamilyOfHom r L).toMonoidHom =
            Ramification.Padic.lowerRamificationGroup S F.Carrier 1)

/-- A finite Galois character and its multiplicative character transported
by normalized reciprocity have equal conductor exponents. The Artin side
is the original rational fixed-space sum, not a newly defined integer. -/
def FiniteReciprocityConductorTransport : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData)
          (χ : L.galoisGroup →ₜ* ℂˣ),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          (T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) : ℚ) =
            @Ramification.Padic.artinConductor p _ (L.asPadicField (p := p)) S F.Carrier
              (inferInstanceAs (Field F.Carrier))
              (inferInstanceAs (Algebra (Padic p) F.Carrier))
              (inferInstanceAs (Algebra F.Carrier L.field))
              (inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)) ℂ _ ℂ _ _ _
              (by
                change Representation ℂ L.galoisGroup ℂ
                exact rankOneCharacterRepresentation χ.toMonoidHom)

/-- The same Artin conductor is bounded by an integer exactly when the
transported character kills that actual unit-congruence level. -/
def FiniteReciprocityConductorLevels : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData)
          (χ : L.galoisGroup →ₜ* ℂˣ) (n : ℕ),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          @Ramification.Padic.artinConductor p _ (L.asPadicField (p := p)) S F.Carrier
              (inferInstanceAs (Field F.Carrier))
              (inferInstanceAs (Algebra (Padic p) F.Carrier))
              (inferInstanceAs (Algebra F.Carrier L.field))
              (inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)) ℂ _ ℂ _ _ _
              (by
                change Representation ℂ L.galoisGroup ℂ
                exact rankOneCharacterRepresentation χ.toMonoidHom) ≤ (n : ℚ) ↔
            ∀ a ∈ T.unitFiltration n, χ (finiteFamilyOfHom r L a) = 1

/-- Unramified characters have conductor zero; conductor at most one means
triviality on wild inertia, retaining the unramified case. -/
def FiniteReciprocityUnramifiedTameCharacters : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData)
          (χ : L.galoisGroup →ₜ* ℂˣ),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          (T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) = 0 ↔
            ∀ σ ∈ Ramification.Padic.inertia S F.Carrier, χ σ = 1) ∧
          (T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) ≤ 1 ↔
            ∀ σ ∈ Ramification.Padic.lowerRamificationGroup S F.Carrier 1,
              χ σ = 1)

/-- Finite abelian character and conductor consequences of the explicitly
normalized reciprocity relation, with the unconditional filtration comparison. -/
def FiniteCharacterConductorTheorems : Prop :=
  UnitFiltrationComparison.{u} ∧
    FiniteReciprocityInertiaImages.{u} ∧
      FiniteReciprocityConductorTransport.{u} ∧
        FiniteReciprocityConductorLevels.{u} ∧
          FiniteReciprocityUnramifiedTameCharacters.{u}

end Langlands.LocalClassField
