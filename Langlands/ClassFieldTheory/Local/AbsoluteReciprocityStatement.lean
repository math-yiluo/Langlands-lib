import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalClassField.Units
import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# Absolute upper ramification and local reciprocity

The absolute filtration is constructed from all finite Galois restrictions.
The target below is its actual image in the Galois abelianization.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Valuation units correspond to the image of actual absolute inertia in
its Galois abelianization, for every compatible topological realization. -/
def AbsoluteReciprocityInertiaImage : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        T.unitSubgroup.map r.toMonoidHom =
          (F.absoluteInertia T).map (localAbelianGaloisProjection F).toMonoidHom

/-- Natural unit levels map onto the image of the actual absolute upper
ramification group. The level-zero unit/inertia endpoint is included. -/
def AbsoluteReciprocityHigherUnitImages : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ n : ℕ,
          (T.unitFiltration n).map r.toMonoidHom =
            Ramification.Padic.localAbelianUpperRamificationGroup F n

/-- Real nonnegative upper indices use the ceiling unit level after passing
to the abelianization, by the abelian integral-break convention. -/
def AbsoluteReciprocityRealUnitImages : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ v : ℝ, 0 ≤ v →
          (T.unitFiltration ⌈v⌉₊).map r.toMonoidHom =
            Ramification.Padic.localAbelianUpperRamificationGroup F v

/-- The conductor of any continuous complex quasicharacter is bounded by a
unit level exactly when the corresponding absolute abelian upper group is
contained in the actual reciprocity image of its kernel. -/
def AbsoluteQuasicharacterConductorLevels : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (χ : F.Carrierˣ →ₜ* ℂˣ) (v : ℝ), 0 ≤ v →
          (T.multiplicativeConductor χ ≤ ⌈v⌉₊ ↔
            Ramification.Padic.localAbelianUpperRamificationGroup F v ≤
              χ.toMonoidHom.ker.map r.toMonoidHom)

/-- Positive conductor n+1 is detected at the absolute abelian upper group
n and vanishes at every strictly later real level, including the tame case. -/
def AbsoluteQuasicharacterLastUpperBreak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (χ : F.Carrierˣ →ₜ* ℂˣ) (n : ℕ),
          (T.multiplicativeConductor χ = n + 1 ↔
            (¬ Ramification.Padic.localAbelianUpperRamificationGroup F n ≤
              χ.toMonoidHom.ker.map r.toMonoidHom) ∧
            ∀ v : ℝ, (n : ℝ) < v →
              Ramification.Padic.localAbelianUpperRamificationGroup F v ≤
                χ.toMonoidHom.ker.map r.toMonoidHom)

/-- Absolute inertia and higher-unit transport, with the conductor and
last-break criteria for arbitrary continuous complex quasicharacters. -/
def AbsoluteUpperReciprocityTheorems : Prop :=
  AbsoluteReciprocityInertiaImage.{u} ∧
    AbsoluteReciprocityHigherUnitImages.{u} ∧
      AbsoluteReciprocityRealUnitImages.{u} ∧
        AbsoluteQuasicharacterConductorLevels.{u} ∧
          AbsoluteQuasicharacterLastUpperBreak.{u}

end Langlands.LocalClassField
