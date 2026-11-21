import Langlands.Correspondence.HenniartTameWeilFields
import Langlands.Weil.Representation.NormalConjugacyClasses
import Langlands.VirtualRepresentation.Weil.Ramification
import Langlands.LocalFactor.Ramification.Herbrand.Absolute

/-!
# Wild inertia orbits and the tame conductor counts

The orbit formula over a p-adic field and the fixed-point formula over its
tame totally ramified fields, as stated targets for the fixed-cutoff average.
-/

noncomputable section

namespace Langlands.Henniart

open Weil.Local FiniteRepresentation

universe uK uW

section Wild

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Wild inertia in the actual local Weil group: the preimage of the absolute
wild inertia subgroup under the projection to the absolute Galois group. -/
def weilWildInertia : Subgroup (localWeilGroup K) :=
  (Ramification.Padic.wildInertia K).comap (localProjection K).toMonoidHom

instance weilWildInertia_normal : (weilWildInertia K).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- Isomorphism classes of irreducible complex representations of wild inertia
with open kernel, with carriers in `Type uW`. -/
abbrev WildClasses := OpenKernelIrreducibleClasses.{uK, uW} (weilWildInertia K)

/-- A representation of wild inertia is trivial on the actual upper group of
index `v` of the Weil group, intersected with wild inertia. -/
def WildTrivialAt (v : ℝ) (A : FiniteRepresentation.{0, uK, uW} ℂ (weilWildInertia K)) :
    Prop :=
  ∀ w : weilWildInertia K,
    (w : localWeilGroup K) ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup K v →
      A.representation w = 1

theorem wildTrivialAt_of_equiv {v : ℝ}
    {A B : FiniteRepresentation.{0, uK, uW} ℂ (weilWildInertia K)}
    (e : FiniteRepresentation.Equiv A B)
    (hA : WildTrivialAt K v A) : WildTrivialAt K v B := by
  intro w hw
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective x
  change B.representation w (e a) = e a
  calc
    B.representation w (e a) = e (A.representation w a) :=
      (Representation.IntertwiningMap.isIntertwining A.representation B.representation
        e.toIntertwiningMap w a).symm
    _ = e a := by rw [hA w hw]; rfl

/-- The triviality condition descends to isomorphism classes. -/
def wildClassTrivialAt (v : ℝ) : WildClasses.{uK, uW} K → Prop :=
  Quotient.lift (fun A => WildTrivialAt K v A.1) fun _ _ ⟨e⟩ =>
    propext ⟨wildTrivialAt_of_equiv K e, wildTrivialAt_of_equiv K e.symm⟩

/-- The wild classes used for the tame comparison: fixed by `J`, of dimension
dividing `p ^ r`, and trivial on every upper group of index greater than
`j / (p ^ r * m)`. -/
def tameOrbitClasses (J : Subgroup (localWeilGroup K)) (r m j : ℕ) :
    Set (WildClasses.{uK, uW} K) :=
  {c | (∀ g ∈ J, g • c = c) ∧ openKernelIrreducibleRank _ c ∣ p ^ r ∧
    ∀ v : ℝ, (j : ℝ) / ((p ^ r * m : ℕ) : ℝ) < v → wildClassTrivialAt K v c}

/-- Inertia orbits on wild classes that meet `tameOrbitClasses` and are mapped to
themselves by conjugation by `φ`. -/
def frobeniusStableTameOrbits (J : Subgroup (localWeilGroup K)) (r m j : ℕ)
    (φ : localWeilGroup K) :
    Set (MulAction.orbitRel.Quotient (localInertia K) (WildClasses.{uK, uW} K)) :=
  {o | ∃ c ∈ tameOrbitClasses.{uK, uW} K J r m j,
    (Quotient.mk'' c : MulAction.orbitRel.Quotient (localInertia K) _) = o ∧
      (Quotient.mk'' (φ • c) : MulAction.orbitRel.Quotient (localInertia K) _) = o}

end Wild

/-- Orbit formula over the base: for an open normal subgroup `J` of the Weil group
inside inertia, of index `m` prime to `p`, and a lift `φ` of geometric degree one,
`C_K(p^r m, j)` is `q_K - 1` times the number of inertia orbits of tame classes
stable under conjugation by `φ`. -/
def WeilTameOrbitFormulaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (r m j : ℕ), ¬ p ∣ m →
    ∀ (J : OpenNormalSubgroup (localWeilGroup K)), J.toSubgroup ≤ localInertia K →
      (J.toSubgroup.subgroupOf (localInertia K)).index = m →
    ∀ φ : localWeilGroup K, localDegreeInt K φ = 1 →
      Numerical.weilConductorCount.{uK, uW} K (p ^ r * m - 1) j =
        ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) *
          (frobeniusStableTameOrbits.{uK, uW} K J.toSubgroup r m j φ).encard

/-- Fixed-point formula over the tame fields: in the Frobenius coset parametrization,
the field indexed by the coset of `g` has `C_E(p^r, j)` equal to `q_K - 1` times the
number of tame classes fixed by conjugation by `g * φ`. -/
def WeilTameFieldFixedPointStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (r m j : ℕ), ¬ p ∣ m →
    ∀ (φ : localWeilGroup K), localDegreeInt K φ = 1 →
    ∀ (D : TameWeilFrobeniusData K m φ) (g : localInertia K),
      Numerical.weilConductorCount.{uK, uW}
          ((D.fieldEquiv (QuotientGroup.mk g)).1.asPadicField (p := p)) (p ^ r - 1) j =
        ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) *
          {c ∈ tameOrbitClasses.{uK, uW} K D.kernel.toSubgroup r m j |
            ((g : localWeilGroup K) * φ) • c = c}.encard

/-- The three arithmetic and representation-theoretic inputs imply the
fixed-cutoff average. -/
def WeilTameAveragingFromOrbitFormulasStatement : Prop :=
  TameWeilFrobeniusParametrizationStatement.{uK} →
    WeilTameOrbitFormulaStatement.{uK, uW} →
      WeilTameFieldFixedPointStatement.{uK, uW} → WeilTameAveragingStatement.{uK, uW}

end Langlands.Henniart
