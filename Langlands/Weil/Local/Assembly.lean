import Langlands.Galois.Local.AbsoluteProof
import Langlands.Galois.FiniteField.ComparisonProof
import Langlands.Weil.AlgebraicProof
import Langlands.Weil.TopologyProof
import Langlands.Weil.Local.ResidueCharacters

/-!
# The actual Weil group of a finite p-adic extension

The field, residue action, and geometric Frobenius normalization are constructed.
The group and topology are the existing integer-Frobenius pullback.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The actual residue field of the canonical topological realization. -/
abbrev localResidueField : Type u :=
  F.residueField F.canonicalTopologicalData

instance localResidueField_finite : Finite (localResidueField F) :=
  F.residueField_finite F.canonicalTopologicalData

/-- The constructed residue action, bundled with its proved continuity. -/
def localResidueMap :
    Field.absoluteGaloisGroup F.Carrier →ₜ* Field.absoluteGaloisGroup (localResidueField F) where
  toMonoidHom := F.absoluteResidueHom F.canonicalTopologicalData
  continuous_toFun := F.absoluteResidueHom_continuous F.canonicalTopologicalData

/-- The actual residue degree, normalized by geometric Frobenius. -/
def localResidueDegree : Field.absoluteGaloisGroup F.Carrier →ₜ* ProfiniteIntegers :=
  (Galois.FiniteField.toProfiniteIntegers (localResidueField F)).comp (localResidueMap F)

/-- The actual local Weil group, with the existing pullback group and topology. -/
abbrev localWeilGroup := Pullback (localResidueDegree F)

/-- Continuous projection to the actual absolute Galois group. -/
def localProjection : localWeilGroup F →ₜ* Field.absoluteGaloisGroup F.Carrier :=
  projection (localResidueDegree F)

/-- Continuous geometric degree with values in the discrete integer group. -/
def localDegree : localWeilGroup F →ₜ* Degree :=
  degree (localResidueDegree F)

/-- The same degree as an ordinary integer. -/
def localDegreeInt (w : localWeilGroup F) : ℤ := (localDegree F w).toAdd

/-- Inertia as a subgroup of the actual Weil group. -/
def localInertia : Subgroup (localWeilGroup F) :=
  inertiaSubgroup (localResidueDegree F)

instance localInertia_normal : (localInertia F).Normal :=
  inferInstanceAs ((localDegree F).toMonoidHom.ker.Normal)

/-- The comparison with profinite integers does not change the residue kernel. -/
theorem localResidueDegree_ker :
    (localResidueDegree F).toMonoidHom.ker = F.absoluteInertia F.canonicalTopologicalData := by
  rw [← F.absoluteResidueHom_ker F.canonicalTopologicalData]
  ext σ
  change Galois.FiniteField.profiniteEquivalence (localResidueField F)
      (F.absoluteResidueHom F.canonicalTopologicalData σ) = 1 ↔
    F.absoluteResidueHom F.canonicalTopologicalData σ = 1
  exact (Galois.FiniteField.profiniteEquivalence (localResidueField F)).map_eq_one_iff

/-- The actual absolute inertia and the input kernel are the same topological group. -/
def localGaloisInertiaEquiv :
    F.absoluteInertia F.canonicalTopologicalData ≃ₜ* inertia (localResidueDegree F) where
  toMulEquiv := MulEquiv.subgroupCongr (localResidueDegree_ker F).symm
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Actual absolute inertia enters the local Weil group with degree zero. -/
def localInertiaInclusion :
    F.absoluteInertia F.canonicalTopologicalData →ₜ* localWeilGroup F :=
  (inertiaInclusion (localResidueDegree F)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localGaloisInertiaEquiv F))

/-- Surjectivity is inherited from the two proved arithmetic maps. -/
theorem localResidueDegree_surjective : Function.Surjective (localResidueDegree F) :=
  (Galois.FiniteField.profiniteEquivalence (localResidueField F)).surjective.comp
    (F.absoluteResidueHom_surjective F.canonicalTopologicalData)

/-- Every integer occurs as the degree of an actual local Weil element. -/
theorem localDegree_surjective : Function.Surjective (localDegree F) :=
  degree_surjective (localResidueDegree F) (localResidueDegree_surjective F)

/-- One geometric Frobenius lift, chosen only from proved degree surjectivity. -/
def localGeometricFrobenius : localWeilGroup F :=
  (localDegree_surjective F (Multiplicative.ofAdd (1 : ℤ))).choose

/-- The chosen lift has geometric degree positive one. -/
theorem localGeometricFrobenius_degree :
    localDegree F (localGeometricFrobenius F) = Multiplicative.ofAdd (1 : ℤ) :=
  (localDegree_surjective F (Multiplicative.ofAdd (1 : ℤ))).choose_spec

/-- Every complex-unit value gives an unramified character of the actual Weil group. -/
def localUnramifiedCharacter (z : ℂˣ) : localWeilGroup F →ₜ* ℂˣ :=
  unramifiedCharacter (localDegree F) z

/-- The actual local norm character, using the canonical field's residue cardinality. -/
def localNormCharacter : localWeilGroup F →ₜ* ℂˣ :=
  canonicalResidueNormCharacter F (localDegree F)

end Langlands.Weil.Local
