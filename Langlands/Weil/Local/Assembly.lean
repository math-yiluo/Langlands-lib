import Langlands.Galois.Local.AbsoluteProof
import Langlands.Galois.FiniteField.ComparisonProof
import Langlands.Weil.AlgebraicProof
import Langlands.Weil.TopologyProof
import Langlands.Weil.Local.ResidueCharacters

/-!
# Local Weil groups over separable closures in arbitrary characteristic

The general construction uses the residue map on a specified separable closure.
The published p-adic interface specializes it using the canonical local field data.
-/

noncomputable section

namespace Langlands.Weil.Local.SepClosed

open ValuativeRel

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- The actual residue field of the local field. -/
abbrev localResidueField : Type u := 𝓀[K]

instance localResidueField_finite : Finite (localResidueField K) := inferInstance

variable (Ω : Type v) [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]

/-- The residue action of the specified separable closure, with its Krull continuity. -/
def localResidueMap : Gal(Ω/K) →ₜ* Field.absoluteGaloisGroup (localResidueField K) where
  toMonoidHom := LocalGalois.SepClosed.absoluteResidueHom K Ω
  continuous_toFun := LocalGalois.SepClosed.absoluteResidueHom_continuous K Ω

/-- The residue degree, normalized by geometric Frobenius. -/
def localResidueDegree : Gal(Ω/K) →ₜ* ProfiniteIntegers :=
  (Galois.FiniteField.toProfiniteIntegers (localResidueField K)).comp (localResidueMap K Ω)

/-- The integer-Frobenius pullback, with the existing subgroup topology. -/
abbrev localWeilGroup := Pullback (localResidueDegree K Ω)

/-- The continuous projection to the absolute Galois group of the specified closure. -/
def localProjection : localWeilGroup K Ω →ₜ* Gal(Ω/K) :=
  projection (localResidueDegree K Ω)

/-- The continuous geometric degree, valued in the discrete integers. -/
def localDegree : localWeilGroup K Ω →ₜ* Degree := degree (localResidueDegree K Ω)

/-- The same degree as an ordinary integer. -/
def localDegreeInt (w : localWeilGroup K Ω) : ℤ := (localDegree K Ω w).toAdd

/-- Inertia is the degree-zero subgroup of the Weil group. -/
def localInertia : Subgroup (localWeilGroup K Ω) :=
  inertiaSubgroup (localResidueDegree K Ω)

instance localInertia_normal : (localInertia K Ω).Normal :=
  inferInstanceAs ((localDegree K Ω).toMonoidHom.ker.Normal)

/-- The finite-field comparison preserves the kernel of the residue action. -/
theorem localResidueDegree_ker :
    (localResidueDegree K Ω).toMonoidHom.ker = LocalGalois.SepClosed.absoluteInertia K Ω := by
  rw [← LocalGalois.SepClosed.absoluteResidueHom_ker K Ω]
  ext σ
  change Galois.FiniteField.profiniteEquivalence (localResidueField K)
      (LocalGalois.SepClosed.absoluteResidueHom K Ω σ) = 1 ↔
    LocalGalois.SepClosed.absoluteResidueHom K Ω σ = 1
  exact (Galois.FiniteField.profiniteEquivalence (localResidueField K)).map_eq_one_iff

/-- Absolute inertia and the input kernel are the same topological group. -/
def localGaloisInertiaEquiv :
    LocalGalois.SepClosed.absoluteInertia K Ω ≃ₜ* inertia (localResidueDegree K Ω) where
  toMulEquiv := MulEquiv.subgroupCongr (localResidueDegree_ker K Ω).symm
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Absolute inertia enters the pullback with degree zero. -/
def localInertiaInclusion :
    LocalGalois.SepClosed.absoluteInertia K Ω →ₜ* localWeilGroup K Ω :=
  (inertiaInclusion (localResidueDegree K Ω)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localGaloisInertiaEquiv K Ω))

section Galois

variable [IsGalois K Ω]

/-- Surjectivity of the residue degree, needed to choose Frobenius. -/
theorem localResidueDegree_surjective : Function.Surjective (localResidueDegree K Ω) :=
  (Galois.FiniteField.profiniteEquivalence (localResidueField K)).surjective.comp
    (LocalGalois.SepClosed.absoluteResidueHom_surjective K Ω)

/-- Every integer occurs as the degree of a Weil element. -/
theorem localDegree_surjective : Function.Surjective (localDegree K Ω) :=
  degree_surjective (localResidueDegree K Ω) (localResidueDegree_surjective K Ω)

/-- A chosen geometric Frobenius lift of degree positive one. -/
def localGeometricFrobenius : localWeilGroup K Ω :=
  (localDegree_surjective K Ω (Multiplicative.ofAdd (1 : ℤ))).choose

/-- The degree equation certifying the chosen lift. -/
theorem localGeometricFrobenius_degree :
    localDegree K Ω (localGeometricFrobenius K Ω) = Multiplicative.ofAdd (1 : ℤ) :=
  (localDegree_surjective K Ω (Multiplicative.ofAdd (1 : ℤ))).choose_spec

end Galois

/-- An unramified character with prescribed complex-unit value at degree one. -/
def localUnramifiedCharacter (z : ℂˣ) : localWeilGroup K Ω →ₜ* ℂˣ :=
  Local.unramifiedCharacter (localDegree K Ω) z

/-- The norm character, normalized by the cardinality of the actual finite residue field. -/
def localNormCharacter : localWeilGroup K Ω →ₜ* ℂˣ :=
  Local.normCharacter (localDegree K Ω) (Nat.card (localResidueField K))
    (Nat.card_pos (α := localResidueField K))

end Langlands.Weil.Local.SepClosed

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
    Field.absoluteGaloisGroup F.Carrier →ₜ* Field.absoluteGaloisGroup (localResidueField F) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact SepClosed.localResidueMap F.Carrier (AlgebraicClosure F.Carrier)

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
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact SepClosed.localResidueDegree_ker F.Carrier (AlgebraicClosure F.Carrier)

/-- The actual absolute inertia and the input kernel are the same topological group. -/
def localGaloisInertiaEquiv :
    F.absoluteInertia F.canonicalTopologicalData ≃ₜ* inertia (localResidueDegree F) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact SepClosed.localGaloisInertiaEquiv F.Carrier (AlgebraicClosure F.Carrier)

/-- Actual absolute inertia enters the local Weil group with degree zero. -/
def localInertiaInclusion :
    F.absoluteInertia F.canonicalTopologicalData →ₜ* localWeilGroup F :=
  (inertiaInclusion (localResidueDegree F)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localGaloisInertiaEquiv F))

/-- Surjectivity is inherited from the two proved arithmetic maps. -/
theorem localResidueDegree_surjective : Function.Surjective (localResidueDegree F) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact SepClosed.localResidueDegree_surjective F.Carrier (AlgebraicClosure F.Carrier)

/-- Every integer occurs as the degree of an actual local Weil element. -/
theorem localDegree_surjective : Function.Surjective (localDegree F) :=
  degree_surjective (localResidueDegree F) (localResidueDegree_surjective F)

/-- One geometric Frobenius lift, chosen only from proved degree surjectivity. -/
def localGeometricFrobenius : localWeilGroup F := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact SepClosed.localGeometricFrobenius F.Carrier (AlgebraicClosure F.Carrier)

/-- The chosen lift has geometric degree positive one. -/
theorem localGeometricFrobenius_degree :
    localDegree F (localGeometricFrobenius F) = Multiplicative.ofAdd (1 : ℤ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact SepClosed.localGeometricFrobenius_degree F.Carrier (AlgebraicClosure F.Carrier)

/-- Every complex-unit value gives an unramified character of the actual Weil group. -/
def localUnramifiedCharacter (z : ℂˣ) : localWeilGroup F →ₜ* ℂˣ :=
  unramifiedCharacter (localDegree F) z

/-- The actual local norm character, using the canonical field's residue cardinality. -/
def localNormCharacter : localWeilGroup F →ₜ* ℂˣ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact SepClosed.localNormCharacter F.Carrier (AlgebraicClosure F.Carrier)

end Langlands.Weil.Local
