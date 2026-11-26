import Langlands.BaseChange.WeylSphericalTraceReplacement
import Langlands.BaseChange.RegularElementaryOrbit
import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Data.Finsupp.Multiset

/-!
# Weyl Jacquet multisets of unramified principal series

Henniart–Lemaire (2011), I.5.4 and I.5.5, Lemme 1. The normalized Jacquet module
of a representation of `GL_(r+1)(F)` along the upper Borel subgroup is restricted to
the vectors fixed by the integral diagonal subgroup `T(𝒪_F)`. The diagonal elements
with the canonical uniformizer in one coordinate act there by commuting operators,
and the dimensions of their simultaneous generalized eigenspaces give a multiset of
tuples of uniformizer values. The proposition states that this multiset is the full
Weyl multiset for the normalized unramified principal series, a submultiset for its
irreducible subquotients, the full multiset for a spherical generic subquotient, and
free of tuples in the opposite order for a generic subquotient without spherical
vectors.
-/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Unramified Langlands.Correspondence
open Langlands.GeneralLinear.BlockShape

universe uF uV

section Multiset

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance weylJacquetFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance weylJacquetGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance weylJacquetGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The integral diagonal subgroup `T(𝒪_F)` of the Levi of the upper Borel subgroup:
the Levi elements whose diagonal matrix lies in `GL_(r+1)(𝒪_F)`. -/
def borelIntegralDiagonal (r : ℕ) : Subgroup ((borelShape r).Levi F.Carrier) :=
  (sphericalSubgroup F r).comap ((borelShape r).leviEmbedding F.Carrier)

/-- The integral diagonal subgroup is open for the canonical Levi topology. -/
def borelIntegralDiagonalOpen (r : ℕ) : OpenSubgroup ((borelShape r).Levi F.Carrier) :=
  (sphericalOpenSubgroup F r).comap ((borelShape r).leviEmbedding F.Carrier)
    (F.canonicalTopologicalData.blockLeviEmbedding (borelShape r)).continuous

@[simp]
theorem borelIntegralDiagonalOpen_toSubgroup (r : ℕ) :
    (borelIntegralDiagonalOpen F r).toSubgroup = borelIntegralDiagonal F r := rfl

/-- A diagonal Levi element is integral exactly when each diagonal entry has
valuation zero. -/
theorem singletonLevi_mem_borelIntegralDiagonal_iff {r : ℕ} (a : Fin (r + 1) → F.Carrierˣ) :
    (singletonLevi F.Carrier a : (borelShape r).Levi F.Carrier) ∈ borelIntegralDiagonal F r ↔
      ∀ i, F.canonicalTopologicalData.ord (a i : F.Carrier) = 0 := by
  have h : (borelShape r).leviEmbedding F.Carrier (singletonLevi F.Carrier a) =
      GeneralLinear.Iwasawa.diagonalUnits a := by
    apply Units.ext
    rw [GeneralLinear.Iwasawa.diagonalUnits_val]
    exact leviEmbedding_singletonLevi_val F.Carrier a
  change (borelShape r).leviEmbedding F.Carrier (singletonLevi F.Carrier a) ∈
    sphericalOpenSubgroup F r ↔ _
  rw [h]
  exact diagonalUnits_mem_sphericalOpenSubgroup_iff F a

/-- The diagonal Levi element with the canonical uniformizer in coordinate `i` and `1`
in the other coordinates. -/
def borelUniformizerLevi (r : ℕ) (i : Fin (r + 1)) : (borelShape r).Levi F.Carrier :=
  (borelShape r).blockScalarLevi F.Carrier
    (Pi.mulSingle i F.canonicalTopologicalData.uniformizerUnit)

theorem borelUniformizerLevi_eq_singletonLevi (r : ℕ) (i : Fin (r + 1)) :
    borelUniformizerLevi F r i =
      singletonLevi F.Carrier (Pi.mulSingle i F.canonicalTopologicalData.uniformizerUnit) :=
  rfl

/-- Its embedded matrix is the diagonal matrix with the canonical uniformizer at `i`. -/
theorem leviEmbedding_borelUniformizerLevi_val (r : ℕ) (i : Fin (r + 1)) :
    ((borelShape r).leviEmbedding F.Carrier (borelUniformizerLevi F r i)).val =
      Matrix.diagonal fun j =>
        (((Pi.mulSingle i F.canonicalTopologicalData.uniformizerUnit :
          Fin (r + 1) → F.Carrierˣ) j : F.Carrierˣ) : F.Carrier) :=
  leviEmbedding_singletonLevi_val F.Carrier _

theorem borelUniformizerLevi_mem_center (r : ℕ) (i : Fin (r + 1)) :
    borelUniformizerLevi F r i ∈ Subgroup.center ((borelShape r).Levi F.Carrier) :=
  (borelShape r).blockScalarLevi_mem_center F.Carrier _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}

/-- The vectors of the normalized Borel Jacquet module fixed by `T(𝒪_F)`. -/
def borelJacquetIntegralFixed (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) :
    Submodule ℂ ((borelShape r).JacquetModule ρ) :=
  fixedVectors (F.canonicalNormalizedJacquet (borelShape r) ρ) (borelIntegralDiagonal F r)

/-- The integral diagonal fixed space of an admissible representation is
finite-dimensional. -/
theorem finiteDimensional_borelJacquetIntegralFixed
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ) :
    FiniteDimensional ℂ (borelJacquetIntegralFixed F ρ) :=
  (Parabolic.isAdmissible_normalizedJacquet F F.canonicalTopologicalData (borelShape r) ρ
    hρ).2 (borelIntegralDiagonalOpen F r)

theorem borelUniformizerLevi_mapsTo
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (i : Fin (r + 1)) :
    Set.MapsTo (F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i))
      (borelJacquetIntegralFixed F ρ) (borelJacquetIntegralFixed F ρ) := by
  intro w hw m
  have hz := Subgroup.mem_center_iff.mp (borelUniformizerLevi_mem_center F r i)
    (m : (borelShape r).Levi F.Carrier)
  have hwm : F.canonicalNormalizedJacquet (borelShape r) ρ
      (m : (borelShape r).Levi F.Carrier) w = w := hw m
  change F.canonicalNormalizedJacquet (borelShape r) ρ (m : (borelShape r).Levi F.Carrier)
      (F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i) w) =
    F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i) w
  rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply, hwm]

/-- The normalized action of the `i`-th uniformizer element on the integral diagonal
fixed space. -/
def borelJacquetUniformizerAction
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (i : Fin (r + 1)) :
    Module.End ℂ (borelJacquetIntegralFixed F ρ) :=
  (F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i)).restrict
    (borelUniformizerLevi_mapsTo F ρ i)

theorem commute_borelJacquetUniformizerAction
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (i j : Fin (r + 1)) :
    Commute (borelJacquetUniformizerAction F ρ i) (borelJacquetUniformizerAction F ρ j) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have hz := Subgroup.mem_center_iff.mp (borelUniformizerLevi_mem_center F r i)
    (borelUniformizerLevi F r j)
  change F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i)
      (F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r j) w) =
    F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r j)
      (F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i) w)
  rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]

/-- The simultaneous generalized weight space with uniformizer values `z`: the vectors of
the integral diagonal fixed space killed by a power of the action of the `i`-th
uniformizer element minus `z i`, for every `i`. -/
def borelJacquetWeightSpace (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (z : Fin (r + 1) → ℂˣ) : Submodule ℂ (borelJacquetIntegralFixed F ρ) :=
  ⨅ i, (borelJacquetUniformizerAction F ρ i).maxGenEigenspace (z i : ℂ)

/-- The multiplicity of `z` in the Borel Jacquet module: the dimension of its
simultaneous generalized weight space. -/
def borelJacquetMultiplicity (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (z : Fin (r + 1) → ℂˣ) : ℕ :=
  Module.finrank ℂ (borelJacquetWeightSpace F ρ z)

open Classical in
/-- The multiset of uniformizer-value tuples of the normalized Borel Jacquet module,
each tuple counted with its multiplicity. It is the empty multiset when infinitely many
tuples have positive multiplicity, which does not happen for admissible
representations. -/
def borelJacquetMultiset (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) :
    Multiset (Fin (r + 1) → ℂˣ) :=
  if h : (Function.support (borelJacquetMultiplicity F ρ)).Finite then
    Finsupp.toMultiset (Finsupp.ofSupportFinite _ h)
  else 0

/-- On a finite-dimensional integral diagonal fixed space only finitely many tuples have
positive multiplicity. -/
theorem finite_support_borelJacquetMultiplicity
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    [FiniteDimensional ℂ (borelJacquetIntegralFixed F ρ)] :
    (Function.support (borelJacquetMultiplicity F ρ)).Finite := by
  let f := borelJacquetUniformizerAction F ρ
  have hind : iSupIndep fun χ : Fin (r + 1) → ℂ => ⨅ i, (f i).maxGenEigenspace (χ i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm
        (commute_borelJacquetUniformizerAction F ρ j i) φ)
  have hfin : {χ : Fin (r + 1) → ℂ | ⨅ i, (f i).maxGenEigenspace (χ i) ≠ ⊥}.Finite := by
    let := hind.fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp
      (Finite.of_fintype {χ : Fin (r + 1) → ℂ // ⨅ i, (f i).maxGenEigenspace (χ i) ≠ ⊥})
  refine (hfin.preimage fun z _ w _ h => funext fun i => Units.ext (congrFun h i)).subset ?_
  intro z hz hbot
  apply hz
  change Module.finrank ℂ (borelJacquetWeightSpace F ρ z) = 0
  rw [show borelJacquetWeightSpace F ρ z = ⊥ from hbot]
  exact finrank_bot ℂ _

/-- On a finite-dimensional integral diagonal fixed space the multiset counts each tuple
with the dimension of its simultaneous generalized weight space. -/
theorem count_borelJacquetMultiset_of_finiteDimensional
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    [FiniteDimensional ℂ (borelJacquetIntegralFixed F ρ)]
    [DecidableEq (Fin (r + 1) → ℂˣ)] (z : Fin (r + 1) → ℂˣ) :
    (borelJacquetMultiset F ρ).count z = borelJacquetMultiplicity F ρ z := by
  unfold borelJacquetMultiset
  split_ifs with h
  · rw [Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe]
  · exact absurd (finite_support_borelJacquetMultiplicity F ρ) h

/-- For an admissible representation the multiset counts each tuple with the dimension of
its simultaneous generalized weight space. -/
theorem count_borelJacquetMultiset
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ)
    [DecidableEq (Fin (r + 1) → ℂˣ)] (z : Fin (r + 1) → ℂˣ) :
    (borelJacquetMultiset F ρ).count z = borelJacquetMultiplicity F ρ z := by
  have := finiteDimensional_borelJacquetIntegralFixed F ρ hρ
  exact count_borelJacquetMultiset_of_finiteDimensional F ρ z

/-- The count formula for the normalized unramified principal series. -/
theorem count_borelJacquetMultiset_principalSeriesOfTuple (z : Fin (r + 1) → ℂˣ)
    [DecidableEq (Fin (r + 1) → ℂˣ)] (y : Fin (r + 1) → ℂˣ) :
    (borelJacquetMultiset F (principalSeriesOfTuple F z)).count y =
      borelJacquetMultiplicity F (principalSeriesOfTuple F z) y :=
  count_borelJacquetMultiset F _ (SphericalExistence.principalSeriesOfTuple_isAdmissible F z) y

/-- The count formula for an irreducible admissible representation. -/
theorem count_borelJacquetMultiset_automorphicObject
    (A : AutomorphicObject.{uF, uV} F r.succPNat)
    [DecidableEq (Fin (r + 1) → ℂˣ)] (y : Fin (r + 1) → ℂˣ) :
    (borelJacquetMultiset F (r := r) A.obj.representation).count y =
      borelJacquetMultiplicity F (r := r) A.obj.representation y :=
  count_borelJacquetMultiset F (r := r) _ A.property.2 y

end Multiset

section Statement

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance weylJacquetStatementFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance weylJacquetStatementGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance weylJacquetStatementGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Henniart–Lemaire (2011), I.5.4 and I.5.5, Lemme 1, for the normalized unramified
principal series of `GL_(r+1)(F)` with uniformizer values `z`. The Borel Jacquet multiset
of the principal series is the full Weyl multiset of `z`. Each irreducible admissible
subquotient has a submultiset. A Whittaker generic subquotient has the full multiset when
it has a nonzero `GL_(r+1)(𝒪_F)`-fixed vector, and otherwise no tuple of its multiset has
weakly decreasing absolute values. -/
def UnramifiedWeylJacquetSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ) (z : Fin (r + 1) → ℂˣ),
    borelJacquetMultiset F (principalSeriesOfTuple F z) = weylTupleMultiset z ∧
    ∀ A : AutomorphicObject.{uF, uV} F r.succPNat,
      IsSubquotientOf (principalSeriesOfTuple F z) A.obj.representation →
        borelJacquetMultiset F (r := r) A.obj.representation ≤ weylTupleMultiset z ∧
        ∀ ψ : NontrivialAdditiveCharacter F,
          Whittaker.IsGeneric ψ r A.obj.representation →
            (fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ →
              borelJacquetMultiset F (r := r) A.obj.representation = weylTupleMultiset z) ∧
            (fixedVectors A.obj.representation (sphericalSubgroup F r) = ⊥ →
              ∀ y ∈ borelJacquetMultiset F (r := r) A.obj.representation,
                ¬ IsOppositeWeightOrder y)

/-- The statement supplies `HasWeylJacquetSupport` for the actual Borel Jacquet multisets
of every family of generic irreducible subquotients of unramified principal series, with
spherical meaning a nonzero `GL_(r+1)(𝒪_F)`-fixed vector. -/
theorem UnramifiedWeylJacquetSupportStatement.hasWeylJacquetSupport
    (h : UnramifiedWeylJacquetSupportStatement.{uF, uV}) {I : Type*} {r : ℕ}
    (inducing : I → Fin (r + 1) → ℂˣ) (A : I → AutomorphicObject.{uF, uV} F r.succPNat)
    (hsub : ∀ i, IsSubquotientOf (principalSeriesOfTuple F (inducing i))
      (A i).obj.representation)
    (hgen : ∀ i, ∃ ψ : NontrivialAdditiveCharacter F,
      Whittaker.IsGeneric ψ r (A i).obj.representation) :
    HasWeylJacquetSupport inducing
      (fun i => fixedVectors (A i).obj.representation (sphericalSubgroup F r) ≠ ⊥)
      (fun i => borelJacquetMultiset F (r := r) (A i).obj.representation) := by
  intro i
  obtain ⟨-, hA⟩ := h p F r (inducing i)
  obtain ⟨hle, hgenA⟩ := hA (A i) (hsub i)
  obtain ⟨ψ, hψ⟩ := hgen i
  obtain ⟨hsph, hnon⟩ := hgenA ψ hψ
  exact ⟨hle, hsph, fun hns => hnon (not_not.mp hns)⟩

end Statement

end Langlands.BaseChange
