import Langlands.Correspondence.OperationCompatibility
import Langlands.Correspondence.AutomorphicRelations
import Langlands.Representation.Conductor.Congruence
import Langlands.Representation.Induction.BlockFactors
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.WeilDeligne.DirectSum
import Mathlib.RepresentationTheory.Intertwining

/-!
# The unramified normalization of a full correspondence

Unramified parameters (trivial on inertia, zero monodromy) correspond to classes
with a nonzero `GL_n(O_F)`-fixed vector, and the sum of the unramified characters
`χ_i ∘ τ_F` corresponds to the spherical constituent of the normalized principal
series induced from `χ_1 ⊗ ⋯ ⊗ χ_n`. These are conditions on a given family.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The hyperspecial maximal compact subgroup `GL_(r+1)(O_F)` of the actual group,
for the canonical valuation ring of `F`. -/
def sphericalSubgroup (r : ℕ) : Subgroup (GeneralLinear (r + 1) F.Carrier) :=
  letI := F.canonicalTopologicalData.valuativeRel
  Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r

/-- A class of rank `r + 1` is spherical: a representative has a nonzero vector
fixed by `GL_(r+1)(O_F)`. -/
def IsSphericalClass {r : ℕ} (π : AutomorphicClass.{uF, uA} F r.succPNat) : Prop :=
  ∃ A : AutomorphicObject.{uF, uA} F r.succPNat,
    automorphicClassOf F A = π ∧
      fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥

/-- A parameter class is unramified: it is the class of `(A, 0)` for a Weil
representation `A` on which inertia acts trivially. -/
def IsUnramifiedParameterClass {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) : Prop :=
  ∃ A : Weil.Local.LocalWeilRepresentation.{uF, uP} F,
    A.IsUnramified (Weil.Local.localInertia F) ∧
      WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy
            (Weil.Local.localNormCharacter F).toMonoidHom A) =
        parameterForget F D

/-- The upper Borel block shape of `GL_(r+1)`: `r + 1` blocks of size one. -/
def borelShape (r : ℕ) : GeneralLinear.BlockShape (r + 1) where
  length := r + 1
  size := fun _ => 1
  positive := fun _ => Nat.one_pos
  sum_eq := by simp

/-- The normalized principal series `i(χ_1, …, χ_(r+1))`: normalized induction
from the upper Borel subgroup of the characters `χ_i` of `GL_1(F)`. -/
def principalSeries (r : ℕ) (χ : Fin (r + 1) → QuasiCharacter F) :=
  F.canonicalTopologicalData.normalizedProductInduced (borelShape r)
    (fun i => characterRepresentation (determinantQuasiCharacter F 1 (χ i)))

/-- `π` is a subquotient of `ρ`: some subrepresentation of `ρ` maps onto `π` by
an intertwining map. The carriers may lie in different universes. -/
def IsSubquotientOf {G : Type*} [Group G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (π : Representation ℂ G W) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π),
    Function.Surjective f.toLinearMap

/-- `D` is the class of `⊕_i (χ_i ∘ τ_F, 0)` for the reciprocity candidate `e`. -/
def IsCharacterSumParameter (e : ReciprocityCandidate F) {r : ℕ}
    (χ : Fin (r + 1) → QuasiCharacter F) (D : WeilDeligneClass.{uF, uP} F r.succPNat) :
    Prop :=
  ∃ A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F,
    WeilDeligneRepresentation.classOf A = parameterForget F D ∧
      Nonempty (WeilDeligneRepresentation.Equiv
        (WeilDeligneRepresentation.directSum fun i =>
          WeilDeligneRepresentation.zeroMonodromy
            (Weil.Local.localNormCharacter F).toMonoidHom
            (FiniteRepresentation.of
              (Langlands.characterRepresentation (weilCharacter F e (χ i))))) A)

/-- Unramified parameters are exactly those with spherical images. -/
def SphericalCompatibility (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ (r : ℕ) (D : WeilDeligneClass.{uF, uP} F r.succPNat),
    IsUnramifiedParameterClass F D ↔ IsSphericalClass F (c r.succPNat D)

/-- For unramified quasi-characters `χ_1, …, χ_(r+1)`, the parameter
`⊕_i (χ_i ∘ τ_F, 0)` exists, and its image is a spherical subquotient of the
normalized principal series `i(χ_1, …, χ_(r+1))`. -/
def PrincipalSeriesCompatibility (e : ReciprocityCandidate F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ (r : ℕ) (χ : Fin (r + 1) → QuasiCharacter F),
    (∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) →
      ∃ D : WeilDeligneClass.{uF, uP} F r.succPNat,
        IsCharacterSumParameter F e χ D ∧
          ∃ A : AutomorphicObject.{uF, uA} F r.succPNat,
            automorphicClassOf F A = c r.succPNat D ∧
              fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ ∧
              IsSubquotientOf (principalSeries F r χ) A.obj.representation

/-- The unramified normalization of a full map relative to `e`. -/
def UnramifiedCompatibility (e : ReciprocityCandidate F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  SphericalCompatibility F c ∧ PrincipalSeriesCompatibility F e c

end Langlands.Correspondence
