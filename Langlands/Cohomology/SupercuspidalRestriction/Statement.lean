import Langlands.Cohomology.SupercuspidalExt.Statement
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Classification.FixedCentralSplittingStatement
import Langlands.Group.GL.Padic

/-!
# Restriction of supercuspidal representations to a subgroup with compact center

Harris (1997, p.96) restricts a supercuspidal representation to an open
subgroup `GJ^0` with compact center and uses that the restriction still has
compactly supported matrix coefficients. The published supercuspidal `Ext`
vanishing statement takes as a hypothesis that the restriction is a finite
direct sum of irreducible representations with compactly supported matrix
coefficients. This module states when that hypothesis holds: in general, for
an irreducible representation whose coefficients are compactly supported
modulo the center (after Bernstein–Zelevinsky 1976, 3.21 and 3.26), and for
supercuspidal representations of `GL_n(F)` restricted to the subgroup of
matrices whose determinant is a unit (Bernstein–Zelevinsky 1976, 3.20–3.26).
It also states Harish-Chandra's theorem in the direction needed. None of the
assertions is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.SupercuspidalRestriction

open Langlands.Cohomology.SupercuspidalExt (restriction HasCompactCoefficients)

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Let `H` be an open normal subgroup of a locally profinite, σ-compact group
`G` such that `H ∩ Z(G)` is compact and `Z(G) H` has finite index. Then the
restriction to `H` of an irreducible smooth complex representation whose
matrix coefficients are compactly supported modulo the center is a finite
direct sum of irreducible smooth representations of `H` with compactly
supported matrix coefficients. -/
def CompactModCenterRestrictionStatement (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [SigmaCompactSpace G] : Prop :=
  ∀ H : Subgroup G, H.Normal → IsOpen (H : Set G) →
    IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G) →
    (Subgroup.center G ⊔ H).FiniteIndex →
    ∀ π : SmoothRep.{0, 0, 0} ℂ G, π.IsIrreducible →
      HasCompactSmoothCoefficientsModCenter π.representation →
      ∃ (m : ℕ) (σ : Fin m → SmoothRep.{0, 0, 0} ℂ H),
        (∀ i, (σ i).IsIrreducible) ∧ (∀ i, HasCompactCoefficients (σ i)) ∧
          Nonempty ((restriction ℂ G H).obj π ≅ ⨁ σ)

section GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{0} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

local instance (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n

local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

/-- The subgroup `G° = {g ∈ GL_n(F) | det g ∈ O_F^×}`, written as the kernel of
`g ↦ ‖det g‖` for the canonical norm of `F`, which extends the `p`-adic
norm. -/
def unitDeterminantSubgroup (n : ℕ) : Subgroup (GeneralLinear n F.Carrier) :=
  letI := F.canonicalNormedField
  ((normHom : F.Carrier →*₀ ℝ).toMonoidHom.comp
    ((Units.coeHom F.Carrier).comp GeneralLinear.determinant)).ker

theorem mem_unitDeterminantSubgroup (n : ℕ) (g : GeneralLinear n F.Carrier) :
    g ∈ unitDeterminantSubgroup F n ↔
      F.canonicalNorm ((GeneralLinear.determinant g : F.Carrierˣ) : F.Carrier) = 1 :=
  Iff.rfl

/-- `G°` is normal: it is the kernel of a homomorphism. -/
theorem unitDeterminantSubgroup_normal (n : ℕ) : (unitDeterminantSubgroup F n).Normal :=
  MonoidHom.normal_ker _

/-- Bernstein–Zelevinsky 1976, 3.20: `G°` is open, `G° ∩ Z` is compact, and
`Z G°` has finite index in `GL_n(F)`. -/
def UnitDeterminantSubgroupStatement (n : ℕ) : Prop :=
  IsOpen (unitDeterminantSubgroup F n : Set (GeneralLinear n F.Carrier)) ∧
    IsCompact ((unitDeterminantSubgroup F n ⊓ Subgroup.center (GeneralLinear n F.Carrier) :
      Subgroup (GeneralLinear n F.Carrier)) : Set (GeneralLinear n F.Carrier)) ∧
    (Subgroup.center (GeneralLinear n F.Carrier) ⊔ unitDeterminantSubgroup F n).FiniteIndex

/-- Harish-Chandra's theorem, in the direction used here (Bernstein–Zelevinsky
1976, 3.21, (1) ⇒ (3)): a smooth complex representation of `GL_n(F)` that is
supercuspidal in the Library's sense has matrix coefficients that are
compactly supported modulo the center. -/
def GLHarishChandraStatement (n : ℕ) : Prop :=
  ∀ π : SmoothRep.{0, 0, 0} ℂ (GeneralLinear n F.Carrier),
    GeneralLinear.IsSupercuspidal π.representation →
      HasCompactSmoothCoefficientsModCenter π.representation

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Bernstein–Zelevinsky 1976, 3.21 and 3.26: the restriction to `G°` of an
irreducible supercuspidal representation of `GL_n(F)` is a finite direct sum of
irreducible smooth representations of `G°` with compactly supported matrix
coefficients. -/
def GLSupercuspidalRestrictionStatement (n : ℕ) : Prop :=
  ∀ π : SmoothRep.{0, 0, 0} ℂ (GeneralLinear n F.Carrier), π.IsIrreducible →
    GeneralLinear.IsSupercuspidal π.representation →
    ∃ (m : ℕ) (σ : Fin m → SmoothRep.{0, 0, 0} ℂ (unitDeterminantSubgroup F n)),
      (∀ i, (σ i).IsIrreducible) ∧ (∀ i, HasCompactCoefficients (σ i)) ∧
        Nonempty ((restriction ℂ (GeneralLinear n F.Carrier) (unitDeterminantSubgroup F n)).obj π ≅
          ⨁ σ)

/-- The `GL_n` restriction statement follows from the general one at `GL_n(F)`,
from Bernstein–Zelevinsky 3.20 and from Harish-Chandra's theorem. Total
disconnectedness and σ-compactness of `GL_n(F)` for the canonical topology are
taken as instance arguments because instance search does not find them. Both are
proved in the Library, but not as instances: σ-compactness by the public theorem
`PadicField.TopologicalData.generalLinearSigmaCompactSpace`, total disconnectedness
only by private theorems that other modules cannot use. -/
theorem glSupercuspidalRestriction_of_compactModCenter (n : ℕ)
    [TotallyDisconnectedSpace (GeneralLinear n F.Carrier)]
    [SigmaCompactSpace (GeneralLinear n F.Carrier)]
    (hG : CompactModCenterRestrictionStatement (GeneralLinear n F.Carrier))
    (hsub : UnitDeterminantSubgroupStatement F n) (hHC : GLHarishChandraStatement F n) :
    GLSupercuspidalRestrictionStatement F n := by
  intro π hπ hsc
  exact hG _ (unitDeterminantSubgroup_normal F n) hsub.1 hsub.2.1 hsub.2.2 π hπ (hHC π hsc)

/-- The three `GL_n` statements together. None is assumed to be true. -/
def GLSupercuspidalRestrictionStatements (n : ℕ) : Prop :=
  UnitDeterminantSubgroupStatement F n ∧ GLHarishChandraStatement F n ∧
    GLSupercuspidalRestrictionStatement F n

end GeneralLinearGroup

end Langlands.Cohomology.SupercuspidalRestriction
