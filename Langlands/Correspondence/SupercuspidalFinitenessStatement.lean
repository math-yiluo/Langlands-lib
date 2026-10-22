import Langlands.Representation.Classification.SupercuspidalStrata

/-!
# Local finiteness for genuine supercuspidal isomorphism classes

Bernstein--Zelevinsky (1976), Corollary 4.15, page 41, and its compact-open
and bounded-fixed-level consequences. These are proposition definitions.
-/

namespace Langlands.Henniart

universe uF uV

open GeneralLinear

/-- Fixing the central character and a compact open subgroup leaves only
finitely many supercuspidal classes with a nonzero fixed vector. -/
def SupercuspidalCompactOpenFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ)
    (K : OpenSubgroup (GeneralLinear (n + 1) F)),
    IsCompact (K : Set (GeneralLinear (n + 1) F)) →
      Set.Finite (SupercuspidalClass.centralFixedStratum.{uF, uV} χ K.toSubgroup)

/-- Fixing the central character and bounding the first nonzero newvector
level leaves finitely many genuine supercuspidal classes. -/
def SupercuspidalBoundedLevelFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ) (b : ℕ),
    Set.Finite (SupercuspidalClass.centralLevelStratum.{uF, uV} χ b)

/-- The bounded-level assertion follows from the compact-open assertion
using the actual last-row congruence subgroups. -/
def SupercuspidalLevelFinitenessReductionStatement : Prop :=
  SupercuspidalCompactOpenFinitenessStatement.{uF, uV} →
    SupercuspidalBoundedLevelFinitenessStatement.{uF, uV}

/-- The local finiteness family; epsilon-conductor identification and
finite-level existence are not assumed in order to state it. -/
def SupercuspidalFinitenessStatement : Prop :=
  SupercuspidalCompactOpenFinitenessStatement.{uF, uV} ∧
    SupercuspidalBoundedLevelFinitenessStatement.{uF, uV} ∧
    SupercuspidalLevelFinitenessReductionStatement.{uF, uV}

end Langlands.Henniart
