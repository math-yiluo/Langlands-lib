import Langlands.GroupScheme.Reductive.PinningScalarCoherence
import Langlands.GroupScheme.Reductive.PinnedBorelBaseChange
import Langlands.GroupScheme.Reductive.PinnedDynamicTransport
import Langlands.GroupScheme.Reductive.PinnedAutomorphismLift

/-! # Actual pinned lifts along field automorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

private theorem ringEquiv_isAlgebraic {k K : Type u} [Field k] [Field K]
    (σ : k ≃+* K) :
    letI : Algebra k K := σ.toRingHom.toAlgebra
    Algebra.IsAlgebraic k K := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  constructor
  intro x
  obtain ⟨y, rfl⟩ := σ.surjective x
  exact isAlgebraic_algebraMap y

attribute [local instance] towerAffine

section RingEquiv
variable {k K : Type u} [Field k] [Field K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Extend the actual supplied pinning using a specified field ring equivalence. -/
def baseChangeAlong (σ : k ≃+* K) :
    SplitPinning ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj G) := by
  letI : Algebra k K := σ.toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic k K := ringEquiv_isAlgebraic σ
  exact p.baseChange (F := K)

/-- The full root-datum equivalence for the specified scalar map. -/
def baseChangeAlongRootDatumEquiv (σ : k ≃+* K) :
    p.rootDatum.Equiv (p.baseChangeAlong σ).rootDatum := by
  letI : Algebra k K := σ.toRingHom.toAlgebra
  exact p.baseChangeRootDatumEquiv (F := K)

theorem baseChangeAlong_simple_iff (σ : k ≃+* K) (a : p.rootIndex) :
    a ∈ (p.baseChangeAlong σ).base.support ↔ a ∈ p.base.support := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  change a ∈ p.baseChangeBase.support ↔ a ∈ p.base.support
  rw [baseChangeBase_support]

/-- The actual Borel comparison along this field ring equivalence. -/
def negativeBorelBaseChangeAlongIso (σ : k ≃+* K) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj
      p.negativeBorel ≅ (p.baseChangeAlong σ).negativeBorel := by
  letI : Algebra k K := σ.toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic k K := ringEquiv_isAlgebraic σ
  exact p.negativeBorelBaseChangeIso (K := K)

theorem negativeBorelBaseChangeAlongIso_hom_comp (σ : k ≃+* K) :
    (p.negativeBorelBaseChangeAlongIso σ).hom ≫
        (p.baseChangeAlong σ).negativeBorelHom =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
        p.negativeBorelHom := by
  let : Algebra k K := σ.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic k K := ringEquiv_isAlgebraic σ
  exact p.negativeBorelBaseChangeIso_hom_comp (K := K)

end RingEquiv

section Automorphism
variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (σ : k ≃+* k) (e : p.basedRootDatumAut)

/-- Correct the inverse canonical scalar-extension equivalence by the prescribed
based automorphism on the full integral root datum. -/
def semilinearRootDatumEquiv :
    (p.baseChangeAlong σ).rootDatum.Equiv p.rootDatum :=
  RootPairing.Equiv.comp e.val (p.baseChangeAlongRootDatumEquiv σ).symm

theorem semilinearRootDatumEquiv_simple_iff
    (a : (p.baseChangeAlong σ).rootIndex) :
    a ∈ (p.baseChangeAlong σ).base.support ↔
      (p.semilinearRootDatumEquiv σ e).indexEquiv a ∈ p.base.support := by
  change a ∈ (p.baseChangeAlong σ).base.support ↔ e.val.indexEquiv a ∈ p.base.support
  exact (p.baseChangeAlong_simple_iff σ a).trans (e.property a)

/-- An actual pinned isomorphism from the specified coefficient pullback back to p. -/
def semilinearPinnedIso : Iso (p.baseChangeAlong σ) p :=
  (p.baseChangeAlong σ).isoOfRootDatumEquiv p
    (p.semilinearRootDatumEquiv σ e) (p.semilinearRootDatumEquiv_simple_iff σ e)

/-- An actual compatible isomorphism of the chosen Borels. -/
def semilinearNegativeBorelIso :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj
      p.negativeBorel ≅ p.negativeBorel :=
  p.negativeBorelBaseChangeAlongIso σ ≪≫
    (p.semilinearPinnedIso σ e).negativeBorelIso

theorem semilinearNegativeBorelIso_hom_comp :
    (p.semilinearNegativeBorelIso σ e).hom ≫ p.negativeBorelHom =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
        p.negativeBorelHom ≫ (p.semilinearPinnedIso σ e).groupIso.hom := by
  change ((p.negativeBorelBaseChangeAlongIso σ).hom ≫
      (p.semilinearPinnedIso σ e).negativeBorelIso.hom) ≫ p.negativeBorelHom = _
  rw [Category.assoc, Iso.negativeBorelIso_hom_comp,
    ← Category.assoc, negativeBorelBaseChangeAlongIso_hom_comp]

theorem range_semilinear_negativeBorelHom :
    SubgroupFunctor.range
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
        p.negativeBorelHom ≫ (p.semilinearPinnedIso σ e).groupIso.hom) =
      SubgroupFunctor.range p.negativeBorelHom := by
  rw [← p.semilinearNegativeBorelIso_hom_comp σ e]
  exact SubgroupFunctor.range_iso_comp (p.semilinearNegativeBorelIso σ e) _

end Automorphism
end Langlands.GroupScheme.SplitPinning
