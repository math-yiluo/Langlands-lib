import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Source axioms for Renard's full module categories

Renard (9 July 2026), A.VI.3, printed p.264 / PDF270, with the source
AB5 and local finite-type conventions on printed p.263 / PDF269.
These are closed future theorem targets, with explicit family-size bounds.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RenardFullModuleAxiomStatements

universe uA uI uM

/-- Arbitrary-size directed subobject distributivity for all original additive
actions over an arbitrary possibly nonunital ring. -/
@[pp_with_univ]
def NonUnitalDirectedSubobjectDistributivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, uM} A
    Langlands.Renard.DirectedSubobjectSumsDistribute.{uI}
      (NonUnitalModuleCat.{uA, uM} A)

/-- Source AB5 for all original additive actions, with carrier size sufficient
for the required `uI`-indexed coproducts. -/
@[pp_with_univ]
def NonUnitalSourceAB5Statement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, max uI uM} A
    Langlands.Renard.SourceAB5.{uI}
      (NonUnitalModuleCat.{uA, max uI uM} A)

/-- Canonical local finite type, Renard's source AB6, for all original additive
actions at an arbitrary independent carrier size. -/
@[pp_with_univ]
def NonUnitalSourceAB6Statement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, uM} A
    Langlands.Renard.SourceAB6 (NonUnitalModuleCat.{uA, uM} A)

/-- Arbitrary-size directed subobject distributivity in the actual category
of unital modules over an arbitrary unital ring. -/
@[pp_with_univ]
def UnitalDirectedSubobjectDistributivityStatement : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{uM} A) := ModuleCat.abelian
    Langlands.Renard.DirectedSubobjectSumsDistribute.{uI} (ModuleCat.{uM} A)

/-- Source AB5 for actual unital modules, with carrier size sufficient for
the required `uI`-indexed coproducts. -/
@[pp_with_univ]
def UnitalSourceAB5Statement : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{max uI uM} A) := ModuleCat.abelian
    Langlands.Renard.SourceAB5.{uI} (ModuleCat.{max uI uM} A)

/-- Canonical local finite type, Renard's source AB6, for actual unital
modules at an arbitrary independent carrier size. -/
@[pp_with_univ]
def UnitalSourceAB6Statement : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{uM} A) := ModuleCat.abelian
    Langlands.Renard.SourceAB6 (ModuleCat.{uM} A)

/-- The six full-category targets, in nonunital then unital order. -/
@[pp_with_univ]
def FullModuleAxiomsStatement : Prop :=
  NonUnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} ∧
    NonUnitalSourceAB5Statement.{uA, uI, uM} ∧
    NonUnitalSourceAB6Statement.{uA, uM} ∧
    UnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} ∧
    UnitalSourceAB5Statement.{uA, uI, uM} ∧
    UnitalSourceAB6Statement.{uA, uM}

/-- The source Grothendieck reading is definitionally the same closed target;
it adds no generator hypothesis. -/
theorem nonUnitalSourceAB5Statement_iff_isSourceGrothendieck :
    NonUnitalSourceAB5Statement.{uA, uI, uM} ↔
      (∀ (A : Type uA) [NonUnitalRing A],
        letI := NonUnitalModuleCat.abelian.{uA, max uI uM} A
        Langlands.Renard.IsSourceGrothendieck.{uI}
          (NonUnitalModuleCat.{uA, max uI uM} A)) := Iff.rfl

/-- The source Grothendieck reading for unital modules is definitionally
the same closed target, with the same standard abelian structure. -/
theorem unitalSourceAB5Statement_iff_isSourceGrothendieck :
    UnitalSourceAB5Statement.{uA, uI, uM} ↔
      (∀ (A : Type uA) [Ring A],
        letI : CategoryTheory.Abelian (ModuleCat.{max uI uM} A) := ModuleCat.abelian
        Langlands.Renard.IsSourceGrothendieck.{uI} (ModuleCat.{max uI uM} A)) := Iff.rfl

end Langlands.Algebra.RenardFullModuleAxiomStatements
