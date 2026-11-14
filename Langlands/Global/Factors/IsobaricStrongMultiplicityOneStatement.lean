import Langlands.Global.Factors.IsobaricAutomorphicRepresentation

/-!
# Strong multiplicity one for isobaric automorphic representations of `GL_(r+1)`

Getz–Hahn (2024), Corollary 11.7.3, for irreducible automorphic operator subquotients
of `GL_(r+1)` over a number field. If two isobaric subquotients have isomorphic local
components at all finite places outside a finite set, they are equivalent as full
operator representations. Local agreement at a finite place `v` is read as: one
irreducible admissible representation of `GL_(r+1)(F_v)` embeds into both
restrictions to `GL_(r+1)(F_v)`. See the paired Markdown for the source, the treatment
of the infinite places and the scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open Automorphic (IrreducibleOperatorSubquotient)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance isobaricSMOGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Strong multiplicity one for isobaric representations** (Getz–Hahn 2024,
Corollary 11.7.3). Let `Q`, `Q'` be isobaric irreducible automorphic operator
subquotients of `GL_(r+1)` over a number field `F`. If at every finite place `v`
outside a finite set `S` some irreducible admissible representation of `GL_(r+1)(F_v)`
embeds into the restrictions of both `Q` and `Q'` to `GL_(r+1)(F_v)`, then `Q` and
`Q'` are equivalent as full operator representations. -/
def IsobaricStrongMultiplicityOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r),
    IrreducibleOperatorSubquotient.IsIsobaric.{u, uQ} Q →
    IrreducibleOperatorSubquotient.IsIsobaric.{u, uQ} Q' →
    ∀ S : Finset (FinitePlace F),
      (∀ v ∉ S, ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
        (∃ f : A.obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
          Function.Injective f.toLinearMap) ∧
        ∃ f : A.obj.representation.IntertwiningMap (Q'.subquotient.localRepresentation v),
          Function.Injective f.toLinearMap) →
      Nonempty (Q.Equivalence Q')

end Langlands.Global
