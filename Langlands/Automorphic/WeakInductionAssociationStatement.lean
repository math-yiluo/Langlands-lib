import Langlands.Automorphic.AssociatedDeterminantTwistStatement
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement
import Langlands.WeilDeligne.InductionAlong
import Langlands.Weil.Representation.CharacterLine

/-!
# Weak automorphic induction and weak association of induced Weil representations

For a tower `F ⊆ E' ⊆ L` of number fields with `L / F` Galois and a Hecke character
`ξ` of `E'`, the representation `Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` of the
relative Weil group is weakly associated with every cuspidal class of `GL_n(𝔸_F)`
that is a weak automorphic induction of `ξ` in the sense of Harris (1998),
Definition 1.3(b). This is the step of Henniart (2000), §3.4, from Harris's
automorphic induction to the associated pairs `(S(X), Π(X))`. Proposition
definitions only.
-/

noncomputable section

universe u uV uP

namespace Langlands.ClassField.Global

open scoped NumberField
open Langlands.Global Langlands.Automorphic

namespace RelativeWeilGroup

section Induced

attribute [local instance] relativeGaloisTopology

/-- The representation `Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` of `W_{L/F}`: the
character `reciprocityCharacter c E' L ξ` of `W_{L/E'}`, on a line, induced along
the intermediate-field inclusion `W_{L/E'} → W_{L/F}`. -/
def inducedReciprocityRepresentation (c : FundamentalClass.ClassFamily.{u})
    (F E' L : Type u) [Field F] [NumberField F] [Field E'] [NumberField E'] [Field L]
    [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L] [IsScalarTower F E' L]
    [IsGalois F L] (h : FundamentalClass.Restriction c)
    (ξ : NumberField.IdeleClassGroup (𝓞 E') E' →ₜ* ℂˣ) :
    FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F L) :=
  haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  FiniteRepresentation.induceAlong (restrictionInclusion c F L E' h).toMonoidHom
    (restrictionInclusion_injective c F L E' h)
    (FiniteRepresentation.characterLine.{u, uV} (reciprocityCharacter c E' L ξ))

end Induced

/-- Henniart (2000), §3.4, from Harris (1998), Definition 1.3(b): at every arithmetic
class family `c`, for every tower `F ⊆ E' ⊆ L` of number fields with `L / F`
Galois, every Hecke character `ξ` of `E'` and every cuspidal class `π` of
`GL_{r+1}(𝔸_F)` that is a weak automorphic induction of `ξ`, the representation
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` is weakly associated with `π`. -/
def WeakInductionAssociationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (h : FundamentalClass.Restriction c)
    (F E' L : Type u) [Field F] [NumberField F] [Field E'] [NumberField E'] [Field L]
    [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L] [IsScalarTower F E' L]
    [IsGalois F L] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r) (ξ : HeckeCharacter E'),
    π.IsWeakAutomorphicInductionOf.{u, u, uP} ξ →
      IsWeaklyAssociatedClass.{u, max u uV, uP}
        (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ) π

end RelativeWeilGroup

end Langlands.ClassField.Global
