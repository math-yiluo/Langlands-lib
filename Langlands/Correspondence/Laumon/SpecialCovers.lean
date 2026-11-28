import Langlands.Correspondence.Laumon.TameCovers

/-!
# Special covers of the punctured line

Katz (1986), (1.3.1)–(1.3.3), pp. 74–76, calls a finite étale covering of `𝔾_m` *special* if it
is tame at `0` and its geometric monodromy group has a unique `p`-Sylow subgroup, and proves in
Main Theorem (1.4.1), p. 76, that restriction to the punctured formal neighbourhood of `∞` is an
equivalence from special coverings onto all finite étale coverings of that neighbourhood. This
module defines the geometric monodromy group of a finite étale cover of `𝔾_m` at a geometric
point and special covers relative to an end `e` (tame at the opposite end), and states the
equivalence for the punctured henselian end trait at `e`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

/-- The geometric monodromy group of a finite étale cover `E` of `𝔾_m` at the geometric point `t`
(Katz (1.2.2)): the image of the geometric fundamental group `gmGeometricSubgroup k t` in the
permutations of the fibre of `E` at `t`. -/
def gmGeometricMonodromyGroup {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ gmOpen k)
    (E : (gmOpen k : Scheme.{u}).FiniteEtale) :
    Subgroup (Equiv.Perm ((Scheme.FiniteEtale.fiber t).obj E)) :=
  (gmGeometricSubgroup k t).map
    (MulAction.toPermHom (Aut (Scheme.FiniteEtale.fiber t)) ((Scheme.FiniteEtale.fiber t).obj E))

/-- **Special covers** relative to the end `e` (Katz (1.3.1), with the roles of `0` and `∞`
given by `e.opposite` and `e`): the finite étale covers of `𝔾_m` that are tame at the opposite end
`e.opposite` and whose geometric monodromy group, at the point `gmEndPoint k e`, has a unique
Sylow `p`-subgroup, `p` the characteristic of `k`. -/
def specialCover (e : FourierEnd) : ObjectProperty (gmOpen k : Scheme.{u}).FiniteEtale :=
  fun E => IsTameCoverAt k e.opposite E ∧
    Subsingleton (Sylow (ringChar k) (gmGeometricMonodromyGroup k (gmEndPoint k e) E))

/-- **Special covers and covers of the punctured end** (Katz 1986, Main Theorem (1.4.1), p. 76,
in the henselian form of Laumon (2.2.2), p. 156). For a finite field `k` and an end `e`, pullback
along `puncturedEndToGm k e : η_e → 𝔾_m` is fully faithful on special covers relative to `e`,
and every finite étale cover of the punctured end trait `η_e` is isomorphic to the pullback of a
special cover. -/
def SpecialCoverEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (e : FourierEnd),
    (∀ E E' : (gmOpen k : Scheme.{u}).FiniteEtale, specialCover k e E → specialCover k e E' →
      Function.Bijective fun φ : E ⟶ E' =>
        (Scheme.FiniteEtale.pullback (puncturedEndToGm k e)).map φ) ∧
    ∀ D : (puncturedEnd k e).FiniteEtale, ∃ E : (gmOpen k : Scheme.{u}).FiniteEtale,
      specialCover k e E ∧ Nonempty ((Scheme.FiniteEtale.pullback (puncturedEndToGm k e)).obj E ≅ D)

end Langlands.Henniart.Laumon
