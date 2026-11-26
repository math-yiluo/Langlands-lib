import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Global.AdelicIwasawaHeight
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Reductive.Basic

/-! # Harish-Chandra's finiteness theorem on `V(𝔸)M'(F) \ G(𝔸)`

Harish-Chandra, *Automorphic forms on semisimple Lie groups* (1968), Chapter I, §2,
Theorem 1, in the adelic form of Borel–Jacquet §4.3 (i), and on the parabolic quotient
`V(𝔸)M'(F) \ G(𝔸)` as in Mœglin–Waldspurger I.2.17: the automorphic forms with a fixed
level at the finite places, a fixed finite set of types under the infinite part of the maximal
compact subgroup and a fixed annihilating ideal of finite codimension in the center of the
enveloping algebra span a finite-dimensional space.

The types are fixed by a finite-dimensional space `E` of functions on the infinite compact
subgroup `K_∞` containing every function `k ↦ f(g k)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme AdelicGroupPoints

/-- **Harish-Chandra's finiteness theorem** on `V(𝔸)M'(F) \ G(𝔸)` (Harish-Chandra 1968,
Chapter I, §2, Theorem 1; Borel–Jacquet §4.3 (i); Mœglin–Waldspurger I.2.17, p. 38). Let `G`
be a connected reductive group over a number field `F`, `q : Q → G` a parabolic subgroup with
geometric unipotent radical `iV : V → Q` and rational Levi subgroup `l' : M' → Q` complementary
to it, `K` a maximal compact subgroup of `G(𝔸)` with `Q(𝔸)K = G(𝔸)`, and `rho` a closed matrix
embedding. Fix an ideal `J` of finite codimension in the center of the complex enveloping
algebra, an open subgroup `L` of `G(𝔸_f)` and a finite-dimensional space `E` of functions on
the infinite compact subgroup `K_∞ = K ∩ G(F_∞)`. Then the functions `f` that are automorphic on
`V(𝔸)M'(F) \ G(𝔸)`, right invariant under `L`, whose infinite slices are annihilated by `J`, and
such that `k ↦ f(g k)` lies in `E` for every `g`, span a finite-dimensional space. -/
def ParabolicHarishChandraFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine Q.X.left]
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    IsIso (subgroupMultiplication l' iV) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact q K →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
    ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (L : Subgroup (FiniteAdelicGroupPoints F G)),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
    ∀ (E : Submodule ℂ (K.comap (ofInfinite F G).toMonoidHom → ℂ)), FiniteDimensional ℂ E →
      FiniteDimensional ℂ (Submodule.span ℂ {f : AdelicGroupPoints F G → ℂ |
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
            (K.comap (ofInfinite F G).toMonoidHom) rho f ∧
          (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, f (g * ofFinite F G b) = f g) ∧
          (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
            ∀ h : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G,
              plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G f b, h⟩ = 0) ∧
          ∀ g : AdelicGroupPoints F G,
            (fun k : K.comap (ofInfinite F G).toMonoidHom => f (g * ofInfinite F G k)) ∈ E})

end Langlands.Automorphic.GroupSchemeFunctions
