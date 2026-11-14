import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Automorphic.IrreducibleOperatorSubquotient

/-!
# Cuspidal support of automorphic representations of `GL_n`, at the finite places

Langlands' theorem that every automorphic representation is a constituent of a
representation induced from cuspidal data (Langlands 1979, Proposition 2;
Getz–Hahn 2024, Theorem 10.7.1, second half), and the uniqueness of those data
(Getz–Hahn 2024, Corollary 10.7.3, from Jacquet–Shalika 1981 II, Theorem (4.4)),
for `GL_(r+1)` over a number field and read at the finite places.

`IsFiniteInducedConstituent hm P h Q` says that an irreducible automorphic
operator subquotient `Q` of `GL_(r+1)` is a constituent, at the finite places, of
the representation normalized-induced from the cuspidal realizations `T i` of
`GL_(m i + 1)`: at every finite place `v` some irreducible admissible subquotient
`A_v` of `i(π_(1,v), …, π_(k,v))`, spherical for `v` outside a finite set, embeds
into the restriction of `Q` to `GL_(r+1)(F_v)`. See the paired Markdown for the
sources and scope.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient PositiveRankCuspidalClass)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject sphericalSubgroup IsSubquotientOf)

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance cuspidalSupportGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Constituent of a cuspidally induced representation, at the finite places.**
Let `T i` (`i < k`) be actual cuspidal realizations of `GL_(m i + 1)` over a number
field `F`, with `∑ (m i + 1) = r + 1`, and `P i` spectral presentations of them
whose finite local components are irreducible and admissible. An irreducible
automorphic operator subquotient `Q` of `GL_(r+1)` is a *finite induced
constituent* of these data if there are, for every finite place `v`, an irreducible
admissible representation `A v` of `GL_(r+1)(F_v)` and a finite set `S` of finite
places such that

* `A v` is a subquotient of the normalized induced representation
  `i(π_(1,v), …, π_(k,v))` from the standard upper block parabolic, for every `v`;
* `A v` has a nonzero `GL_(r+1)(O_v)`-fixed vector for every `v ∉ S`;
* `A v` embeds into the restriction of `Q` to `GL_(r+1)(F_v)`, for every `v`. -/
def IsFiniteInducedConstituent {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r k : ℕ} {m : Fin k → ℕ}
    (hm : ∑ i, (m i + 1) = r + 1) {T : ∀ i, CuspidalOperatorRealization F (m i)}
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  ∃ (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (S : Finset (FinitePlace F)),
    (∀ v : FinitePlace F,
      IsSubquotientOf
        ((padicField v).canonicalNormalizedProductInduced
          ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
          (fun i => (((P i).localComponent v).padicObject
            (h i v).1 (h i v).2).obj.representation))
        (A v).obj.representation) ∧
    (∀ v ∉ S,
      fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥) ∧
    ∀ v : FinitePlace F,
      ∃ f : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap

/-- **Every automorphic representation has a cuspidal support** (Langlands 1979,
Proposition 2, "only if"; Getz–Hahn 2024, Theorem 10.7.1, second half), at the
finite places. For every irreducible automorphic operator subquotient `Q` of
`GL_(r+1)` over a number field `F` there are `k`, ranks `m i + 1` with
`∑ (m i + 1) = r + 1`, actual cuspidal realizations `T i` of `GL_(m i + 1)` and
spectral presentations `P i` of them, with factors in the form-space universe and
irreducible admissible finite local components, such that `Q` is a finite induced
constituent of these data. -/
def CuspidalSupportExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (Q : IrreducibleOperatorSubquotient F r),
    ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
      (T : ∀ i, CuspidalOperatorRealization F (m i))
      (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i))
      (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
      IsFiniteInducedConstituent hm P h Q

/-- **Uniqueness of the cuspidal support** (Getz–Hahn 2024, Corollary 10.7.3, from
Jacquet–Shalika 1981 II, Theorem (4.4)), at the finite places. If an irreducible
automorphic operator subquotient `Q` of `GL_(r+1)` over a number field is a finite
induced constituent of cuspidal data `(T i)_(i < k)` and of cuspidal data
`(T' j)_(j < k')`, then there is a bijection `e : Fin k ≃ Fin k'` with
`m' (e i) = m i` and `T' (e i)` equivalent to `T i`, as an equality of
positive-rank cuspidal classes. -/
def CuspidalSupportUniquenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k k' : ℕ) (m : Fin k → ℕ) (m' : Fin k' → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1) (hm' : ∑ j, (m' j + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (T' : ∀ j, CuspidalOperatorRealization F (m' j))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (P' : ∀ j, CuspidalSpectralPresentation.{u, uQ} (T' j))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (h' : ∀ j, HasIrreducibleAdmissibleComponents (P' j))
    (Q : IrreducibleOperatorSubquotient F r),
    IsFiniteInducedConstituent hm P h Q →
    IsFiniteInducedConstituent hm' P' h' Q →
    ∃ e : Fin k ≃ Fin k', ∀ i,
      (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F) =
        ⟨m' (e i), (T' (e i)).isoClass⟩

end Langlands.Global
