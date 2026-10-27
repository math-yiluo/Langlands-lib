import Langlands.Automorphic.AssociatedFactorStatement

/-! # Uniqueness for weak association

Henniart (2000), §2.2: a cuspidal class is weakly associated with at most one semisimple
representation of the relative Weil group `W_{E/F}` of an arithmetic fundamental class, by a
variant of the Chebotarev density theorem, and a representation of `W_{E/F}` is weakly
associated with at most one cuspidal class, by Jacquet--Shalika (1981), Theorem 4.2.
Proposition definitions only.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

universe u uV uW uP uQ

namespace RelativeWeilGroup

section WeakEquivalence

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- `S` and `S'` are weakly equivalent: at almost every finite place `v` of `F`, both are
unramified at `v` and match one common polynomial, so that `det(1 - X S(ι Fr))` and
`det(1 - X S'(ι Fr))` agree for every local map `ι` at every place of `E` above `v`. -/
def IsWeaklyEquivalent (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)) : Prop :=
  ∀ᶠ v in Filter.cofinite,
    ∃ P : Polynomial ℂ, IsUnramifiedMatchAt S v P ∧ IsUnramifiedMatchAt S' v P

theorem IsWeaklyEquivalent.symm
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)}
    (h : IsWeaklyEquivalent S S') : IsWeaklyEquivalent S' S :=
  h.mono fun _ ⟨P, hS, hS'⟩ => ⟨P, hS', hS⟩

/-- Two representations weakly associated with one spectral system are weakly
equivalent. -/
theorem IsWeaklyEquivalent.of_isWeaklyAssociated {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)}
    {s : SpectralSystem (FinitePlace F) n}
    (h : IsWeaklyAssociated S s) (h' : IsWeaklyAssociated S' s) :
    IsWeaklyEquivalent S S' := by
  filter_upwards [h.2.2, h'.2.2] with v hv hv'
  obtain ⟨hs, hm⟩ := hv
  obtain ⟨_, hm'⟩ := hv'
  exact ⟨s.eulerPolynomial v hs, hm, hm'⟩

/-- The matching polynomial at `v` is unique, since some place of `E` lies above `v`. -/
theorem IsUnramifiedMatchAt.eq {v : FinitePlace F} {P Q : Polynomial ℂ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (hP : IsUnramifiedMatchAt S v P) (hQ : IsUnramifiedMatchAt S v Q) : P = Q := by
  obtain ⟨w⟩ := finitePlacesAbove_nonempty (L := E) v
  obtain ⟨⟨e, ι, hι⟩, hP'⟩ := hP w
  exact (hP' e ι hι).2.symm.trans ((hQ w).2 e ι hι).2

/-- Two spectral systems weakly associated with one representation have equal Euler
polynomials at almost every finite place. -/
theorem IsWeaklyAssociated.eventually_eulerPolynomial_eq {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s t : SpectralSystem (FinitePlace F) n}
    (hs : IsWeaklyAssociated S s) (ht : IsWeaklyAssociated S t) :
    ∀ᶠ v in Filter.cofinite, ∃ (hsv : v ∉ s.exceptional) (htv : v ∉ t.exceptional),
      s.eulerPolynomial v hsv = t.eulerPolynomial v htv := by
  filter_upwards [hs.2.2, ht.2.2] with v hv hv'
  obtain ⟨hsv, hm⟩ := hv
  obtain ⟨htv, hm'⟩ := hv'
  exact ⟨hsv, htv, hm.eq hm'⟩

end WeakEquivalence

/-- The variant of the Chebotarev density theorem used in Henniart (2000), §2.2, for the
relative Weil group of an arithmetic fundamental class: two continuous semisimple
representations of `W_{E/F}` that are weakly equivalent are equivalent. -/
def WeakEquivalenceRigidityStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E]
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)),
    S.IsContinuous → S'.IsContinuous → S.IsSemisimple → S'.IsSemisimple →
    IsWeaklyEquivalent S S' → Nonempty (FiniteRepresentation.Equiv S S')

/-- Henniart (2000), §2.2, uniqueness of the Weil side, for cuspidal classes: two
semisimple representations of `W_{E/F}` weakly associated with the same actual cuspidal
class `π` of `GL_{r+1}` over `F` are equivalent. -/
def AssociatedRepresentationUniquenessStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (π : Automorphic.CuspidalOperatorRealization.IsoClass F r)
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)),
    S.IsSemisimple → S'.IsSemisimple →
    IsWeaklyAssociatedClass.{u, uV, uP} S π → IsWeaklyAssociatedClass.{u, uW, uQ} S' π →
    Nonempty (FiniteRepresentation.Equiv S S')

/-- Henniart (2000), §2.2, uniqueness of the automorphic side, for cuspidal classes (a
consequence of Jacquet--Shalika 1981, Theorem 4.2): a representation of `W_{E/F}`, for any
class family, is weakly associated with at most one actual cuspidal class of `GL_{r+1}`
over `F`. -/
def AssociatedClassUniquenessStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (π π' : Automorphic.CuspidalOperatorRealization.IsoClass F r),
    IsWeaklyAssociatedClass.{u, uV, uP} S π → IsWeaklyAssociatedClass.{u, uV, uQ} S π' →
    π = π'

/-- The uniqueness assertions of Henniart (2000), §2.2, at the relative level and for
cuspidal classes. -/
def AssociatedUniquenessStatement : Prop :=
  WeakEquivalenceRigidityStatement.{u, uV, uW} ∧
    AssociatedRepresentationUniquenessStatement.{u, uV, uW, uP, uQ} ∧
    AssociatedClassUniquenessStatement.{u, uV, uP, uQ}

end RelativeWeilGroup

end Langlands.ClassField.Global
