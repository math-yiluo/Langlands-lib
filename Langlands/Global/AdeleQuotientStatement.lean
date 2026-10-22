import Langlands.Global.Adelic

/-!
# The additive adele quotient `𝔸_K / K`: statements

The principal adeles, the additive quotient `𝔸_K / K` with its quotient topology, and
the statements that `𝔸_K` is locally compact, that `K` is discrete and closed in `𝔸_K`,
and that `𝔸_K / K` is compact (Cassels, *Global fields*, §14; Weil, *Basic number
theory*, IV §2 Theorem 2). See `AdeleQuotientStatement.md`.
-/

noncomputable section

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- The principal adeles: the additive subgroup of `𝔸_K` that is the range of `diagonal`. -/
abbrev principalAdeles : AddSubgroup (Adeles K) :=
  NumberField.AdeleRing.principalSubgroup (NumberField.RingOfIntegers K) K

/-- The additive adele quotient `𝔸_K / K`, with the quotient topology. -/
abbrev AdeleQuotient := Adeles K ⧸ principalAdeles K

/-- The continuous additive quotient map `𝔸_K → 𝔸_K / K`. -/
def adeleQuotientMap : Adeles K →ₜ+ AdeleQuotient K where
  toAddMonoidHom := QuotientAddGroup.mk' (principalAdeles K)
  continuous_toFun := QuotientAddGroup.continuous_mk

/-- The adele ring `𝔸_K` is locally compact (Cassels §14, p.63). -/
def AdelesLocallyCompactStatement : Prop :=
  LocallyCompactSpace (Adeles K)

/-- The principal adeles form a discrete subgroup of `𝔸_K` (Cassels §14, Theorem, p.64),
and hence a closed one. -/
def PrincipalAdelesDiscreteStatement : Prop :=
  DiscreteTopology (principalAdeles K) ∧ IsClosed (principalAdeles K : Set (Adeles K))

/-- The additive adele quotient `𝔸_K / K` is compact (Cassels §14, Theorem, p.64). -/
def AdeleQuotientCompactStatement : Prop :=
  CompactSpace (AdeleQuotient K)

/-- For every number field `K`: `𝔸_K` is locally compact, `K` is discrete and closed in
`𝔸_K`, and `𝔸_K / K` is compact. -/
def AdeleQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    AdelesLocallyCompactStatement K ∧ PrincipalAdelesDiscreteStatement K ∧
      AdeleQuotientCompactStatement K

end Langlands.Global
