import Langlands.GroupScheme.Rational.FundamentalRepresentations

/-! # Fundamental weights under an equivalence of based root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (p : SplitPinning G) (q : SplitPinning H)

/-- A based equivalence carries the integral dual bases of the two actual coroot lattices to each other. -/
def FundamentalWeightBasisTransportStatement (e : p.rootDatum.Equiv q.rootDatum)
    (hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (hp : p.rootDatum.corootSpan ℤ = ⊤) (hq : q.rootDatum.corootSpan ℤ = ⊤) : Prop :=
  ∀ a : p.base.support,
    e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hp a) =
      Langlands.RootDatum.fundamentalWeightBasis q.rootDatum q.base hq (e.indexEquiv.subtypeEquiv hb a)

/-- Evaluation at the corresponding simple coroots identifies the two integral fundamental weights. -/
theorem weightEquiv_fundamentalWeightBasis (e : p.rootDatum.Equiv q.rootDatum)
    (hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (hp : p.rootDatum.corootSpan ℤ = ⊤) (hq : q.rootDatum.corootSpan ℤ = ⊤) :
    p.FundamentalWeightBasisTransportStatement q e hb hp hq := by
  classical
  intro a
  let s := e.indexEquiv.subtypeEquiv hb
  apply (Langlands.RootDatum.fundamentalWeightBasis q.rootDatum q.base hq).repr.injective
  ext j
  obtain ⟨b, rfl⟩ := s.surjective j
  rw [Langlands.RootDatum.fundamentalWeightBasis_repr, Langlands.RootDatum.fundamentalWeightBasis_repr,
    Langlands.RootDatum.fundamentalWeightBasis_pairing]
  change q.rootDatum.coroot' (e.indexEquiv b)
    (e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hp a)) = _
  rw [e.coroot'_weightEquiv]
  change p.rootDatum.toLinearMap
    (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hp a)
    (p.rootDatum.coroot (b : p.rootIndex)) = _
  rw [Langlands.RootDatum.fundamentalWeightBasis_pairing, if_congr s.apply_eq_iff_eq rfl rfl]

end Langlands.GroupScheme.SplitPinning
