import Langlands.Representation.Category.DisjointConstituentCoproduct

/-! # Coproducts of spanning invariant subspaces with disjoint constituents -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {V : SmoothRep.{0, uG, uV} ℂ G}

/-- The cofan of the actual invariant-subspace inclusions. Its index need not
fit in the carrier universe. -/
def invariantSubspaceCofan (W : I → Subrepresentation V.representation) :
    Cofan (fun i => subrepresentation V (W i)) :=
  Cofan.mk V (fun i => subtype V (W i))

/-- Spanning and disjoint irreducible constituents make the actual invariant
subspaces a categorical coproduct, without any index-size hypothesis. -/
def invariantSubspaceCofanIsColimit
    (W : I → Subrepresentation V.representation)
    (hspan : (⨆ i, W i) = ⊤)
    (hW : ∀ i j, i ≠ j → ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D (subrepresentation V (W i)) →
        IsSubquotient D (subrepresentation V (W j)) → False) :
    IsColimit (invariantSubspaceCofan W) := by
  classical
  have hind := iSupIndep_of_no_common_irreducibleSubquotient W hW
  apply cofanIsColimitOfBijective
  constructor
  · exact hind.dfinsupp_lsum_injective
  · have hsurj : Function.Surjective
        (DirectSum.coeLinearMap (fun i => (W i).toSubmodule)) := by
      apply LinearMap.range_eq_top.mp
      rw [DirectSum.range_coeLinearMap,
        ← Langlands.Subrepresentation.toSubmodule_iSup, hspan]
      rfl
    exact hsurj

/-- The actual images of all legs of a coproduct span its vertex. -/
theorem iSup_range_cofan_eq_top
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A) (hs : IsColimit s) :
    (⨆ i, (hom (s.inj i)).range) = ⊤ := by
  let W : Subrepresentation s.pt.representation := ⨆ i, (hom (s.inj i)).range
  let q := mkQ s.pt W
  have hq : q = 0 := by
    apply hs.hom_ext
    rintro ⟨i⟩
    ext v
    change hom q (hom (s.inj i) v) = 0
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr
    exact (le_iSup (fun j => (hom (s.inj j)).range) i) ⟨v, rfl⟩
  apply top_unique
  intro v _
  apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
  exact congrArg (fun f => hom f v) hq

end Langlands.SmoothRep
