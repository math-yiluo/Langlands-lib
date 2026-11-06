import Langlands.WeilDeligne.DirectSum

/-! # Reindexing finite direct sums of Weil–Deligne pairs -/

noncomputable section

universe uK uG uV uι uκ

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}
  {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

/-- Reindexing a finite direct sum of pairs along an equivalence of index types is a
genuine pair equivalence: the coordinate of index `i` on the right is the coordinate
of index `e i` on the left. -/
def directSumReindexEquiv (e : ι ≃ κ) (X : κ → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (directSum X) (directSum fun i => X (e i)) where
  representationEquiv :=
    Representation.Equiv.mk (DirectSum.lequivCongrLeft K e.symm) fun g => by
      apply LinearMap.ext
      intro x
      apply DirectSum.ext
      intro i
      rfl
  comm_monodromy := by
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro i
    rfl

end Langlands.WeilDeligneRepresentation
