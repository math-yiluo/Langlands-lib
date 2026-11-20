import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatchingGluingStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization

/-! # Proof of gluing of matching families of pieces -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}

namespace LocalAlgebras

variable (F : LocalAlgebras c)

/-- The inverse image in the spectrum of the `i`-th local algebra of a full
domain contained in the `i`-th cover member. Its algebra is the closed-quotient
base change `F.baseChange i W h`. -/
def pieceDomain (i : Fin c.size) (W : Domain K R) (h : W.locus ⊆ (c.obj i).locus) :
    Domain K (F.algebra i) :=
  Domain.pullback (F.map i) ((c.obj i).relative W (Domain.inclusionOfSubset W (c.obj i) h))

theorem mem_pieceDomain_locus (i : Fin c.size) (W : Domain K R)
    (h : W.locus ⊆ (c.obj i).locus) (x : BanachSpectrum (F.algebra i)) :
    x ∈ (F.pieceDomain i W h).locus ↔
      (c.obj i).spectrumMap (BanachSpectrum.comap (F.map i).toBoundedRingHom x) ∈ W.locus := by
  change BanachSpectrum.comap (F.map i).toBoundedRingHom x ∈
    ((c.obj i).relative W (Domain.inclusionOfSubset W (c.obj i) h)).locus ↔ _
  rw [Domain.relative_locus_eq_preimage]
  rfl

/-- The original restriction between pieces as an arrow of inverse-image domains. -/
def pieceInclusion (i : Fin c.size) {E D : Domain K R} (hED : E.locus ⊆ D.locus)
    (hDi : D.locus ⊆ (c.obj i).locus) :
    F.pieceDomain i E (Set.Subset.trans hED hDi) ⟶ F.pieceDomain i D hDi :=
  ⟨F.restrict i hED hDi, F.restrict_localMap i hED hDi⟩

/-- A finite cover of an inverse-image piece domain by inverse-image piece domains. -/
def pieceCoverOf (i : Fin c.size) {D : Domain K R} (hD : D.locus ⊆ (c.obj i).locus)
    {n : ℕ} (G : Fin n → Domain K R) (hG : ∀ a, (G a).locus ⊆ D.locus)
    (hcov : ∀ x ∈ D.locus, ∃ a, x ∈ (G a).locus) :
    Domain.FiniteCover (F.pieceDomain i D hD) where
  size := n
  obj a := F.pieceDomain i (G a) (Set.Subset.trans (hG a) hD)
  map a := F.pieceInclusion i (hG a) hD
  covers x hx := by
    obtain ⟨a, ha⟩ := hcov _ ((F.mem_pieceDomain_locus i D hD x).1 hx)
    exact ⟨a, (F.mem_pieceDomain_locus i (G a) _ x).2 ha⟩

end LocalAlgebras

namespace PairTransitions

variable {F : LocalAlgebras c} (t : PairTransitions F)

theorem inter_subset_inter_left {V : Domain K R} (e : Domain.FiniteCover V) (a : Fin e.size)
    (i : Fin c.size) : ((e.obj a).inter (c.obj i)).locus ⊆ (V.inter (c.obj i)).locus :=
  inter_subset_inter (Domain.Inclusion.subset (e.map a)) i

/-- The cover of the `i`-th piece domain over `V` by the piece domains over the
members of a cover of `V`. -/
def pieceCover (V : Domain K R) (e : Domain.FiniteCover V) (i : Fin c.size) :
    Domain.FiniteCover (F.pieceDomain i (V.inter (c.obj i)) (inter_subset_member V i)) :=
  F.pieceCoverOf i (inter_subset_member V i) (fun a => (e.obj a).inter (c.obj i))
    (fun a => inter_subset_inter_left e a i) (fun x hx => by
      obtain ⟨a, ha⟩ := e.covers x hx.1
      exact ⟨a, ha, hx.2⟩)

/-- Matching families agreeing on pairwise intersections give compatible
components on the piece-domain cover. -/
theorem pieceCover_compatible (V : Domain K R) (e : Domain.FiniteCover V)
    (m : ∀ a, t.pieceMatching (e.obj a))
    (hm : ∀ a b, t.matchingRestrict (V' := (e.obj a).inter (e.obj b)) Set.inter_subset_left (m a) =
      t.matchingRestrict (V' := (e.obj a).inter (e.obj b)) Set.inter_subset_right (m b))
    (i : Fin c.size) :
    (pieceCover (F := F) V e i).AlgebraCompatible (fun a => (m a).val i) := by
  intro a b W f g
  have hab : (((e.obj a).inter (e.obj b)).inter (c.obj i)).locus ⊆
      ((e.obj a).inter (c.obj i)).locus := inter_subset_inter Set.inter_subset_left i
  have hba : (((e.obj a).inter (e.obj b)).inter (c.obj i)).locus ⊆
      ((e.obj b).inter (c.obj i)).locus := inter_subset_inter Set.inter_subset_right i
  have hW : W.locus ⊆ (F.pieceDomain i (((e.obj a).inter (e.obj b)).inter (c.obj i))
      (inter_subset_member _ i)).locus := by
    intro x hx
    have ha := (F.mem_pieceDomain_locus i _ _ x).1 (Domain.Inclusion.subset f hx)
    have hb := (F.mem_pieceDomain_locus i _ _ x).1 (Domain.Inclusion.subset g hx)
    exact (F.mem_pieceDomain_locus i _ _ x).2 ⟨⟨ha.1, hb.1⟩, ha.2⟩
  let k := Domain.inclusionOfSubset W _ hW
  have hf : f.restriction = k.restriction.comp
      (F.restrict i hab (inter_subset_member _ i)) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W
        (F.pieceDomain i ((e.obj a).inter (c.obj i)) (inter_subset_member _ i))) _ f
      ⟨k.restriction.comp (F.restrict i hab (inter_subset_member _ i)),
        (BoundedAlgHom.comp_assoc _ _ _).trans ((congrArg k.restriction.comp
          (F.restrict_localMap i hab (inter_subset_member _ i))).trans k.comp_baseMap)⟩)
  have hg : g.restriction = k.restriction.comp
      (F.restrict i hba (inter_subset_member _ i)) :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion W
        (F.pieceDomain i ((e.obj b).inter (c.obj i)) (inter_subset_member _ i))) _ g
      ⟨k.restriction.comp (F.restrict i hba (inter_subset_member _ i)),
        (BoundedAlgHom.comp_assoc _ _ _).trans ((congrArg k.restriction.comp
          (F.restrict_localMap i hba (inter_subset_member _ i))).trans k.comp_baseMap)⟩)
  calc f.restriction ((m a).val i)
      = k.restriction ((t.matchingRestrict (V' := (e.obj a).inter (e.obj b))
          Set.inter_subset_left (m a)).val i) := by rw [hf]; rfl
    _ = k.restriction ((t.matchingRestrict (V' := (e.obj a).inter (e.obj b))
          Set.inter_subset_right (m b)).val i) := by rw [hm a b]
    _ = g.restriction ((m b).val i) := by rw [hg]; rfl

end PairTransitions

open PairTransitions in
/-- Gluing of matching families of pieces along finite covers. -/
theorem pieceMatchingGluing : PieceMatchingGluingStatement.{u} := by
  intro K _ _ _ R c F t V e m hm
  choose x hx hxu using fun i => Domain.FiniteCover.algebra_existsUnique (pieceCover (F := F) V e i)
    (fun a => (m a).val i) (t.pieceCover_compatible V e m hm i)
  have hxa : ∀ i a, F.restrict i (inter_subset_inter_left e a i) (inter_subset_member V i)
      (x i) = (m a).val i := fun i a => congrFun (hx i) a
  have hmatch : t.IsMatching V x := by
    intro i j E hi hj
    have hEV : E.locus ⊆ V.locus := fun y hy => (hi hy).1
    have hi' : E.locus ⊆ (c.obj i).locus := Set.Subset.trans hi (inter_subset_member V i)
    have hj' : E.locus ⊆ (c.obj j).locus := Set.Subset.trans hj (inter_subset_member V j)
    apply Domain.FiniteCover.algebra_ext_of_restrict_eq (F.pieceCoverOf j hj'
      (fun a => E.inter (e.obj a)) (fun a => Set.inter_subset_left) (fun y hy => by
        obtain ⟨a, ha⟩ := e.covers y (hEV hy)
        exact ⟨a, hy, ha⟩))
    intro a
    have hEaE : (E.inter (e.obj a)).locus ⊆ E.locus := Set.inter_subset_left
    have hEai : (E.inter (e.obj a)).locus ⊆ ((e.obj a).inter (c.obj i)).locus :=
      fun y hy => ⟨hy.2, hi' hy.1⟩
    have hEaj : (E.inter (e.obj a)).locus ⊆ ((e.obj a).inter (c.obj j)).locus :=
      fun y hy => ⟨hy.2, hj' hy.1⟩
    have A := congrArg (fun q => q (F.restrict i hi (inter_subset_member V i) (x i)))
      (t.restrict_transition i j hEaE hi' hj')
    have B := congrArg (t.transition i j (E.inter (e.obj a)) (Set.Subset.trans hEaE hi')
      (Set.Subset.trans hEaE hj')) (F.restrict_restrict i hEaE hi (inter_subset_member V i) (x i))
    have C := congrArg (t.transition i j (E.inter (e.obj a)) (Set.Subset.trans hEaE hi')
      (Set.Subset.trans hEaE hj')) (F.restrict_restrict i hEai (inter_subset_inter_left e a i)
        (inter_subset_member V i) (x i)).symm
    have D' := congrArg (fun z => t.transition i j (E.inter (e.obj a))
      (Set.Subset.trans hEaE hi') (Set.Subset.trans hEaE hj')
        (F.restrict i hEai (inter_subset_member _ i) z)) (hxa i a)
    have E' := (m a).property i j (E.inter (e.obj a)) hEai hEaj
    have F₁ := F.restrict_restrict j hEaE hj (inter_subset_member V j) (x j)
    have G := (F.restrict_restrict j hEaj (inter_subset_inter_left e a j)
      (inter_subset_member V j) (x j)).symm
    have H := congrArg (F.restrict j hEaj (inter_subset_member _ j)) (hxa j a)
    exact (A.trans (B.trans (C.trans (D'.trans E')))).trans (F₁.trans (G.trans H)).symm
  refine ⟨⟨x, hmatch⟩, fun a => Subtype.ext (funext fun i => hxa i a), fun y hy => ?_⟩
  apply Subtype.ext
  funext i
  exact hxu i (y.val i) (funext fun a => congrArg (fun z : t.pieceMatching (e.obj a) => z.val i)
    (hy a))

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
