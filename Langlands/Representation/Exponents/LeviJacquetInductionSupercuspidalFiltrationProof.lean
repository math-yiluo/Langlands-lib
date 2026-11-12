import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationStatement
import Langlands.Representation.Exponents.SupercuspidalIndexComparison
import Langlands.Representation.Exponents.RepresentedSupercuspidalityTransport
import Langlands.Representation.Geometric.DegenerateJacquetPieces
import Langlands.Representation.Filtration.GluedAtObject
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # Renard VI.5.3 (iii) for represented parabolics

The filtration of `r_Q^G i_P^G ρ` for a supercuspidal `ρ` along conjugate Levis is obtained
from the represented geometric lemma: the pieces with a proper source intersection vanish,
the remaining pieces are the conjugates of `ρ`, and they are indexed by the double cosets
containing an element conjugating `L` onto `M`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supercuspidalFiltrationAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- For isomorphic outer Levis and a full source intersection, the inverse of the recovered
Levi conjugacy is an isomorphism `L ≅ M` given by conjugation by `z`. -/
def fullTargetConjugacy (E : M ≅ L) (h : IsIso D.p') :
    {ψ : L ≅ M // ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso z).hom} :=
  haveI := h
  haveI := D.isIso_q'_of_isIso_p'_of_iso E
  ⟨D.fullLeviConjugacy.val.symm, by
    have h := congrArg
      (fun f : M ⟶ G => D.fullLeviConjugacy.val.inv ≫ f ≫ (G.innerIso z).hom)
      D.fullLeviConjugacy.property
    simpa only [Iso.symm_hom, innerIso_inv_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using h.symm⟩

/-- The topological-group isomorphism `L(F) ≃ M(F)` inverse to the recovered Levi points
equivalence. -/
def fullTargetPointsEquiv (E : M ≅ L) (h : IsIso D.p') :
    letI := leviPointTopology lQ hlQ
    letI := leviPointTopology l hl
    rationalPoints L ≃ₜ* rationalPoints M :=
  letI := leviPointTopology lQ hlQ
  letI := leviPointTopology l hl
  haveI := h
  haveI := D.isIso_q'_of_isIso_p'_of_iso E
  D.fullLeviPointsEquiv.symm

omit [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The isomorphism `fullTargetPointsEquiv` is the point map of `fullTargetConjugacy`. -/
theorem fullTargetPointsEquiv_apply (E : M ≅ L) (h : IsIso D.p') (x : rationalPoints L) :
    letI := leviPointTopology lQ hlQ
    letI := leviPointTopology l hl
    D.fullTargetPointsEquiv E h x =
      rationalPoints.map (D.fullTargetConjugacy E h).val.hom x := by
  let := leviPointTopology lQ hlQ
  let := leviPointTopology l hl
  have := h
  have := D.isIso_q'_of_isIso_p'_of_iso E
  apply D.fullLeviPointsEquiv.injective
  change D.fullLeviPointsEquiv (D.fullLeviPointsEquiv.symm x) =
    D.fullLeviPointsEquiv (rationalPoints.map D.fullLeviConjugacy.val.inv x)
  rw [ContinuousMulEquiv.apply_symm_apply, fullLeviPointsEquiv_apply, ← pointMap_comp_apply,
    Iso.inv_hom_id]
  rfl

/-- A full geometric piece is the pullback of the inducing representation along
`fullTargetPointsEquiv`. -/
def fullTargetPieceEquiv (E : M ≅ L) (h : IsIso D.p')
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    (D.pieceFunctor.obj σ).ρ.Equiv
      (SmoothRep.pullback (D.fullTargetPointsEquiv E h) σ).representation := by
  have := h
  have := D.isIso_q'_of_isIso_p'_of_iso E
  exact D.fullPieceEquiv σ

end GeometricLemmaIntersectionDatum

/-- Renard VI.5.3 (iii) for represented parabolics, deduced from the represented geometric
lemma. -/
theorem leviJacquetInductionSupercuspidalFiltration_of_geometricLemma
    (hGeom : RepresentedGeometricLemmaStatement.{u, v}) :
    LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hconj
  obtain ⟨g, E, -⟩ := hconj
  have := hG.isAffineHom
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro ρ hρ
  obtain ⟨m₀, c₀, z₀, hz₀, D, hglue⟩ :=
    hGeom k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hzero : ∀ i, ¬ IsIso (D i).p' → Subsingleton ((D i).pieceFunctor.obj ρ) := fun i hi =>
    (D i).subsingleton_pieceFunctor_obj ρ
      (hρ _ _ _ (D i).p' (D i).l' (D i).r' (D i).hp' (D i).hl' (D i).hr' (D i).hmul' hi)
  obtain ⟨m, e, s, hs⟩ :=
    hglue.exists_selected_filtration ρ (fun i => IsIso (D i).p') hzero
  have hsc : ∀ j : Fin m, IsSupercuspidal
      (SmoothRep.pullback ((D (e j).1).fullTargetPointsEquiv E (e j).2) ρ) := fun j =>
    isSupercuspidal_pullback_of_iso _ _ ((D (e j).1).fullTargetPointsEquiv_apply E (e j).2) ρ hρ
  have hgr : ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
      (SmoothRep.pullback ((D (e j).1).fullTargetPointsEquiv E (e j).2) ρ).representation) :=
    fun j => by
      obtain ⟨f⟩ := hs j
      exact ⟨f.trans ((D (e j).1).fullTargetPieceEquiv E (e j).2 ρ)⟩
  refine ⟨⟨m, e.trans (fullIndexEquiv parabolicDynamic hG E c₀ z₀ hz₀ D),
    fun j => z₀ (e j).1, fun j => ((D (e j).1).fullTargetConjugacy E (e j).2).1,
    fun j => (D (e j).1).fullTargetPointsEquiv E (e j).2, fun j => hz₀ (e j).1,
    fun j => ((D (e j).1).fullTargetConjugacy E (e j).2).2,
    fun j x => (D (e j).1).fullTargetPointsEquiv_apply E (e j).2 x, s, hgr⟩, ?_⟩
  exact isSupercuspidal_of_filtration s _ hsc hgr

/-- Renard VI.5.3 (iii) for represented parabolics: for a supercuspidal `ρ` of `M(F)` and
conjugate Levis, `r_Q i_P ρ` is filtered by the conjugates of `ρ` indexed by the double
cosets conjugating `L` onto `M`, and it is supercuspidal. -/
theorem leviJacquetInductionSupercuspidalFiltration :
    LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v} :=
  leviJacquetInductionSupercuspidalFiltration_of_geometricLemma representedGeometricLemma

end Langlands.Aubert.General.RepresentedParabolic
