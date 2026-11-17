import Langlands.GroupScheme.Reductive.SuppliedBorelFieldComparison
import Langlands.GroupScheme.Torus.EtalePermutationChartCoherence

/-! # The actual permutation atlas of a supplied Borel adjoint torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

namespace EtalePermutationAtlas

variable {S U : Scheme.{u}} {D : GroupScheme S} {I J : Type u}
  [Fintype I] [Fintype J]

/-- The actual transition between two split charts with the same direct source. -/
def normalizedTransition (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange f).obj D ≅ splitTorus U J) :
    splitTorus U I ≅ splitTorus U J := e.symm ≪≫ e'

/-- Normalized base change of a transition is the transition of the two
normalized restricted actual charts. -/
theorem normalizedTransition_baseChange {V : Scheme.{u}} (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange f).obj D ≅ splitTorus U J)
    (p : V ⟶ U) (r : V ⟶ S) (hp : p ≫ f = r) :
    splitTorus.coordinateBaseChangeGroupHom p (normalizedTransition f e e').hom =
      (restrictChart f e p r hp).inv ≫ (restrictChart f e' p r hp).hom := by
  simp only [normalizedTransition, splitTorus.coordinateBaseChangeGroupHom,
    restrictChart, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

variable {U' : Scheme.{u}}

/-- The actual transition on the scheme-theoretic overlap of two charts. -/
def overlapTransition (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J) :
    splitTorus (pullback f g) I ≅ splitTorus (pullback f g) J :=
  normalizedTransition (pullback.fst f g ≫ f)
    (restrictChart f e (pullback.fst f g) (pullback.fst f g ≫ f) rfl)
    (restrictChart g e' (pullback.snd f g) (pullback.fst f g ≫ f) pullback.condition.symm)

/-- Residue-fibre permutations extend to actual all-test permutations on
open overlap neighbourhoods, with the same prescribed permutation. -/
theorem locallyPermutes_of_residue_transition [DecidableEq I] [DecidableEq J]
    (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : ∀ w : (pullback f g : Scheme.{u}), ∃ σ : J ≃ I,
      splitTorus.coordinateBaseChangeGroupHom ((pullback f g : Scheme.{u}).fromSpecResidueField w)
        (overlapTransition f g e e').hom =
          (splitTorus.coordinatePermutationIso _ σ).hom) :
    LocallyPermutes f g e e' := by
  intro w
  obtain ⟨σ, hσ⟩ := H w
  obtain ⟨O, hw, hO⟩ := splitTorus.exists_open_coordinatePermutation_of_residue_eq
    (overlapTransition f g e e').hom σ w hσ
  refine ⟨O, hw, σ, ?_⟩
  dsimp only [overlapTransition] at hO
  rw [normalizedTransition_baseChange _ _ _ O.ι
    (O.ι ≫ pullback.fst f g ≫ f) rfl, restrictChart_trans, restrictChart_trans] at hO
  have hsq := congrArg (fun v =>
    (restrictChart f e (O.ι ≫ pullback.fst f g) (O.ι ≫ pullback.fst f g ≫ f)
      (by simp only [Category.assoc])).hom ≫ v) hO
  simp only [Iso.hom_inv_id_assoc] at hsq
  intro Z x l
  rw [hsq, Grp.comp_hom_hom, ← Category.assoc,
    splitTorus.coordinatePermutationIso_hom_points]

end EtalePermutationAtlas

namespace SuppliedBorelChart

variable {S U : Scheme.{u}} {T : CommGroupScheme S} {G B D : GroupScheme S}
  {j : B ⟶ G} {t : T.toGrp ⟶ B} (C C' : SuppliedBorelChart j t)
  (q : T.toGrp ⟶ D) (hq : RelativeRoot.IsFppfQuotient ((center G).comap (t ≫ j)) q)

/-- Restricting the actual Borel-open chart gives the direct affine-model
quotient chart at the composite map. -/
theorem quotientChart_restrict (a : U ⟶ C.space) (r : U ⟶ S) (ha : a ≫ C.map = r) :
    EtalePermutationAtlas.restrictChart C.map (C.quotientChart q hq) a r ha =
      C.affine.quotientChartOver C.adapted.rootBase q hq (a ≫ C.adapted.projection)
        r ((Category.assoc _ _ _).trans ha) :=
  EtalePermutationAtlas.restrictChart_trans C.affine.map
    (C.affine.model.adjointQuotientChart C.adapted.rootBase (C.affine.quotientMap q)
      (C.affine.quotientMap_isFppfQuotient q hq))
    C.adapted.projection C.map rfl a r ha

/-- The actual quotient charts attached to the supplied Borel permute their
simple-root coordinates locally on their actual overlap. -/
theorem quotientChart_locallyPermutes :
    EtalePermutationAtlas.LocallyPermutes C.map C'.map
      (C.quotientChart q hq) (C'.quotientChart q hq) := by
  classical
  apply EtalePermutationAtlas.locallyPermutes_of_residue_transition
  intro w
  let W : Scheme.{u} := pullback C.map C'.map
  let b := W.fromSpecResidueField w
  let a := b ≫ pullback.fst C.map C'.map
  let a' := b ≫ pullback.snd C.map C'.map
  let r := b ≫ pullback.fst C.map C'.map ≫ C.map
  have ha : a ≫ C.map = r := Category.assoc _ _ _
  have ha' : a' ≫ C'.map = r := by
    dsimp only [a', r]
    rw [Category.assoc, pullback.condition]
  refine ⟨(C.basedComparison C' a a' r ha ha').simpleRootEquiv, ?_⟩
  dsimp only [EtalePermutationAtlas.overlapTransition]
  rw [EtalePermutationAtlas.normalizedTransition_baseChange _ _ _ b r rfl,
    EtalePermutationAtlas.restrictChart_trans, EtalePermutationAtlas.restrictChart_trans,
    C.quotientChart_restrict, C'.quotientChart_restrict]
  exact C.quotientChartOver_field_transition C' q hq a a' r ha ha'

end SuppliedBorelChart

/-- A point-indexed small family of actual Borel-adapted supplied-torus charts,
with chosen points witnessing coverage. -/
structure SuppliedBorelAtlas {S : Scheme.{u}} {T : CommGroupScheme S}
    {G B : GroupScheme S} (j : B ⟶ G) (t : T.toGrp ⟶ B) where
  chart : S → SuppliedBorelChart j t
  point : ∀ s : S, (chart s).space
  image_point : ∀ s : S, (chart s).map (point s) = s

namespace SuppliedBorelAtlas

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G B : GroupScheme S}
  {j : B ⟶ G} {t : T.toGrp ⟶ B}

/-- Choose a Borel-adapted supplied-torus chart above each base point. -/
def ofData (hG : IsReductive G) (hj : IsRelativeBorelSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup (t ≫ j))
    (hmax : IsFibrewiseMaximalTorus (T := T) (t ≫ j)) : SuppliedBorelAtlas j t where
  chart s := (SuppliedBorelChart.exists_over j t hG hj hT ht hmax s).choose
  point s := (SuppliedBorelChart.exists_over j t hG hj hT ht hmax s).choose_spec.choose
  image_point s := (SuppliedBorelChart.exists_over j t hG hj hT ht hmax s).choose_spec.choose_spec

/-- The actual jointly surjective small etale family. -/
def cover (A : SuppliedBorelAtlas j t) : S.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers S (fun s => (A.chart s).space) (fun s => (A.chart s).map)
    (fun s => ⟨s, A.point s, A.image_point s⟩) (fun _ => inferInstance)

variable {D : GroupScheme S} (A : SuppliedBorelAtlas j t)
  (q : T.toGrp ⟶ D) (hq : RelativeRoot.IsFppfQuotient ((center G).comap (t ≫ j)) q)

include A q hq in
/-- The actual supplied quotient has an etale permutation atlas, indexed on
each chart by the simple roots of the actual supplied Borel. -/
theorem hasEtalePermutationAtlas : HasEtalePermutationAtlas D := by
  refine ⟨A.cover, (fun s => (A.chart s).adapted.rootBase.support),
    (fun _ => inferInstance), (fun s => (A.chart s).quotientChart q hq), ?_⟩
  intro s s'
  exact (A.chart s).quotientChart_locallyPermutes (A.chart s') q hq

end SuppliedBorelAtlas

end Langlands.GroupScheme
