/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import all WeilConjectures.AlgebraicGeometry.PicardFiberRankClopen
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected.Clopen

/-! # A reference bundle has fixed rank near a base point

Source: Stacks Project, Tag 0BDP, first proof paragraph.
(blueprint: lem-sc-picard-reference-rank-neighbourhood).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Reuse the existing private rank API via a proof-only `import all`.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The residue-field fibre has a field of global functions, hence is connected. -/
private theorem fibre_connected {X S : Scheme.{u}} (f : X ⟶ S)
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf))) (s : S) :
    ConnectedSpace (pullback f (S.fromSpecResidueField s) : Scheme.{u}) := by
  let q := pullback.snd f (S.fromSpecResidueField s)
  obtain ⟨hu, he⟩ := Modules.tensorPullbackObjUnitToUnit_isIso q
  have := hu
  have := hO (S.fromSpecResidueField s)
  let c := SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom
  have : IsIso c := by
    dsimp only [c]
    rw [← he]
    infer_instance
  have : IsIso (c.val.app (Opposite.op ⊤)) :=
    (SheafOfModules.evaluation _ (Opposite.op ⊤)).map_isIso c
  have hb : Function.Bijective q.appTop.hom :=
    (ConcreteCategory.isIso_iff_bijective (c.val.app (Opposite.op ⊤))).mp inferInstance
  let e : S.residueField s ≃+* Γ(pullback f (S.fromSpecResidueField s), ⊤) :=
    (ΓSpecIso (S.residueField s)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective q.appTop.hom hb)
  have hn : Nonempty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) := by
    by_contra hn
    have : IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) :=
      not_nonempty_iff.mp hn
    exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))
  have := hn
  apply (connectedSpace_iff_isIdempotentElem _).mpr
  intro a ha
  have ha' : IsIdempotentElem (e.symm a) := by
    change e.symm a * e.symm a = e.symm a
    rw [← map_mul, ha]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp ha' with h | h
  · left
    simpa only [map_zero, RingEquiv.apply_symm_apply] using congrArg e h
  · right
    simpa only [map_one, RingEquiv.apply_symm_apply] using congrArg e h

/-- The universal structure-sheaf unit gives surjectivity and a neighbourhood on which
all base changes of the reference bundle have one rank. No direct image of a second
bundle and no derived complex occurs in this statement.
Source: Stacks Project, Tag 0BDP, first proof paragraph.
(blueprint: lem-sc-picard-reference-rank-neighbourhood).

Proof: Apply the structure-sheaf unit to Spec of each residue field and take global
sections. Its target is the field, so the fibre cannot be empty. A disconnected fibre
has a nontrivial idempotent global function, impossible in that field. Thus f is
surjective and its fibres are connected. Local trivializations give a locally constant
rank function on X, constant on every fibre. Choose the rank r of the fibre over s.
The rank-r fibre locus is clopen by picardFiberRank_clopen and contains s. Take its
open subscheme U. Tensor pullback has rank r exactly when the images of all source
points lie in the local rank-r locus. For a point of any X_T with T mapping to U,
the residue-field fibre over its image contains a point mapping to the same point of X,
by the range formula for pullback.fst. Since this fibre has rank r, that X-point lies
in the local rank-r locus. The criterion gives the asserted condition on X_T.
Empty T has an empty
pullback, where every rank condition holds. The argument also applies to r=0. -/
theorem exists_picardReferenceRankNeighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (s : S) :
    Surjective f ∧ ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (g ≫ U.ι))).obj E) r := by
  classical
  have hconnected (t : S) :
      ConnectedSpace (pullback f (S.fromSpecResidueField t) : Scheme.{u}) :=
    fibre_connected f hO t
  have hsurj : Surjective f := by
    constructor
    intro t
    have := hconnected t
    obtain ⟨y⟩ := (inferInstance : Nonempty
      (pullback f (S.fromSpecResidueField t) : Scheme.{u}))
    refine ⟨(pullback.fst f (S.fromSpecResidueField t)) y, ?_⟩
    rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
    exact fromSpecResidueField_apply _ _
  have := hconnected s
  obtain ⟨y⟩ := (inferInstance : Nonempty
    (pullback f (S.fromSpecResidueField s) : Scheme.{u}))
  obtain ⟨r, hyr⟩ := exists_localRank E ((pullback.fst f (S.fromSpecResidueField s)) y)
  have hfibre : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r := by
    rw [tensorPullback_rank_iff]
    have hc := (localRank_isClopen E r).preimage
      (pullback.fst f (S.fromSpecResidueField s)).continuous
    have heq := hc.eq_univ ⟨y, hyr⟩
    intro z
    exact heq.ge (Set.mem_univ z)
  let A : Set S := {t | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField t))).obj E) r}
  let U : S.Opens := ⟨A, (picardFiberRank_clopen f E r).2.isOpen⟩
  refine ⟨hsurj, U, hfibre, r, ?_⟩
  intro T g
  rw [tensorPullback_rank_iff]
  intro z
  let x := (pullback.fst f (g ≫ U.ι)) z
  let t := (g ≫ U.ι) ((pullback.snd f (g ≫ U.ι)) z)
  have ht : t ∈ U := (g ((pullback.snd f (g ≫ U.ι)) z)).property
  have hxt : f x = t := by
    rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
  have hxq : x ∈ Set.range (pullback.fst f (S.fromSpecResidueField t)) := by
    rw [Pullback.range_fst, range_fromSpecResidueField]
    exact hxt
  obtain ⟨z', hz'⟩ := hxq
  have hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField t))).obj E) r := ht
  have hx := (tensorPullback_rank_iff _ E r).mp hr z'
  rwa [hz'] at hx

end AlgebraicGeometry.Scheme
