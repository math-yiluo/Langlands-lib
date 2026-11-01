import Langlands.AlgebraicGeometry.AlgClosedConnectedStatement
import Mathlib.Topology.JacobsonSpace

/-! # Connected schemes of locally finite type over an algebraically closed field -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

private lemma connectedSpace_of_openMap_closedFibres
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace Y] [JacobsonSpace Y]
    (p : X → Y) (hp : IsOpenMap p) (hs : Function.Surjective p)
    (hf : ∀ y : Y, IsClosed {y} → IsPreconnected (p ⁻¹' {y})) :
    ConnectedSpace X := by
  have : Nonempty X := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    obtain ⟨x, _⟩ := hs y
    exact ⟨x⟩
  refine connectedSpace_iff_univ.mpr ⟨Set.univ_nonempty, ?_⟩
  intro U V hU hV hcover hUne hVne
  obtain ⟨u, _, hu⟩ := hUne
  obtain ⟨v, _, hv⟩ := hVne
  have hcover' : Set.univ ⊆ p '' U ∪ p '' V := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    rcases hcover (Set.mem_univ x) with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  obtain ⟨y, _, hy⟩ := isPreconnected_univ (p '' U) (p '' V)
    (hp U hU) (hp V hV) hcover'
    ⟨p u, Set.mem_univ _, ⟨u, hu, rfl⟩⟩
    ⟨p v, Set.mem_univ _, ⟨v, hv, rfl⟩⟩
  obtain ⟨y, ⟨hyU, hyV⟩, hyclosed⟩ :=
    nonempty_inter_closedPoints ⟨y, hy⟩ ((hp U hU).inter (hp V hV)).isLocallyClosed
  obtain ⟨a, haU, ha⟩ := hyU
  obtain ⟨b, hbV, hb⟩ := hyV
  obtain ⟨z, _, hz⟩ := hf y hyclosed U V hU hV
    (fun z _ => hcover (Set.mem_univ z))
    ⟨a, ha, haU⟩ ⟨b, hb, hbV⟩
  exact ⟨z, Set.mem_univ _, hz⟩

private lemma connected_rational_fibre
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ f = 𝟙 _) :
    _root_.IsConnected ((pullback.fst f g) ⁻¹' Set.range e) := by
  let p := pullback.fst f g
  let s := pullback.snd f g
  let j : Spec (CommRingCat.of L) ⟶ pullback f g :=
    pullback.lift (g ≫ e) (𝟙 _) (by simp [Category.assoc, he])
  have hjp : j ≫ p = g ≫ e := pullback.lift_fst _ _ _
  have hjs : j ≫ s = 𝟙 _ := pullback.lift_snd _ _ _
  let l : Spec (CommRingCat.of L) ⟶ pullback p e :=
    pullback.lift j g hjp
  let d : pullback p e ⟶ Spec (CommRingCat.of L) :=
    pullback.fst p e ≫ s
  have hlp : l ≫ pullback.fst p e = j := pullback.lift_fst _ _ _
  have hlq : l ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  have hdg : d ≫ g = pullback.snd p e := by
    dsimp only [d, s, p]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, he, Category.comp_id]
  have hdj : d ≫ j = pullback.fst p e := by
    apply pullback.hom_ext
    · change (d ≫ j) ≫ p = pullback.fst p e ≫ p
      rw [Category.assoc, hjp, ← Category.assoc, hdg, pullback.condition]
    · change (d ≫ j) ≫ s = pullback.fst p e ≫ s
      rw [Category.assoc, hjs, Category.comp_id]
  let iso : pullback p e ≅ Spec (CommRingCat.of L) := {
    hom := d
    inv := l
    hom_inv_id := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, hlp, Category.id_comp] using hdj
      · simpa only [Category.assoc, hlq, Category.id_comp] using hdg
    inv_hom_id := by
      dsimp only [d]
      rw [← Category.assoc, hlp, hjs] }
  have : IsIso iso.hom := iso.isIso_hom
  have : ConnectedSpace ↥(pullback p e) :=
    iso.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  have h := isConnected_range (pullback.fst p e).continuous
  rwa [Scheme.Pullback.range_fst] at h

/-- Over an algebraically closed field, connectedness of a locally finite type
scheme persists after every field extension. -/
theorem algClosedConnected : AlgClosedConnectedStatement.{u} := by
  intro K _ _ X f _ _
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ g
  have : Surjective g := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  apply connectedSpace_of_openMap_closedFibres (pullback.fst f g)
    (pullback.fst f g).isOpenMap (pullback.fst f g).surjective
  intro x hx
  let e := pointOfClosedPoint f x hx
  have he : e ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
  have hrange : Set.range e = {x} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact Set.mem_singleton_iff.mpr (pointOfClosedPoint_apply f x hx a)
    · intro hy
      have hyx : y = x := hy
      subst y
      exact ⟨default, pointOfClosedPoint_apply f x hx default⟩
  rw [← hrange]
  exact (connected_rational_fibre f g e he).isPreconnected

end Langlands.AlgebraicGeometry
