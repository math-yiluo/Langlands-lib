import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviCartanCoverTransport
import Langlands.GroupScheme.Dynamic.OppositeCellPreimage
import Langlands.Representation.Jacquet.StandardGeneralizedJacquetLift

/-! # Literal Iwahori decompositions pulled back to a standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe uG uH u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type uH} [Group H] {G : Type uG} [Group G]
  (f : H →* G) (K M N Nbar : Subgroup G)

/-- The exact map from three pulled-back literal intersections to the
original ordered intersections. -/
def orderedIntersectionComapMap :
    ↥(K.comap f ⊓ Nbar.comap f) × ↥(K.comap f ⊓ M.comap f) × ↥(K.comap f ⊓ N.comap f) →
      ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) :=
  fun t => (⟨f t.1.val, t.1.property⟩,
    ⟨f t.2.1.val, t.2.1.property⟩, ⟨f t.2.2.val, t.2.2.property⟩)

/-- An injective embedding preserves the literal ordered decomposition
provided every factor of an image point lifts to the source. -/
theorem HasIwahoriIntersectionDecomposition.comap_of_factorLifts
    (hf : Function.Injective f) (hK : HasIwahoriIntersectionDecomposition K M N Nbar)
    (hlift : ∀ (x : H) (a b c : G), a ∈ Nbar → b ∈ M → c ∈ N →
      a * b * c = f x → ∃ a' b' c' : H, f a' = a ∧ f b' = b ∧ f c' = c) :
    HasIwahoriIntersectionDecomposition (K.comap f) (M.comap f) (N.comap f) (Nbar.comap f) := by
  constructor
  · intro a b hab
    have ht : orderedIntersectionComapMap f K M N Nbar a =
        orderedIntersectionComapMap f K M N Nbar b := by
      apply hK.1
      apply Subtype.ext
      have h := congrArg (fun k : K.comap f => f k.val) hab
      simpa only [orderedIntersectionProduct, orderedIntersectionComapMap, map_mul] using h
    apply Prod.ext
    · apply Subtype.ext
      exact hf (congrArg (fun t : ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) => t.1.val) ht)
    · apply Prod.ext
      · apply Subtype.ext
        exact hf (congrArg (fun t : ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) => t.2.1.val) ht)
      · apply Subtype.ext
        exact hf (congrArg (fun t : ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) => t.2.2.val) ht)
  · intro x
    obtain ⟨t, ht⟩ := hK.2 ⟨f x.val, x.property⟩
    have hprod : t.1.val * t.2.1.val * t.2.2.val = f x.val :=
      congrArg (fun k : K => k.val) ht
    obtain ⟨a, b, c, ha, hb, hc⟩ := hlift x.val t.1.val t.2.1.val t.2.2.val
      t.1.property.2 t.2.1.property.2 t.2.2.property.2 hprod
    have haK : f a ∈ K ⊓ Nbar := ha ▸ t.1.property
    have hbK : f b ∈ K ⊓ M := hb ▸ t.2.1.property
    have hcK : f c ∈ K ⊓ N := hc ▸ t.2.2.property
    refine ⟨(⟨a, haK⟩, ⟨b, hbK⟩, ⟨c, hcK⟩), Subtype.ext (hf ?_)⟩
    simpa only [orderedIntersectionProduct, map_mul, ha, hb, hc] using hprod

end Groups

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] Langlands.HarishChandraSchwartz.rationalWeightsIsAffine
  Langlands.HarishChandraSchwartz.rationalWeightsTopology
  Langlands.HarishChandraSchwartz.rationalWeightsTopologicalGroup

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance iwahoriLeviTransportAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_isAffineHom i ν J
local instance iwahoriLeviTransportFiniteType :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_locallyOfFiniteType i ν J
local instance iwahoriLeviTransportAffine : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Pull the ambient standard Iwahori decomposition back to the canonical
Levi scheme for a nested simple-root subset, at the same subgroup preimage. -/
theorem hasIwahoriIntersectionDecomposition_leviScheme
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {R : Set (characterLattice S)} (hRJ : R ⊆ J)
    {K : Subgroup (rationalPoints G)}
    (hK : HasIwahoriIntersectionDecomposition K (standardLeviPoints i ν R)
      (standardUnipotentPoints i ν R) (standardOppositeUnipotentPoints i ν R)) :
    HasIwahoriIntersectionDecomposition
      (Langlands.HarishChandraSchwartz.leviSchemeCompact K i ν J)
      (standardLeviPoints (Standard.leviTorusHom i ν J) ν R)
      (standardUnipotentPoints (Standard.leviTorusHom i ν J) ν R)
      (standardOppositeUnipotentPoints (Standard.leviTorusHom i ν J) ν R) := by
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  let iL := Standard.leviTorusHom i ν J
  have hL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := Langlands.HarishChandraSchwartz.isGenericCocharacter_leviTorusHom (J := J) hν
  have hsimple := Langlands.HarishChandraSchwartz.simpleRelativeRoots_leviScheme i ν J hG hi hν hJ
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).1
  have hζL : IsStandardCocharacter iL ν R ζ := by
    refine ⟨?_, hζ.2.1, fun α hα hαR => hζ.2.2 α (hJ ?_) hαR⟩
    · rw [hsimple]
      exact hRJ
    · exact hsimple ▸ hα
  have hχ : (CommGroupScheme.groupHom ζ ≫ iL) ≫ j = CommGroupScheme.groupHom ζ ≫ i := by
    rw [Category.assoc, Standard.leviTorusHom_comp]
  have hχop : Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ iL) ≫ j =
      Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i) := by
    simpa only [Dynamic.inverseCocharacter, Dynamic.oppositeCocharacter, Category.assoc] using
      congrArg (fun x => CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ x) hχ
  obtain ⟨-, hM, hN⟩ := (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).2 ζ hζ
  obtain ⟨-, hML, hNL⟩ := (standardCocharacter F L hL S iL hiL ν hνL R hζL.1).2 ζ hζL
  have hbar := Langlands.Jacquet.standardOppositeUnipotentPoints_eq_dynamic i ν hG hi hν hζ
  have hbarL := Langlands.Jacquet.standardOppositeUnipotentPoints_eq_dynamic iL ν hL hiL hνL hζL
  have hMc : standardLeviPoints iL ν R =
      (standardLeviPoints i ν R).comap (rationalPoints.map j) := by
    rw [standardLeviPoints, standardLeviPoints, hML, hM]
    have hc := Dynamic.centralizer_eq_comap_of_isClosedSubgroup
      (CommGroupScheme.groupHom ζ ≫ iL) j (Standard.isClosedSubgroup_leviHom i ν J)
    rw [hχ] at hc
    rw [hc]
    rfl
  have hNc : standardUnipotentPoints iL ν R =
      (standardUnipotentPoints i ν R).comap (rationalPoints.map j) := by
    rw [standardUnipotentPoints, standardUnipotentPoints, hNL, hN]
    have hc := Dynamic.unipotent_eq_comap_of_isClosedSubgroup
      (CommGroupScheme.groupHom ζ ≫ iL) j (Standard.isClosedSubgroup_leviHom i ν J)
    rw [hχ] at hc
    rw [hc]
    rfl
  have hbarc : standardOppositeUnipotentPoints iL ν R =
      (standardOppositeUnipotentPoints i ν R).comap (rationalPoints.map j) := by
    rw [hbarL, hbar]
    have hc := Dynamic.unipotent_eq_comap_of_isClosedSubgroup
      (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ iL)) j
      (Standard.isClosedSubgroup_leviHom i ν J)
    rw [hχop] at hc
    rw [hc]
    rfl
  rw [hMc, hNc, hbarc]
  apply HasIwahoriIntersectionDecomposition.comap_of_factorLifts (rationalPoints.map j)
    K (standardLeviPoints i ν R) (standardUnipotentPoints i ν R)
    (standardOppositeUnipotentPoints i ν R)
    (Langlands.HarishChandraSchwartz.map_leviHom_injective) hK
  intro x a b c ha hb hc hprod
  have ha' : a ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ ((CommGroupScheme.groupHom ζ ≫ iL) ≫ j))).carrier _ := by
    rw [hχ]
    change a ∈ (Dynamic.unipotent (Dynamic.inverseCocharacter
      (CommGroupScheme.groupHom ζ ≫ i))).carrier _
    rw [← hbar]
    exact ha
  have hb' : b ∈ (Dynamic.centralizer ((CommGroupScheme.groupHom ζ ≫ iL) ≫ j)).carrier _ := by
    simpa only [hχ, ← hM] using hb
  have hc' : c ∈ (Dynamic.unipotent ((CommGroupScheme.groupHom ζ ≫ iL) ≫ j)).carrier _ := by
    simpa only [hχ, ← hN] using hc
  obtain ⟨a', b', c', -, -, -, ha', hb', hc', -⟩ := Dynamic.exists_triple_factors_of_isClosedSubgroup
    (CommGroupScheme.groupHom ζ ≫ iL) j (Standard.isClosedSubgroup_leviHom i ν J)
    x a b c ha' hb' hc' (by simpa only [rationalPoints.map_apply, mul_assoc] using hprod)
  exact ⟨a', b', c', ha', hb', hc'⟩

end Rational

end Langlands.BruhatTits.SpecialCompact
