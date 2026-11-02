import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.Topology.Constructions.SumProd

/-! # Compatible-point maps and open charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Restriction along a commutative pair of squares maps compatible pairs. -/
def schemeCompatiblePairMap
    {U V W X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {F : U ⟶ W} {G : V ⟶ W}
    (a : U ⟶ X) (b : V ⟶ Y) (d : W ⟶ Z)
    (ha : F ≫ d = a ≫ f) (hb : G ≫ d = b ≫ g)
    (q : {q : RingPoint R U S × RingPoint R V S // q.1 ≫ F = q.2 ≫ G}) :
    {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} :=
  ⟨(q.1.1 ≫ a, q.1.2 ≫ b), by
    dsimp only [RingPoint] at q ⊢
    calc
      (q.1.1 ≫ a) ≫ f = (q.1.1 ≫ F) ≫ d := by
        simp only [Category.assoc, ← ha]
      _ = (q.1.2 ≫ G) ≫ d := congrArg (fun p => p ≫ d) q.2
      _ = (q.1.2 ≫ b) ≫ g := by simp only [Category.assoc, hb]⟩

/-- A monic common target chart detects compatibility. -/
theorem schemeCompatiblePair_iff
    {U V W X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {F : U ⟶ W} {G : V ⟶ W}
    (a : U ⟶ X) (b : V ⟶ Y) (d : W ⟶ Z) [Mono d]
    (ha : F ≫ d = a ≫ f) (hb : G ≫ d = b ≫ g)
    (q : RingPoint R U S × RingPoint R V S) :
    q.1 ≫ F = q.2 ≫ G ↔ (q.1 ≫ a) ≫ f = (q.2 ≫ b) ≫ g := by
  dsimp only [RingPoint] at q ⊢
  rw [← cancel_mono d]
  simp only [Category.assoc, ha, hb]

/-- Compatible-pair charts inherit openness from their two factors. -/
theorem isOpenEmbedding_schemeCompatiblePairMap
    {U V W X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {F : U ⟶ W} {G : V ⟶ W}
    [TopologicalSpace (RingPoint R U S)] [TopologicalSpace (RingPoint R V S)]
    [TopologicalSpace (RingPoint R X S)] [TopologicalSpace (RingPoint R Y S)]
    (a : U ⟶ X) (b : V ⟶ Y) (d : W ⟶ Z) [Mono d]
    (ha : F ≫ d = a ≫ f) (hb : G ≫ d = b ≫ g)
    (haOpen : @IsOpenEmbedding (RingPoint R U S) (RingPoint R X S)
      inferInstance inferInstance (fun p => p ≫ a))
    (hbOpen : @IsOpenEmbedding (RingPoint R V S) (RingPoint R Y S)
      inferInstance inferInstance (fun p => p ≫ b)) :
    IsOpenEmbedding (schemeCompatiblePairMap R S a b d ha hb) := by
  let e : RingPoint R U S × RingPoint R V S →
      RingPoint R X S × RingPoint R Y S :=
    Prod.map (fun p => (p ≫ a : RingPoint R X S))
      (fun p => (p ≫ b : RingPoint R Y S))
  have he : IsOpenEmbedding e := haOpen.prodMap hbOpen
  have hmaps : Set.MapsTo e {q | q.1 ≫ F = q.2 ≫ G}
      {q | q.1 ≫ f = q.2 ≫ g} :=
    fun q hq => (schemeCompatiblePair_iff R S a b d ha hb q).mp hq
  have hEmbedding : IsEmbedding (schemeCompatiblePairMap R S a b d ha hb) :=
    he.isEmbedding.restrict hmaps
  have hrange : Set.range (schemeCompatiblePairMap R S a b d ha hb) =
      Subtype.val ⁻¹' Set.range e := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, rfl⟩
    · rintro ⟨p, hp⟩
      have hcp : (p.1 ≫ a) ≫ f = (p.2 ≫ b) ≫ g := by
        change (e p).1 ≫ f = (e p).2 ≫ g
        rw [hp]
        exact q.property
      have hc : p.1 ≫ F = p.2 ≫ G :=
        (schemeCompatiblePair_iff R S a b d ha hb p).mpr hcp
      exact ⟨⟨p, hc⟩, Subtype.ext hp⟩
  exact ⟨hEmbedding, by rw [hrange]; exact he.isOpen_range.preimage continuous_subtype_val⟩

end Langlands.AlgebraicGeometry.PointTopology
