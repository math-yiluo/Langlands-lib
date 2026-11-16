import Langlands.AlgebraicGeometry.Picard.LocalRepresenterEtaleRelation
import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleCocycle

/-! # Equivariant universal bundle of a local presheaf representer -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LocalRepresenter

variable {S U : Scheme.{u}} (p : U ⟶ S) [Etale p]
    {F : (Over S)ᵒᵖ ⥤ Type v} {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)

/-- Related chart maps have the same coordinate on the original base. -/
theorem related_base {T : Scheme.{u}} {a b : T ⟶ M.left}
    (h : (etaleRelation p e).Related a b) :
    b ≫ (chart p (M := M)).hom = a ≫ (chart p (M := M)).hom := by
  change ∃ r : T ⟶ overlap p (M := M), r ≫ first p = a ∧ r ≫ second p e = b at h
  obtain ⟨r, rfl, rfl⟩ := h
  simp only [Category.assoc, first_base, second_base]

/-- Matching chart maps, with the test scheme viewed over their common base. -/
def relatedSecond {T : Scheme.{u}} (a b : T ⟶ M.left)
    (h : (etaleRelation p e).Related a b) :
    Over.mk (a ≫ (chart p (M := M)).hom) ⟶ chart p (M := M) :=
  Over.homMk b (related_base p e h)

/-- Related chart maps classify the same actual family on their common test. -/
theorem related_family {T : Scheme.{u}} (a b : T ⟶ M.left)
    (h : (etaleRelation p e).Related a b) :
    F.map (Over.homMk a rfl : Over.mk (a ≫ (chart p (M := M)).hom) ⟶
        chart p (M := M)).op (family p e) =
      F.map (relatedSecond p e a b h).op (family p e) := by
  change ∃ r : T ⟶ overlap p (M := M), r ≫ first p = a ∧ r ≫ second p e = b at h
  obtain ⟨r, ha, hb⟩ := h
  let r' : Over.mk (a ≫ (chart p (M := M)).hom) ⟶ overlapOverS p (M := M) :=
    Over.homMk r (by
      change r ≫ (overlapOverS p (M := M)).hom = a ≫ (chart p (M := M)).hom
      rw [← ha]
      rw [Category.assoc, first_base])
  have h1 : r' ≫ firstOver p = Over.homMk a rfl := by
    apply Over.OverMorphism.ext
    exact ha
  have h2 : r' ≫ secondOverS p e = relatedSecond p e a b ⟨r, ha, hb⟩ := by
    apply Over.OverMorphism.ext
    exact hb
  simpa only [h1, h2] using kernel_w p e r'

/-- Transition of the actual local universal bundle on a related pair. -/
def bundleTransport (L : PresheafLineBundle F) {T : Scheme.{u}}
    (a b : T ⟶ M.left) (h : (etaleRelation p e).Related a b) :
    (LineBundle.pullback a).obj (L.bundle (chart p (M := M)) (family p e)) ≅
      (LineBundle.pullback b).obj (L.bundle (chart p (M := M)) (family p e)) :=
  L.transition (T := Over.mk (a ≫ (chart p (M := M)).hom))
    (U := chart p (M := M)) (V := chart p (M := M))
    (Over.homMk a rfl) (relatedSecond p e a b h)
    (family p e) (family p e) (related_family p e a b h)

/-- Coherent transport of the local universal bundle across the actual
étale equivalence relation. -/
def equivariantBundle (L : PresheafLineBundle F) :
    EquivariantLineBundle (etaleRelation p e) where
  bundle := L.bundle (chart p (M := M)) (family p e)
  transport := bundleTransport p e L
  transport_self a h := by
    exact L.transition_self (T := Over.mk (a ≫ (chart p (M := M)).hom))
      (U := chart p (M := M)) (Over.homMk a rfl) (family p e)
  transport_trans {T} a b c hab hbc hac := by
    let T' : Over S := Over.mk (a ≫ (chart p (M := M)).hom)
    let b' : T' ⟶ chart p (M := M) := relatedSecond p e a b hab
    let c' : T' ⟶ chart p (M := M) := relatedSecond p e a c hac
    have hb : F.map b'.op (family p e) = F.map c'.op (family p e) :=
      (related_family p e a b hab).symm.trans (related_family p e a c hac)
    have hc : bundleTransport p e L b c hbc =
        L.transition b' c' (family p e) (family p e) hb := by
      exact L.transition_overMk (U := chart p (M := M)) (V := chart p (M := M))
        b c (family p e) (family p e) (b ≫ (chart p (M := M)).hom)
        (a ≫ (chart p (M := M)).hom) rfl (related_base p e hbc)
        (related_base p e hab) (related_base p e hac) (related_family p e b c hbc) hb
    change bundleTransport p e L a b hab ≪≫ bundleTransport p e L b c hbc = _
    rw [hc]
    exact L.transition_trans (T := T') (U := chart p (M := M))
      (V := chart p (M := M)) (W := chart p (M := M))
      (Over.homMk a rfl) b' c' (family p e) (family p e) (family p e)
      (related_family p e a b hab) hb
  transport_precompose k a b h h' := by
    let k' : Over.mk ((k ≫ a) ≫ (chart p (M := M)).hom) ⟶
        Over.mk (a ≫ (chart p (M := M)).hom) :=
      Over.homMk k (Category.assoc k a _).symm
    exact L.transition_precompose (T := Over.mk (a ≫ (chart p (M := M)).hom))
      (U := chart p (M := M)) (V := chart p (M := M))
      k' (Over.homMk a rfl)
      (relatedSecond p e a b h) (family p e) (family p e) (related_family p e a b h)

end Langlands.AlgebraicGeometry.Picard.LocalRepresenter
