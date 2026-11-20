import Langlands.AlgebraicGeometry.AffineChartPoints
import Langlands.GroupScheme.HomScheme.AdicInfinitesimalSteps
import Langlands.GroupScheme.HomScheme.AdicTorusSourceLift
import Langlands.GroupScheme.Torus.MultiplicativeTypeNilpotentHom
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # A common actual source for a compatible adic family of closed tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor
open HomScheme.Adic (System transitionRingHom transitionRingHom_surjective transitionRingHom_ker_sq)

private theorem exists_iso_of_reduction {S S₀ : Scheme.{u}} {P Q : GroupScheme S}
    (b : S₀ ⟶ S) [IsClosedImmersion b] [Surjective b]
    (hP : RelativeTorus.IsTorus P) (hQ : RelativeTorus.IsTorus Q)
    (e : (baseChange b).obj P ≅ (baseChange b).obj Q) :
    ∃ d : P ≅ Q, (baseChange b).map d.hom = e.hom := by
  let B := baseChange b
  let hP' := hP.isMultiplicativeType
  let hQ' := hQ.isMultiplicativeType
  obtain ⟨f, hf⟩ := (hP'.baseChange_hom_bijective_of_surjective_closedImmersion hQ' b).surjective e.hom
  obtain ⟨g, hg⟩ := (hQ'.baseChange_hom_bijective_of_surjective_closedImmersion hP' b).surjective e.inv
  change B.map f = e.hom at hf
  change B.map g = e.inv at hg
  have hgf : f ≫ g = 𝟙 P := by
    apply (hP'.baseChange_hom_bijective_of_surjective_closedImmersion hP' b).injective
    change B.map (f ≫ g) = B.map (𝟙 P)
    rw [Functor.map_comp, B.map_id, hf, hg, e.hom_inv_id]
  have hfg : g ≫ f = 𝟙 Q := by
    apply (hQ'.baseChange_hom_bijective_of_surjective_closedImmersion hQ' b).injective
    change B.map (g ≫ f) = B.map (𝟙 Q)
    rw [Functor.map_comp, B.map_id, hf, hg, e.inv_hom_id]
  exact ⟨⟨f, g, hgf, hfg⟩, hf⟩

variable {A : Type u} [CommRing A] (I : Ideal A)
  {G H : GroupScheme (Spec (CommRingCat.of A))}

private theorem transition_closed_surjective (n : ℕ) :
    IsClosedImmersion (transition I n) ∧ Surjective (transition I n) := by
  let φ := transitionRingHom I n
  have hsur := transitionRingHom_surjective I n
  refine ⟨IsClosedImmersion.spec_of_surjective (f := CommRingCat.ofHom φ) hsur, ⟨?_⟩⟩
  apply Langlands.AlgebraicGeometry.specMap_surjective φ hsur
  intro x hx
  refine ⟨2, ?_⟩
  have h := Ideal.pow_mem_pow hx 2
  rw [transitionRingHom_ker_sq I n, Ideal.mem_bot] at h
  exact h

set_option maxHeartbeats 900000 in
private theorem evaluate_comp_of_sourceIso {S : Scheme.{u}} {G H : GroupScheme S}
    {U V : Over S} (b : U ⟶ V) {P : GroupScheme V.left} {Q : GroupScheme U.left}
    (j : P ⟶ (baseChange V.hom).obj G) (k : Q ⟶ (baseChange U.hom).obj G)
    (d : (baseChange V.hom).obj H ≅ P) (e : (baseChange U.hom).obj H ≅ Q)
    (a : (baseChange b.left).obj P ≅ Q) (ha : familyHom j b = a.hom ≫ k)
    (hd : (baseChange b.left).map d.hom =
      (Descent.pullbackComparison V.hom b.left U.hom b.w H).hom ≫ e.hom ≫ a.inv) :
    HomScheme.evaluate b (d.hom ≫ j) = e.hom ≫ k := by
  let B := baseChange b.left
  let c := Descent.pullbackComparison V.hom b.left U.hom b.w H
  let g := Descent.pullbackComparison V.hom b.left U.hom b.w G
  change c.inv ≫ B.map (d.hom ≫ j) ≫ g.hom = _
  have hd' : B.map d.hom = c.hom ≫ e.hom ≫ a.inv := hd
  have ha' : B.map j ≫ g.hom = a.hom ≫ k := ha
  simp only [Functor.map_comp, hd', Category.assoc, Iso.inv_hom_id_assoc]
  rw [ha', Iso.inv_hom_id_assoc]

set_option maxHeartbeats 1000000 in
private theorem exists_next_sourceIso {S : Scheme.{u}} {G H : GroupScheme S}
    {U V : Over S} (b : U ⟶ V) [IsClosedImmersion b.left] [Surjective b.left]
    (hH : RelativeTorus.IsTorus H)
    (F : AdmissibleSubgroup ((baseChange U.hom).obj G))
    (F' : AdmissibleSubgroup ((baseChange V.hom).obj G)) (hF : restrict b F' = F)
    (e : (baseChange U.hom).obj H ≅ (admissibleRepresentative F).group) :
    ∃ d : (baseChange V.hom).obj H ≅ (admissibleRepresentative F').group,
      HomScheme.evaluate b (d.hom ≫ (admissibleRepresentative F').hom) =
        e.hom ≫ (admissibleRepresentative F).hom := by
  let B := baseChange b.left
  let r := admissibleRepresentative F
  let r' := admissibleRepresentative F'
  let j : B.obj r'.group ⟶ (baseChange U.hom).obj G := familyHom r'.hom b
  have hj : IsClosedSubgroup j := isClosedSubgroup_familyHom r'.hom r'.closed b
  have heq : range j = range r.hom :=
    (congrArg Subtype.val hF).trans r.represents.2.symm
  let eF : B.obj r'.group ≅ r.group := hj.sourceIsoOfRangeEq r.closed heq
  have heF : eF.hom ≫ r.hom = j := hj.sourceIsoOfRangeEq_hom_comp r.closed heq
  let cH := Descent.pullbackComparison V.hom b.left U.hom b.w H
  let E : B.obj ((baseChange V.hom).obj H) ≅ B.obj r'.group := cH ≪≫ e ≪≫ eF.symm
  obtain ⟨d, hd⟩ := exists_iso_of_reduction b.left (hH.baseChange V.hom) r'.torus E
  exact ⟨d, evaluate_comp_of_sourceIso b r'.hom r.hom d e eF heF.symm hd⟩

/-- A compatible sequence of actual closed tori on the adic thickenings of a
complete local ring has a common actual source torus and an adic Hom system. -/
def AdicTorusFamilyStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (G : GroupScheme (Spec (CommRingCat.of A))),
    let I := maximalIdeal A
    ∀ (F : ∀ n : ℕ, AdmissibleSubgroup ((baseChange (quotientMap I n)).obj G)),
      (∀ n, restrict (transitionOver I n) (F (n + 1)) = F n) →
      ∃ (H : GroupScheme (Spec (CommRingCat.of A))) (s : System I H G),
        RelativeTorus.IsTorus H ∧ ∀ n, IsClosedSubgroup (s.hom n) ∧ range (s.hom n) = (F n).val

set_option maxHeartbeats 1500000 in
/-- Lift an actual residue source and extend the chosen identifications
recursively by full faithfulness of torus Hom restriction. -/
theorem adicTorusFamily : AdicTorusFamilyStatement.{u} := by
  intro A _ _ _ G I F hF
  let r (n : ℕ) := admissibleRepresentative (F n)
  obtain ⟨H, hH, ⟨e₀⟩⟩ := HomScheme.Adic.adicTorusSourceLift A (r 0).group (r 0).torus
  let E (n : ℕ) := (baseChange (quotientMap I n)).obj H ≅ (r n).group
  let step (n : ℕ) (e : E n) :
      ∃ d : E (n + 1), HomScheme.evaluate (transitionOver I n) (d.hom ≫ (r (n + 1)).hom) =
        e.hom ≫ (r n).hom := by
    let b := transitionOver I n
    obtain ⟨hb, hb'⟩ := transition_closed_surjective I n
    have : IsClosedImmersion b.left := hb
    have : Surjective b.left := hb'
    exact exists_next_sourceIso b hH (F n) (F (n + 1)) (hF n) e
  let e : ∀ n : ℕ, E n := Nat.rec e₀ (fun n d => (step n d).choose)
  let s : System I H G := {
    hom n := (e n).hom ≫ (r n).hom,
    compatible n := (step n (e n)).choose_spec }
  exact ⟨H, s, hH, fun n => ⟨(r n).closed.iso_comp (e n),
    (range_iso_comp _ _).trans (r n).represents.2⟩⟩

end Langlands.GroupScheme.TorusSubgroupModuli
