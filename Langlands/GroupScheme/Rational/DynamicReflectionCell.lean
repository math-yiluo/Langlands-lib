import Langlands.GroupScheme.Rational.DynamicReflectionNormalizerLift
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Ordinary dynamic cells for a fixed lifted reflection -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section NormalizingImage

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G H : GroupScheme S}
    {i : T.toGrp ⟶ G} {m : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}

/-- A group homomorphism preserves the same actual normalizing equation. -/
theorem IsNormalizingPoint.comp_hom (hm : IsNormalizingPoint i m σ) (q : G ⟶ H) :
    IsNormalizingPoint (i ≫ q) (m ≫ q.hom.hom) σ := by
  change (i ≫ q) ≫ (H.innerIso (m ≫ q.hom.hom)).hom =
    CommGroupScheme.groupHom σ.hom ≫ (i ≫ q)
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hm, Category.assoc]

end NormalizingImage

namespace RelativeRoot

section CyclicConjugation

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) {a : characterLattice T}

/-- Under integral cyclic root support, a normalizer negating the original
character carries the entire opposite dynamic subgroup into the positive one. -/
theorem dynamic_conj_opposite_mem_unipotent_of_cyclic_support
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (hcyclic : ∀ c ∈ relativeRoots i, c ∈ AddSubgroup.zmultiples a)
    (hpos : 0 < latticePairing T a ν)
    (hne : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) ≠ ⊥)
    (n : normalizerPoints i) (hn : weylAction i n a = -a)
    {V : Over (Spec (CommRingCat.of k))} {w : V ⟶ G.X}
    (hw : w ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier V) :
    G.constantPoint n V * w * (G.constantPoint n V)⁻¹ ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier V := by
  let b := cyclicDynamicRoot i ν hT hroot hcyclic hpos hne
  have hb : weylAction i n b.val = -b.val := by
    obtain ⟨r, hr⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (hcyclic b.val b.property.1.1.1)
    rw [← hr, map_zsmul, hn, smul_neg]
  rw [b.property.2.2] at hw
  rw [b.property.2.1]
  have h := normalizer_conj_mem i (-b.val) n hw
  simpa only [map_neg, hb, neg_neg] using h

end CyclicConjugation

section Lift

variable {k : Type u} [Field k] [PerfectField k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (r : N ⟶ G) (hr : IsClosedSubgroup r) (hN : IsUnipotent N)
    (q : G ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range r) q)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (hQ : IsConnectedReductive Q) (hi : IsMaximalSplitTorus (i ≫ q))
    [IsAffineHom Q.X.hom] [Mono (i ≫ q).hom.hom.left]
    (a : characterLattice T)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp Q)
    (he : e.restrict (CommGroupScheme.groupHom a) =
      AutomorphicAction.conjugation (i ≫ q))
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)
    (hne : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ (i ≫ q)) ≠ ⊥)

/-- Choose one actual source normalizer and its exact torus automorphism
whose quotient image translates every nonidentity positive dynamic point
into the ordinary opposite-unipotent/parabolic cell. -/
def dynamicReflectionCellNormalizerLift :
    {m : rationalPoints G × (T ≅ T) //
      IsNormalizingPoint i m.1 m.2 ∧ characterAut m.2 a = -a ∧
        ∀ (x : rationalPoints Q),
          x ∈ (Dynamic.unipotent
            (CommGroupScheme.groupHom ν ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)) →
          x ≠ 1 →
          ∃ y ∈ (Dynamic.unipotent
              (CommGroupScheme.groupHom (-ν) ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)),
            ∃ v ∈ (Dynamic.parabolic
                (CommGroupScheme.groupHom ν ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)),
              x * (rationalPoints.map q m.1)⁻¹ = y * v} := by
  let : Smooth Q.X.hom := hQ.smooth
  let m := dynamicReflectionNormalizerLift r hr hN q hq i hT hQ hi a e he ν hpos hne
  let n : normalizerPoints (i ≫ q) :=
    ⟨rationalPoints.map q m.val.1, ⟨m.val.2, m.property.1.comp_hom q⟩⟩
  have hn : weylAction (i ≫ q) n a = -a := by
    have hmQ : IsNormalizingPoint (i ≫ q) n.val m.val.2 :=
      m.property.1.comp_hom q
    have hσ : normalizingAut (i ≫ q) n = m.val.2 :=
      (isNormalizingPoint_normalizingAut (i ≫ q) n).unique (i ≫ q) hmQ
    change characterAut (normalizingAut (i ≫ q) n) a = -a
    rw [hσ]
    exact m.property.2.1
  have hcyclic : ∀ c ∈ relativeRoots (i ≫ q), c ∈ AddSubgroup.zmultiples a :=
    fun _ hc => root_mem_zmultiples_of_descendedAction (i ≫ q) a e he
      hi.isSplitSubtorus.1 hc
  refine ⟨m.val, m.property.1, m.property.2.1, ?_⟩
  intro x hx hx1
  obtain ⟨y, hy, z, hz, w, hw, hprod⟩ := m.property.2.2 x hx hx1
  have hw' : n.val * w * n.val⁻¹ ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ (i ≫ q))).carrier
        (Over.mk (𝟙 _)) := by
    simpa only [GroupScheme.constantPoint_self] using
      dynamic_conj_opposite_mem_unipotent_of_cyclic_support (i ≫ q) ν
        hi.isSplitSubtorus.1 (relativeRootSystem k Q hQ T (i ≫ q) hi)
        hcyclic hpos hne n hn hw
  refine ⟨y, hy, z * (n.val * w * n.val⁻¹), ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (Dynamic.centralizer_le_parabolic _ _ hz)
      (Dynamic.unipotent_le_parabolic _ _ hw')
  · change x * n.val⁻¹ = y * (z * (n.val * w * n.val⁻¹))
    change x = y * z * n.val * w at hprod
    rw [hprod]
    group

end Lift

end RelativeRoot
end Langlands.GroupScheme
