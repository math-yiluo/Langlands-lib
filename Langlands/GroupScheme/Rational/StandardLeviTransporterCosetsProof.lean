import Langlands.GroupScheme.Rational.StandardLeviTransporterCosetsStatement
import Langlands.GroupScheme.Rational.StandardLeviNormalizerQuotientProof

/-! # The point and Weyl transporter cosets in Renard VII.1.3 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open StandardMaximalLeviWeyl

namespace StandardLeviTransporterCosets

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A point transporting one standard Levi onto another can be replaced by a
normalizer point in the same left coset of the source Levi. -/
private theorem exists_normalizerPoint_in_coset (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I J : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X)
    (hg : (levi i ν I).map
        (MulAut.conj g : RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J) :
    ∃ n : normalizerPoints i,
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
          RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J ∧
        (n : RationalPoint k G.X)⁻¹ * g ∈ levi i ν I := by
  let roots := rootSet i ν J
  let j := Standard.leviHom i ν roots
  have hrep := Standard.isRepresentedBy_leviHom i ν roots
  have hclosed := Standard.isClosedSubgroup_leviHom i ν roots
  let conjugateTorus := i ≫ (G.innerIso g).hom
  have hsplit := hi.isSplitSubtorus.1
  have : Smooth T.toGrp.X.hom := hsplit.smooth
  have : IsAffineHom T.toGrp.X.hom := hsplit.isAffineHom
  have : ConnectedSpace T.toGrp.X.left := hsplit.connectedSpace
  have hpoints : (SubgroupFunctor.range conjugateTorus).carrier (Over.mk (𝟙 _)) ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
    rw [hrep.2]
    intro x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have ht : t ≫ i.hom.hom ∈ levi i ν I := torusPoints_le_levi i ν I ⟨t, rfl⟩
    have he : t ≫ conjugateTorus.hom.hom = g * (t ≫ i.hom.hom) * g⁻¹ := by
      rw [← StandardLeviNormalizerQuotient.comp_innerIso_hom_base g (t ≫ i.hom.hom)]
      simp only [conjugateTorus, Grp.comp_hom_hom, Category.assoc]
    change t ≫ conjugateTorus.hom.hom ∈ levi i ν J
    rw [he, ← hg]
    exact ⟨_, ht, rfl⟩
  have hconjugateRange : SubgroupFunctor.range conjugateTorus ≤ standardLevi i ν roots :=
    hrep.2 ▸ SubgroupFunctor.range_le_of_localField_points hclosed hpoints
  have htorusRange : SubgroupFunctor.range i ≤ standardLevi i ν roots :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν roots)
  let f := hrep.factorHom conjugateTorus hconjugateRange
  let f₀ := hrep.factorHom i htorusRange
  have hf : f ≫ j = conjugateTorus := hrep.factorHom_comp conjugateTorus hconjugateRange
  have hf₀ : f₀ ≫ j = i := hrep.factorHom_comp i htorusRange
  have hfmax : IsMaximalSplitTorus f :=
    (hi.comp_iso (G.innerIso g)).isMaximalSplitTorus_factorHom hrep hclosed hconjugateRange
  have hf₀max : IsMaximalSplitTorus f₀ :=
    hi.isMaximalSplitTorus_factorHom hrep hclosed htorusRange
  have hLevi := (standardLeviSplitComponentStatement k G hG T i hi ν hν roots
    (rootSet_subset i ν J)).1
  obtain ⟨m, e, hm⟩ := (maximalSplitTorusConjugacy k _ hLevi).1 T T f f₀ hfmax hf₀max
  let m' : RationalPoint k G.X := m ≫ j.hom.hom
  have hm' : m' ∈ levi i ν J := by
    change m' ∈ (standardLevi i ν roots).carrier _
    rw [← hrep.2]
    exact ⟨m, rfl⟩
  have hconj : i ≫ (G.innerIso (m' * g)).hom = e.hom ≫ i := by
    have h := congrArg (· ≫ j) hm
    simp only [Category.assoc] at h
    rw [innerIso_hom_comp, ← Category.assoc, hf, hf₀] at h
    rw [innerIso_mul_hom, ← Category.assoc]
    exact h
  let e' : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hnormalizes : m' * g ∈ normalizerPoints i := ⟨e', hconj⟩
  refine ⟨⟨m' * g, hnormalizes⟩, ?_, ?_⟩
  · change (levi i ν I).map (MulAut.conj (m' * g) :
      RationalPoint k G.X →* RationalPoint k G.X) = _
    rw [map_conj_mul, hg, map_conj_eq_self_of_mem hm']
  · have hmem : g⁻¹ * m'⁻¹ * (g⁻¹)⁻¹ ∈ levi i ν I := by
      rw [← map_conj_inv_of_map_conj_eq hg]
      exact ⟨m'⁻¹, (levi i ν J).inv_mem hm', rfl⟩
    change (m' * g)⁻¹ * g ∈ levi i ν I
    simpa [mul_inv_rev] using hmem

end StandardLeviTransporterCosets

/-- The standard Levi transporter comparison is induced by the same
normalizer point on both quotient sets. -/
theorem standardLeviTransporterCosets : StandardLeviTransporterCosetsStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν I isTransporter pointCosets
  let weylCoset (n : normalizerPoints i) :
      relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I) :=
    QuotientGroup.mk (QuotientGroup.mk n : relativeWeylGroup i)
  let pointCoset (g : RationalPoint k G.X) : RationalPoint k G.X ⧸ levi i ν I :=
    QuotientGroup.mk g
  have hEq (n m : normalizerPoints i) :
      weylCoset n = weylCoset m ↔ pointCoset n = pointCoset m := by
    simp only [weylCoset, pointCoset, QuotientGroup.eq, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, mk_mem_iff_mem_levi, Subgroup.coe_mul, Subgroup.coe_inv]
  have lift (x : cosets I) : ∃ n : normalizerPoints i, weylCoset n = x.val ∧ isTransporter n := by
    obtain ⟨w, ⟨n, rfl, hn⟩, hw⟩ := x.property
    exact ⟨n, hw, hn⟩
  let toPoint (x : cosets I) : pointCosets :=
    ⟨pointCoset (lift x).choose, ⟨(lift x).choose, (lift x).choose_spec.2, rfl⟩⟩
  have representative (x : cosets I) (n : normalizerPoints i) (hx : x.val = weylCoset n) :
      (toPoint x).val = pointCoset n :=
    (hEq (lift x).choose n).mp ((lift x).choose_spec.1.trans hx)
  have hinj : Function.Injective toPoint := by
    intro x y hxy
    apply Subtype.ext
    have h := (hEq (lift x).choose (lift y).choose).mpr (congrArg Subtype.val hxy)
    exact (lift x).choose_spec.1.symm.trans (h.trans (lift y).choose_spec.1)
  have hsurj : Function.Surjective toPoint := by
    intro y
    obtain ⟨g, ⟨J, hg⟩, hgy⟩ := y.property
    obtain ⟨n, hn, hng⟩ :=
      StandardLeviTransporterCosets.exists_normalizerPoint_in_coset i ν hG hi hν I J g hg
    let x : cosets I := ⟨weylCoset n, ⟨QuotientGroup.mk n, ⟨n, rfl, J, hn⟩, rfl⟩⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [representative x n rfl]
    exact (QuotientGroup.eq.mpr hng).trans hgy
  exact ⟨Equiv.ofBijective toPoint ⟨hinj, hsurj⟩, representative⟩

end Langlands.GroupScheme
