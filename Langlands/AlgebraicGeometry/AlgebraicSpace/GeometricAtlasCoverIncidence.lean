import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasClosedCoverIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentGeometry
import Langlands.Topology.FiniteIncidenceConstructibility

/-! # Geometric base change of atlas closed-cover incidence -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S} {U : Over S} {ι : Type v}

@[simp]
theorem productAtlasMap_fst (a : (schemeYoneda S).obj U ⟶ F) (V : Over S) :
    productAtlasMap a V ≫ prod.fst = (schemeYoneda S).map (prod.fst (X := U) (Y := V)) ≫ a := by
  simp [productAtlasMap, Category.assoc]

@[simp]
theorem productAtlasMap_snd (a : (schemeYoneda S).obj U ⟶ F) (V : Over S) :
    productAtlasMap a V ≫ prod.snd = (schemeYoneda S).map (prod.snd (X := U) (Y := V)) := by
  simp [productAtlasMap, Category.assoc]

/-- Incidence after represented base change is witnessed by an original overlap point
whose image belongs to the range of the base-change scheme. -/
theorem atlasCoverIncidence_productAtlasMap_iff
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (V : Over S)
    (s : ι → Set U.left) (i j : ι) :
    atlasCoverIncidence (productAtlasMap a V)
        (isEtale_productAtlasMap a ha V).representable
        (fun k => (prod.fst (X := U) (Y := V)).left ⁻¹' s k) i j ↔
      ∃ r : (ha.representable.pullback a).left,
        (ha.representable.snd a).left r ∈ s i ∧
        (ha.representable.fst' a).left r ∈ s j ∧
        (ha.representable.pullback a).hom r ∈ Set.range V.hom := by
  let b := productAtlasMap a V
  let hb := (isEtale_productAtlasMap a ha V).representable
  let R := ha.representable.pullback a
  let s' : ι → Set (U ⨯ V).left := fun k => (prod.fst (X := U) (Y := V)).left ⁻¹' s k
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (coverFibreRelation_chartPointMap_iff b hb s' i j).mpr h
    have hsame : SameImage₂ a a ((prod.fst (X := U) (Y := V)).left x) ((prod.fst (X := U) (Y := V)).left y) := by
      obtain ⟨T, g, k, t, he, hg, hk⟩ :=
        (chartPointMap_eq_iff_sameImage₂ b b x y).mp hxy
      refine ⟨T, g ≫ prod.fst (X := U) (Y := V), k ≫ prod.fst (X := U) (Y := V), t, ?_, ?_, ?_⟩
      · have he' := congrArg (fun z => z ≫ prod.fst) he
        simpa only [Category.assoc, b, productAtlasMap_fst, ← Functor.map_comp_assoc] using he'
      · rw [Over.comp_left, Scheme.Hom.comp_apply, hg]
      · rw [Over.comp_left, Scheme.Hom.comp_apply, hk]
    obtain ⟨r, hrx, hry⟩ := hsame.exists_pullback ha.representable
    refine ⟨r, ?_, ?_, (prod.snd (X := U) (Y := V)).left x, ?_⟩
    · simpa only [hrx, s', Set.mem_preimage] using hx
    · simpa only [hry, s', Set.mem_preimage] using hy
    · have h₁ := congrArg (fun (g : R.left ⟶ S) => g r)
        (Over.w (ha.representable.snd a))
      have h₂ := congrArg (fun (g : (U ⨯ V).left ⟶ S) => g x)
        ((Over.w (prod.fst (X := U) (Y := V))).trans (Over.w (prod.snd (X := U) (Y := V))).symm)
      simp only [Scheme.Hom.comp_apply] at h₁ h₂
      exact (h₁.symm.trans ((congrArg U.hom hrx).trans h₂)).symm
  · rintro ⟨r, hri, hrj, hrV⟩
    have hrange : r ∈ Set.range (Limits.pullback.fst R.hom V.hom) := by
      rw [Scheme.Pullback.range_fst]
      exact hrV
    obtain ⟨t, ht⟩ := hrange
    let t' : (R ⨯ V).left := (Over.prodLeftIsoPullback R V).inv t
    have htR : (prod.fst (X := R) (Y := V)).left t' = r := by
      change (prod.fst (X := R) (Y := V)).left ((Over.prodLeftIsoPullback R V).inv t) = r
      rw [← Scheme.Hom.comp_apply, Over.prodLeftIsoPullback_inv_fst]
      exact ht
    let g : R ⨯ V ⟶ U ⨯ V := prod.map (ha.representable.snd a) (𝟙 V)
    let k : R ⨯ V ⟶ U ⨯ V := prod.map (ha.representable.fst' a) (𝟙 V)
    have he : (schemeYoneda S).map (ha.representable.snd a) ≫ a =
        (schemeYoneda S).map (ha.representable.fst' a) ≫ a :=
      (Functor.relativelyRepresentable.isPullback' ha.representable a).w.symm
    have hmaps : (schemeYoneda S).map g ≫ b = (schemeYoneda S).map k ≫ b := by
      apply prod.hom_ext
      · simp only [Category.assoc, b, productAtlasMap_fst, ← Functor.map_comp_assoc,
          g, k, prod.map_fst]
        simp only [Functor.map_comp, Category.assoc, he]
      · simp only [Category.assoc, b, productAtlasMap_snd, ← Functor.map_comp,
          g, k, prod.map_snd]
    have hfst (d : R ⟶ U) :
        (prod.fst (X := U) (Y := V)).left ((prod.map d (𝟙 V)).left t') = d.left r := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, prod.map_fst, Over.comp_left,
        Scheme.Hom.comp_apply, htR]
    apply (coverFibreRelation_chartPointMap_iff b hb s' i j).mp
    refine ⟨g.left t', ?_, k.left t', ?_, chartPointMap_comm hmaps t'⟩
    · change (prod.fst (X := U) (Y := V)).left (g.left t') ∈ s i
      simpa only [g, hfst] using hri
    · change (prod.fst (X := U) (Y := V)).left (k.left t') ∈ s j
      simpa only [k, hfst] using hrj

/-- Pull the atlas cover back to the canonical algebraic-closure geometric point. -/
def geometricAtlasCoverSets (s : ι → Set U.left) (p : S) :
    ι → Set (U ⨯ Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)).left :=
  fun i => (prod.fst (X := U) (Y := Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))).left ⁻¹' s i

/-- The canonical geometric point has exactly its given base point as its image. -/
theorem range_componentCountGeometricPoint (p : S) :
    Set.range (SchemeFiberGeometry.componentCountGeometricPoint p) = {p} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    change S.fromSpecResidueField p _ = p
    exact Scheme.fromSpecResidueField_apply p _
  · intro hq
    have hqp : q = p := Set.mem_singleton_iff.mp hq
    subst q
    refine ⟨closedPoint (AlgebraicClosure (S.residueField p)), ?_⟩
    change S.fromSpecResidueField p _ = p
    exact Scheme.fromSpecResidueField_apply p _

/-- Geometric cover incidence is exactly membership in the original overlap image locus. -/
theorem geometricAtlasCoverIncidence_iff
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    (s : ι → Set U.left) (p : S) (i j : ι) :
    atlasCoverIncidence
        (productAtlasMap a (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
        (isEtale_productAtlasMap a ha _).representable
        (geometricAtlasCoverSets s p) i j ↔
      p ∈ atlasCoverIncidenceLocus a ha.representable s i j := by
  unfold geometricAtlasCoverSets
  rw [atlasCoverIncidence_productAtlasMap_iff a ha
    (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)) s i j]
  simp only [Over.mk_hom]
  rw [range_componentCountGeometricPoint p]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hi, hj, hp⟩
    exact ⟨r, ⟨hi, hj⟩, hp⟩
  · rintro ⟨r, ⟨hi, hj⟩, hp⟩
    exact ⟨r, hi, hj, hp⟩

/-- A finite connected geometric atlas cover computes the fibre components using the
original overlap image relation on its fixed labels. -/
def geometricAtlasClosedCoverComponentsEquiv [Finite ι]
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    (s : ι → Set U.left) (hclosed : ∀ i, IsClosed (s i)) (p : S)
    (hconn : ∀ i, _root_.IsConnected (geometricAtlasCoverSets s p i))
    (hcover : (⋃ i, geometricAtlasCoverSets s p i) = Set.univ) :
    Quot (fun i j => p ∈ atlasCoverIncidenceLocus a ha.representable s i j) ≃
      @_root_.ConnectedComponents
        (Points (F ⨯ (schemeYoneda S).obj
          (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))))
        (pointTopology _) := by
  exact (Quot.congr (Equiv.refl ι) (fun i j =>
    (geometricAtlasCoverIncidence_iff a ha s p i j).symm)).trans
      (atlasClosedCoverConnectedComponentsEquiv _ (isEtale_productAtlasMap a ha _)
        (isSurjective_productAtlasMap a hs _) (geometricAtlasCoverSets s p)
        (fun i => (hclosed i).preimage
          (prod.fst (X := U) (Y := Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))).left.continuous)
        hconn hcover)

/-- Actual geometric component-count loci are constructible over a Noetherian ring
when one finite closed atlas cover is connected and covering on every geometric fibre. -/
theorem isConstructible_geometricFibreCount_of_closedAtlasCover
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Finite ι]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : IsQuasiSeparated X)
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (s : ι → Set U.left) (hclosed : ∀ i, IsClosed (s i))
    (hconn : ∀ p i, _root_.IsConnected (geometricAtlasCoverSets s p i))
    (hcover : ∀ p, (⋃ i, geometricAtlasCoverSets s p i) = Set.univ) (n : ℕ) :
    IsConstructible {p | geometricFibreComponentCount B X p = n} := by
  let R : Spec (CommRingCat.of B) → ι → ι → Prop :=
    fun p i j => p ∈ atlasCoverIncidenceLocus a ha.representable s i j
  have hcount (p : Spec (CommRingCat.of B)) :
      geometricFibreComponentCount B X p = ENat.card (Quot (R p)) :=
    (ENat.card_congr
      (geometricAtlasClosedCoverComponentsEquiv a ha hs s hclosed p (hconn p) (hcover p))).symm
  have heq : {p | geometricFibreComponentCount B X p = n} =
      {p | ENat.card (Quot (R p)) = n} := by
    ext p
    simp only [Set.mem_ofPred_eq, hcount p]
  rw [heq]
  exact Langlands.Topology.isConstructible_finite_incidenceQuotient_count R
    (fun i j => isConstructible_atlasCoverIncidenceLocus X hX a ha s hclosed i j) n

end Langlands.AlgebraicGeometry.AlgebraicSpace
