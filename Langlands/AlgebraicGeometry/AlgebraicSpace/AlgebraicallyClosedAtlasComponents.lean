import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricAtlasCoverIncidence
import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverProof
import Langlands.AlgebraicGeometry.AlgClosedConnectedProof

/-! # Atlas components under extension of an algebraically closed field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open GenericImagePattern ComponentIncidence

variable {K L : Type u} [Field K] [Field L]
  {F : Presheaf (Spec (CommRingCat.of K))}
  {U : Over (Spec (CommRingCat.of K))} {ι : Type v}

/-- The product-chart cover agrees with the actual field-base-change ranges. -/
theorem productAtlasCoverSets_eq_preimage
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left) (i : ι) :
    ((prod.fst (X := U) (Y := Over.mk e)).left ⁻¹' Set.range (g i)) =
      (Over.prodLeftIsoPullback U (Over.mk e)).hom ⁻¹'
        baseChangeSubschemeRanges (Limits.pullback.fst U.hom e) g i := by
  rw [baseChangeSubschemeRanges_eq_preimage]
  ext x
  change (prod.fst (X := U) (Y := Over.mk e)).left x ∈ Set.range (g i) ↔
    Limits.pullback.fst U.hom e
    ((Over.prodLeftIsoPullback U (Over.mk e)).hom x) ∈ Set.range (g i)
  have h := congrArg (fun (q : (U ⨯ Over.mk e).left ⟶ U.left) => q x)
    (Over.prodLeftIsoPullback_hom_fst U (Over.mk e))
  exact Iff.of_eq (by
    simpa only [Over.mk_hom, Scheme.Hom.comp_apply] using
      (congrArg (fun y => y ∈ Set.range (g i)) h).symm)

/-- A geometrically connected piece stays connected in the product atlas. -/
theorem isConnected_productAtlasCoverSets
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left) (i : ι)
    [GeometricallyConnected (g i ≫ U.hom)] :
    _root_.IsConnected ((prod.fst (X := U) (Y := Over.mk e)).left ⁻¹'
      Set.range (g i)) := by
  rw [productAtlasCoverSets_eq_preimage e g i]
  exact (Over.prodLeftIsoPullback U (Over.mk e)).hom.homeomorph.isConnected_preimage.mpr
    (isConnected_fieldBaseChangeSubschemeRanges U.hom e g i)

/-- A finite geometrically connected closed chart cover computes the same actual
component set after any extension of the base field. -/
def fieldAtlasClosedCoverComponentsEquiv [Finite ι]
    (a : (schemeYoneda _).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left)
    [∀ i, _root_.AlgebraicGeometry.IsClosedImmersion (g i)] [∀ i, GeometricallyConnected (g i ≫ U.hom)]
    (hcover : (⋃ i, Set.range (g i)) = Set.univ) :
    @_root_.ConnectedComponents (Points (F ⨯ (schemeYoneda _).obj (Over.mk e)))
        (pointTopology _) ≃
      @_root_.ConnectedComponents (Points F) (pointTopology _) := by
  let s := fun i => Set.range (g i)
  let t := fun i => (prod.fst (X := U) (Y := Over.mk e)).left ⁻¹' s i
  have hclosed : ∀ i, IsClosed (s i) :=
    fun i => (g i).isClosedEmbedding.isClosed_range
  have hconn : ∀ i, _root_.IsConnected (s i) := by
    intro i
    let : ConnectedSpace (Z i) :=
      GeometricallyConnected.connectedSpace_of_subsingleton (g i ≫ U.hom)
    exact isConnected_range (g i).continuous
  have hconn' : ∀ i, _root_.IsConnected (t i) :=
    fun i => isConnected_productAtlasCoverSets e g i
  have hcover' : (⋃ i, t i) = Set.univ := by
    simp only [t, ← Set.preimage_iUnion, show (⋃ i, s i) = Set.univ from hcover,
      Set.preimage_univ]
  have hrel : ∀ i j,
      atlasCoverIncidence (productAtlasMap a (Over.mk e))
        (isEtale_productAtlasMap a ha _).representable t i j ↔
      atlasCoverIncidence a ha.representable s i j := by
    intro i j
    rw [atlasCoverIncidence_productAtlasMap_iff a ha (Over.mk e) s i j]
    let := surjective_fieldSpectrumMap e
    constructor
    · rintro ⟨r, hi, hj, _⟩
      exact ⟨r, hi, hj⟩
    · rintro ⟨r, hi, hj⟩
      exact ⟨r, hi, hj, e.surjective ((ha.representable.pullback a).hom r)⟩
  exact (atlasClosedCoverConnectedComponentsEquiv _ (isEtale_productAtlasMap a ha _)
    (isSurjective_productAtlasMap a hs _) t
    (fun i => (hclosed i).preimage
      (prod.fst (X := U) (Y := Over.mk e)).left.continuous) hconn' hcover').symm.trans
      ((Quot.congr (Equiv.refl ι) hrel).trans
        (atlasClosedCoverConnectedComponentsEquiv a ha hs s hclosed hconn hcover))

/-- Over an algebraically closed field, every finite-type quasi-compact atlas
has an actual component equivalence after every field extension. -/
def algebraicallyClosedAtlasComponentsEquiv [IsAlgClosed K]
    (a : (schemeYoneda _).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    @_root_.ConnectedComponents (Points (F ⨯ (schemeYoneda _).obj (Over.mk e)))
        (pointTopology _) ≃
      @_root_.ConnectedComponents (Points F) (pointTopology _) := by
  let : IsNoetherian U.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian U.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace U.hom }
  let := (NoetherianSpace.finite_irreducibleComponents (α := U.left)).to_subtype
  let C : irreducibleComponents U.left → TopologicalSpace.Closeds U.left :=
    fun c => ⟨c.val, isClosed_of_mem_irreducibleComponents c.val c.property⟩
  let Z := fun c => (Scheme.IdealSheafData.vanishingIdeal (C c)).subscheme
  let g : ∀ c, Z c ⟶ U.left :=
    fun c => (Scheme.IdealSheafData.vanishingIdeal (C c)).subschemeι
  have hrange : ∀ c, Set.range (g c) = c.val := by
    intro c
    exact Scheme.IdealSheafData.range_subschemeι _
  let : ∀ c, _root_.AlgebraicGeometry.IsClosedImmersion (g c) := fun c => inferInstance
  let : ∀ c, GeometricallyConnected (g c ≫ U.hom) := by
    intro c
    let : ConnectedSpace ↥(Set.range (g c)) :=
      isConnected_iff_connectedSpace.mp ((hrange c).symm ▸ c.property.1.isConnected)
    let : ConnectedSpace (Z c) := (g c).isEmbedding.toHomeomorph.connectedSpace_iff.mpr
      inferInstance
    exact Langlands.AlgebraicGeometry.algClosedConnected K (Z c) (g c ≫ U.hom)
  apply fieldAtlasClosedCoverComponentsEquiv a ha hs e g
  simp_rw [hrange]
  exact iUnion_componentSets U.left

end Langlands.AlgebraicGeometry.AlgebraicSpace
