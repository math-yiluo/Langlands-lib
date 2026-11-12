import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPointsEquivalence
import Langlands.Global.AdelicSpaceLevelPointsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceStatement

/-! # Exact integral and product preimages for algebraic-space points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace AdelicSpacePreimageAssembly

/-- Local coefficient lifts assemble whenever the source level has all product points. -/
theorem mem_range_of_local_lifts
    (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B]
    {ι : Type u} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, CommRing (L i)]
    [∀ i, Algebra C (R i)] [∀ i, Algebra C (L i)]
    (a : A →ₐ[C] B) (ar : ∀ i, A →ₐ[C] R i)
    (b : B →ₐ[C] ∀ i, L i) (hb : Function.Injective b)
    (r : ∀ i, R i →ₐ[C] L i)
    (hcompat : ∀ i, (Pi.evalAlgHom C L i).comp (b.comp a) = (r i).comp (ar i))
    (X : AlgebraicSpace (Spec (CommRingCat.of C))) (hX : IsSeparated X)
    (hprod : Function.Surjective
      (fun (p : RingPoints C X A) i => RingPoints.changeRing (ar i) p))
    (z : RingPoints C X B)
    (hlift : ∀ i, ∃ q : RingPoints C X (R i),
      RingPoints.changeRing (r i) q =
        RingPoints.changeRing ((Pi.evalAlgHom C L i).comp b) z) :
    z ∈ Set.range (RingPoints.changeRing (X := X) a) := by
  classical
  choose q hq using hlift
  obtain ⟨p, hp⟩ := hprod q
  refine ⟨p, ?_⟩
  apply RelativeIntegralPoints.changeRing_injective hX b hb
  apply separatedProductPoints_injective C X hX ι L
  funext i
  calc
    RingPoints.changeRing (Pi.evalAlgHom C L i)
        (RingPoints.changeRing b (RingPoints.changeRing a p)) =
        RingPoints.changeRing ((Pi.evalAlgHom C L i).comp (b.comp a)) p := by
      simp only [ProductPointsDescent.changeRing_changeRing]
    _ = RingPoints.changeRing ((r i).comp (ar i)) p := by rw [hcompat i]
    _ = RingPoints.changeRing (r i) (RingPoints.changeRing (ar i) p) :=
      (ProductPointsDescent.changeRing_changeRing C _ _ _).symm
    _ = RingPoints.changeRing (r i) (q i) :=
      congrArg (RingPoints.changeRing (r i)) (congrFun hp i)
    _ = RingPoints.changeRing ((Pi.evalAlgHom C L i).comp b) z := hq i
    _ = RingPoints.changeRing (Pi.evalAlgHom C L i) (RingPoints.changeRing b z) :=
      (ProductPointsDescent.changeRing_changeRing C _ _ _).symm

/-- Exact local integral preimages imply the exact level preimage. -/
theorem preimage_eq_of_local_preimages
    (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B]
    {ι : Type u} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, CommRing (L i)]
    [∀ i, Algebra C (R i)] [∀ i, Algebra C (L i)]
    (a : A →ₐ[C] B) (ar : ∀ i, A →ₐ[C] R i)
    (b : B →ₐ[C] ∀ i, L i) (hb : Function.Injective b)
    (r : ∀ i, R i →ₐ[C] L i)
    (hcompat : ∀ i, (Pi.evalAlgHom C L i).comp (b.comp a) = (r i).comp (ar i))
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (hX : IsSeparated X)
    (hprod : Function.Surjective
      (fun (p : RingPoints C X A) i => RingPoints.changeRing (ar i) p))
    (hlocal : ∀ i,
      (RingPoints.map f : RingPoints C X (L i) → RingPoints C Y (L i)) ⁻¹'
          Set.range (RingPoints.changeRing (X := Y) (r i)) =
        Set.range (RingPoints.changeRing (X := X) (r i))) :
    (RingPoints.map f : RingPoints C X B → RingPoints C Y B) ⁻¹'
        Set.range (RingPoints.changeRing (X := Y) a) =
      Set.range (RingPoints.changeRing (X := X) a) := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    apply mem_range_of_local_lifts C A B R L a ar b hb r hcompat X hX hprod z
    intro i
    change RingPoints.changeRing ((Pi.evalAlgHom C L i).comp b) z ∈
      Set.range (RingPoints.changeRing (X := X) (r i))
    rw [← hlocal i]
    refine ⟨RingPoints.changeRing (ar i) w, ?_⟩
    rw [ProductPointsDescent.changeRing_changeRing, ← hcompat i]
    change RingPoints.changeRing (((Pi.evalAlgHom C L i).comp b).comp a) w = _
    rw [← ProductPointsDescent.changeRing_changeRing, hw, RingPoints.changeRing_map]
  · rintro ⟨q, rfl⟩
    exact ⟨RingPoints.map f q, RingPoints.changeRing_map f a q⟩

/-- An isomorphism of coefficient rings has the exact preimage property. -/
theorem preimage_eq_of_bijective
    {C R L : Type u} [CommRing C] [CommRing R] [CommRing L]
    [Algebra C R] [Algebra C L] (r : R →ₐ[C] L) (hr : Function.Bijective r)
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y) :
    (RingPoints.map f : RingPoints C X L → RingPoints C Y L) ⁻¹'
        Set.range (RingPoints.changeRing (X := Y) r) =
      Set.range (RingPoints.changeRing (X := X) r) := by
  have hX := (RingPoints.changeRingEquiv X (AlgEquiv.ofBijective r hr)).surjective
  have hY := (RingPoints.changeRingEquiv Y (AlgEquiv.ofBijective r hr)).surjective
  ext z
  exact ⟨fun _ => hX z, fun _ => hY (RingPoints.map f z)⟩

/-- The valuative-existence input gives the exact integral preimage over any base ring. -/
theorem integral_preimage_of_valuative
    (hv : SpaceValuativeExistenceStatement.{u})
    (C R L : Type u) [CommRing C] [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra C R] [Algebra R L] [Algebra C L] [IsScalarTower C R L]
    [IsFractionRing R L]
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (hf : IsProperMorphism f) :
    (RingPoints.map f : RingPoints C X L → RingPoints C Y L) ⁻¹'
        Set.range (RingPoints.changeRing (X := Y) (IsScalarTower.toAlgHom C R L)) =
      Set.range (RingPoints.changeRing (X := X) (IsScalarTower.toAlgHom C R L)) := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    change X.sections (ringTest C L) at z
    change Y.sections (ringTest C R) at w
    let s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of C) := Spec.algebraMap C R
    let e : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ s) ≅ ringTest C L :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap C L)) =
          Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap C R))
        rw [Category.id_comp]
        rw [← Spec.map_comp]
        congr 1
        exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq C R L))
    let z' := X.pullback e.hom z
    have hcomm : mapSections f _ z' =
        Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R L))) rfl) w := by
      change mapSections f _ (X.pullback e.hom z) = _
      rw [← mapSections_naturality]
      change Y.pullback e.hom (RingPoints.map f z) = _
      rw [← hw]
      change Y.pullback e.hom
        (Y.pullback (ringTestMap C (IsScalarTower.toAlgHom C R L)) w) = _
      rw [← pullback_comp]
      apply BaseChangeComparison.pullback_congr_left
      exact Category.id_comp _
    obtain ⟨q, hq, _⟩ := hv _ X Y f hf.2.1 hf.1 hf.2.2.2
      R L s z' w hcomm
    refine ⟨q, ?_⟩
    have he := congrArg (X.pullback e.inv) hq
    change X.pullback e.inv (X.pullback _ q) = X.pullback e.inv (X.pullback e.hom z) at he
    rw [← pullback_comp, ← pullback_comp, e.inv_hom_id, pullback_id] at he
    change X.pullback (ringTestMap C (IsScalarTower.toAlgHom C R L)) q = z
    rw [← he]
    apply BaseChangeComparison.pullback_congr_left
    exact (Category.id_comp _).symm
  · rintro ⟨q, rfl⟩
    exact ⟨RingPoints.map f q, RingPoints.changeRing_map f _ q⟩

end AdelicSpacePreimageAssembly

end Langlands.AlgebraicGeometry.AlgebraicSpace
