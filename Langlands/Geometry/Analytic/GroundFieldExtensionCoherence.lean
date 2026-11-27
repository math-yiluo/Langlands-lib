import Langlands.Geometry.Analytic.GroundFieldExtensionTowerNaturality
import Langlands.Geometry.Analytic.GroundFieldExtensionUnitAtlas
import Langlands.Geometry.Analytic.ValuedField.CompleteUltrametricFields

/-! # Coherence of scalar extension on compatible analytic atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Set PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension IndexedAffinoidAtlas.GroundFieldExtension

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- The matching chart indices and their presentation coordinates. -/
private structure ChartCoordinates (A : AffinoidAtlasPresentation.{u, v, w} K)
    (I : Type w) (n : I → ℕ) where
  index : I → A.atlas.Index
  surjective : Function.Surjective index
  position : ∀ i, Fin (n i) ≃ Fin (A.atlas.algebra (index i)).arity

private def ChartCoordinates.base (A : AffinoidAtlasPresentation.{u, v, w} K) :
    ChartCoordinates A A.atlas.Index (fun i => (A.atlas.algebra i).arity) :=
  ⟨id, Function.surjective_id, fun _ => Equiv.refl _⟩

variable {I : Type w} {n : I → ℕ}

private def PullsBackCoordinates (f : CompatibleStrongHom A B)
    (a : ChartCoordinates A I n) (b : ChartCoordinates B I n) : Prop :=
  ∀ i : I, ∃ h : f.baseMap '' range (A.atlas.chart (a.index i)) ⊆ range (B.atlas.chart (b.index i)),
    ∀ k : Fin (n i), f.pullback (a.index i) (b.index i) h
      (coordinate K (B.atlas.algebra (b.index i)) (b.position i k)) =
      coordinate K (A.atlas.algebra (a.index i)) (a.position i k)

private theorem PullsBackCoordinates.comp {f : CompatibleStrongHom A B} {g : CompatibleStrongHom B C}
    {a : ChartCoordinates A I n} {b : ChartCoordinates B I n} {c : ChartCoordinates C I n}
    (hf : PullsBackCoordinates f a b) (hg : PullsBackCoordinates g b c) :
    PullsBackCoordinates (f.comp g) a c := by
  intro i
  obtain ⟨hi, hfi⟩ := hf i
  obtain ⟨hj, hgi⟩ := hg i
  have ht : (f.comp g).baseMap '' range (A.atlas.chart (a.index i)) ⊆ range (C.atlas.chart (c.index i)) :=
    f.toStrongHom.comp_admissible g.toStrongHom (a.index i) (b.index i) (c.index i) hi hj
  refine ⟨ht, fun k => ?_⟩
  rw [CompatibleStrongHom.comp_pullback f g (a.index i) (b.index i) (c.index i) hi hj]
  change f.pullback (a.index i) (b.index i) hi (g.pullback (b.index i) (c.index i) hj _) = _
  exact (congrArg (fun x => f.pullback (a.index i) (b.index i) hi x) (hgi k)).trans (hfi k)

private theorem PullsBackCoordinates.ext {f g : CompatibleStrongHom A B}
    {a : ChartCoordinates A I n} {b : ChartCoordinates B I n}
    (hf : PullsBackCoordinates f a b) (hg : PullsBackCoordinates g a b) : f = g := by
  have hmap (i : I)
      (hi : f.baseMap '' range (A.atlas.chart (a.index i)) ⊆ range (B.atlas.chart (b.index i)))
      (hj : g.baseMap '' range (A.atlas.chart (a.index i)) ⊆ range (B.atlas.chart (b.index i))) :
      f.pullback (a.index i) (b.index i) hi = g.pullback (a.index i) (b.index i) hj := by
    obtain ⟨_, hfi⟩ := hf i
    obtain ⟨_, hgi⟩ := hg i
    apply hom_ext_coordinate K _ _ _
    intro k
    obtain ⟨k', rfl⟩ := (b.position i).surjective k
    exact (hfi k').trans (hgi k').symm
  have hb : f.baseMap = g.baseMap := by
    ext x
    obtain ⟨U, ⟨j, rfl⟩, hz⟩ := mem_sUnion.mp
      (show x ∈ ⋃₀ range (fun j => range (A.atlas.chart j)) from
        A.atlas.isNet_chartFamily.1.covers.symm ▸ mem_univ x)
    obtain ⟨i, rfl⟩ := a.surjective j
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨hi, _⟩ := hf i
    obtain ⟨hj, _⟩ := hg i
    rw [← f.chart_comm (a.index i) (b.index i) hi,
      ← g.chart_comm (a.index i) (b.index i) hj, hmap i hi hj]
  refine CompatibleStrongHom.ext_of_pullback hb fun j => ?_
  obtain ⟨i, rfl⟩ := a.surjective j
  obtain ⟨hi, _⟩ := hf i
  exact ⟨b.index i, hi, hmap i hi _⟩

private theorem id_pullbackCoordinates (a : ChartCoordinates A I n) :
    PullsBackCoordinates (CompatibleStrongHom.id A) a a := by
  intro i
  refine ⟨by simp [CompatibleStrongHom.id, StrongHom.id], fun k => ?_⟩
  change (A.atlas.restriction (a.index i) (a.index i) _) _ = _
  rw [IndexedAffinoidAtlas.restriction_id]
  rfl

section Extend

variable (K)
  (L : Type u) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

private def ChartCoordinates.extend (a : ChartCoordinates A I n) :
    ChartCoordinates (presentation K L A.atlas) I n :=
  ⟨a.index, a.surjective, a.position⟩

private theorem PullsBackCoordinates.extend {f : CompatibleStrongHom A B}
    {a : ChartCoordinates A I n} {b : ChartCoordinates B I n}
    (hf : PullsBackCoordinates f a b) :
    PullsBackCoordinates (compatibleMap K L f) (a.extend K L) (b.extend K L) := by
  intro i
  obtain ⟨hi, hcoord⟩ := hf i
  refine ⟨(admissible_iff K L f.toStrongHom f.compatible (a.index i) (b.index i)).mpr hi, fun k => ?_⟩
  change map K L (f.pullback (a.index i) (b.index i) hi)
    (coordinate L (algebra K L (B.atlas.algebra (b.index i))) (b.position i k)) =
      coordinate L (algebra K L (A.atlas.algebra (a.index i))) (a.position i k)
  rw [map_coordinate, hcoord, iota_coordinate]

end Extend

section Comparisons

variable (K)
  (L : Type u) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (M : Type u) [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]

private theorem unit_pullbackCoordinates (A : AffinoidAtlasPresentation.{u, max u w, w} K)
    (a : ChartCoordinates A I n) :
    PullsBackCoordinates (unitCompatibleMap K A) (a.extend K K) a := by
  intro i
  have hi : (unitCompatibleMap K A).baseMap ''
      range ((presentation K K A.atlas).atlas.chart (a.index i)) ⊆ range (A.atlas.chart (a.index i)) :=
    (projection_image_chart K K A.atlas (a.index i)).subset
  refine ⟨hi, fun k => ?_⟩
  change (unitCompatibleMap K A).pullback (a.index i) (a.index i) hi
    (coordinate K _ (a.position i k)) = _
  rw [unitCompatibleMap_pullback_same K A (a.index i) hi]
  exact iota_coordinate K K (A.atlas.algebra (a.index i)) (a.position i k)

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

local notation "D" => presentation K M A.atlas
local notation "S" => presentation L M (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L A.atlas)
local notation "t" => towerCompatibleHom K L M A.atlas

private theorem tower_pullbackCoordinate (i : A.atlas.Index)
    (hi : (t).baseMap '' range ((D).atlas.chart i) ⊆ range ((S).atlas.chart i))
    (k : Fin (A.atlas.algebra i).arity) :
    (t).pullback i i hi (coordinate M ((S).atlas.algebra i) k) =
      coordinate M ((D).atlas.algebra i) k := by
  rw [towerCompatibleHom_pullback_same K L M A.atlas i hi]
  exact towerEquiv_coordinate K L M (A.atlas.algebra i) k

private theorem tower_pullbackCoordinates (a : ChartCoordinates A I n) :
    PullsBackCoordinates t (a.extend K M) ((a.extend K L).extend L M) := by
  intro i
  have hi : (t).baseMap '' range ((D).atlas.chart (a.index i)) ⊆ range ((S).atlas.chart (a.index i)) :=
    (towerAdmissible_iff K L M A.atlas (a.index i) (a.index i)).mpr subset_rfl
  exact ⟨hi, fun k => tower_pullbackCoordinate K L M A (a.index i) hi (a.position i k)⟩

end Comparisons

namespace CompleteField

open CompleteUltrametricField

variable {K L M N : CompleteUltrametricField.{u}}

/-- Ground-field extension before localization, in a common sufficiently large
universe of compatible charted spaces. -/
def compatibleExtend (f : K ⟶ L) :
    CompatibleAtlasPresentation.{u, max u v, max u v} K ⥤
      CompatibleAtlasPresentation.{u, max u v, max u v} L := by
  letI := f.normedAlgebra
  exact compatibleFunctor K L

/-- The identity projection before localization. -/
def compatibleExtendId (K : CompleteUltrametricField.{u}) :
    compatibleExtend.{u, v} (𝟙 K) ⟶ 𝟭 _ :=
  unitNaturalProjection K

/-- The natural comparison from direct to successive extension. -/
def compatibleExtendComp (f : K ⟶ L) (g : L ⟶ M) :
    compatibleExtend.{u, v} (f ≫ g) ≅ compatibleExtend.{u, v} f ⋙ compatibleExtend.{u, v} g := by
  letI := f.normedAlgebra
  letI := g.normedAlgebra
  letI := (f ≫ g).normedAlgebra
  letI := f.isScalarTower_comp g
  exact towerNatIso K L M

set_option maxHeartbeats 1200000 in
/-- The left unit law for the compatible scalar-extension comparisons. -/
theorem compatibleExtend_id_left (f : K ⟶ L)
    (A : CompatibleAtlasPresentation.{u, max u v, max u v} K) :
    (compatibleExtendComp.{u, v} (𝟙 K) f).hom.app A ≫
      (compatibleExtend.{u, v} f).map ((compatibleExtendId.{u, v} K).app A) =
      eqToHom (congrArg (fun e => (compatibleExtend.{u, v} e).obj A) (Category.id_comp f)) := by
  let := f.normedAlgebra
  let : IsScalarTower K K L := (𝟙 K : K ⟶ K).isScalarTower_comp f
  let P := A.presentation
  change (towerCompatibleHom K K L P.atlas).comp (compatibleMap K L (unitCompatibleMap K P)) =
    CompatibleStrongHom.id (presentation K L P.atlas)
  let a := ChartCoordinates.base P
  exact ((tower_pullbackCoordinates K K L P a).comp
    ((unit_pullbackCoordinates K P a).extend K L)).ext (id_pullbackCoordinates (a.extend K L))

set_option maxHeartbeats 1200000 in
/-- The right unit law for the compatible scalar-extension comparisons. -/
theorem compatibleExtend_id_right (f : K ⟶ L)
    (A : CompatibleAtlasPresentation.{u, max u v, max u v} K) :
    (compatibleExtendComp.{u, v} f (𝟙 L)).hom.app A ≫
      (compatibleExtendId.{u, v} L).app ((compatibleExtend.{u, v} f).obj A) =
      eqToHom (congrArg (fun e => (compatibleExtend.{u, v} e).obj A) (Category.comp_id f)) := by
  let := f.normedAlgebra
  let : IsScalarTower K L L := f.isScalarTower_comp (𝟙 L)
  let P := A.presentation
  change (towerCompatibleHom K L L P.atlas).comp (unitCompatibleMap L (presentation K L P.atlas)) =
    CompatibleStrongHom.id (presentation K L P.atlas)
  let a := ChartCoordinates.base P
  exact ((tower_pullbackCoordinates K L L P a).comp
    (unit_pullbackCoordinates L (presentation K L P.atlas) (a.extend K L))).ext
      (id_pullbackCoordinates (a.extend K L))

set_option maxHeartbeats 1500000 in
/-- The two routes from direct extension to three successive extensions agree. -/
theorem compatibleExtend_assoc (f : K ⟶ L) (g : L ⟶ M) (h : M ⟶ N)
    (A : CompatibleAtlasPresentation.{u, max u v, max u v} K) :
    (compatibleExtendComp.{u, v} (f ≫ g) h).hom.app A ≫
      (compatibleExtend.{u, v} h).map ((compatibleExtendComp.{u, v} f g).hom.app A) =
    eqToHom (congrArg (fun e => (compatibleExtend.{u, v} e).obj A) (Category.assoc f g h)) ≫
      (compatibleExtendComp.{u, v} f (g ≫ h)).hom.app A ≫
        (compatibleExtendComp.{u, v} g h).hom.app ((compatibleExtend.{u, v} f).obj A) := by
  let := f.normedAlgebra
  let := g.normedAlgebra
  let := h.normedAlgebra
  let := (f ≫ g).normedAlgebra
  let := (g ≫ h).normedAlgebra
  let := ((f ≫ g) ≫ h).normedAlgebra
  let : IsScalarTower K L M := f.isScalarTower_comp g
  let : IsScalarTower L M N := g.isScalarTower_comp h
  let : IsScalarTower K M N := (f ≫ g).isScalarTower_comp h
  let : IsScalarTower K L N := f.isScalarTower_comp (g ≫ h)
  let P := A.presentation
  let direct := presentation K N P.atlas
  change (towerCompatibleHom K M N P.atlas).comp (compatibleMap M N (towerCompatibleHom K L M P.atlas)) =
    (CompatibleStrongHom.id direct).comp
      ((towerCompatibleHom K L N P.atlas).comp (towerCompatibleHom L M N (presentation K L P.atlas).atlas))
  rw [CompatibleStrongHom.id_comp]
  let a := ChartCoordinates.base P
  exact ((tower_pullbackCoordinates K M N P a).comp
    ((tower_pullbackCoordinates K L M P a).extend M N)).ext
    ((tower_pullbackCoordinates K L N P a).comp
      (tower_pullbackCoordinates L M N (presentation K L P.atlas) (a.extend K L)))

end CompleteField

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
