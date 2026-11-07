import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.AlgebraicGeometry.Picard.PointFiberTestReduction
import Langlands.AlgebraicGeometry.Picard.PointFiberChartRestriction

/-! # Artinian lifting for representing schemes of versal point fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.PointFiberArtinianLifting

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {U : Over (Spec (CommRingCat.of R))} (L : LineBundle ((relativeSpace f).obj U))

/-- The iterated slice of the underlying arrow of a slice arrow is that arrow. -/
def sliceIso {T W : Over (Spec (CommRingCat.of R))} (b : W ⟶ T) :
    T.iteratedSliceBackward.obj (Over.mk b.left) ≅ Over.mk b :=
  Over.isoMk (Over.isoMk (Iso.refl _) (by dsimp [Over.iteratedSliceBackward]; simp [Over.w b]))
    (by ext; dsimp [Over.iteratedSliceBackward]; simp)

variable {T : Over (Spec (CommRingCat.of R))} {M : LineBundle ((relativeSpace f).obj T)}
  {P : Over T.left}
  (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M)

/-- A raw fibre point as an element of the lifted point-fibre presheaf. -/
def toPresheaf {Z : Over T.left} (z : PointFiberPoints f L M Z) :
    (pointFiberPresheaf f L M).obj (op Z) :=
  ULift.up z

/-- The fibre point of a scheme map into the representing scheme. -/
def pointOf {W : Over (Spec (CommRingCat.of R))} (b : W ⟶ T) (α : W.left ⟶ P.left)
    (hα : α ≫ P.hom = b.left) :
    PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk M) (Over.mk b) :=
  PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M) (sliceIso b).inv
    (e.hom.app (op (Over.mk b.left)) (ULift.up (Over.homMk α hα))).down

/-- The scheme map into the representing scheme of a fibre point. -/
def mapOf {W : Over (Spec (CommRingCat.of R))} (a : W ⟶ T)
    (x : PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk M) (Over.mk a)) :
    Over.mk a.left ⟶ P :=
  (e.inv.app (op (Over.mk a.left)) (toPresheaf f L
    (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
      (sliceIso a).hom x))).down

/-- Restricting a lifted point recovers the original scheme map. -/
lemma map_mapOf {W W' : Over (Spec (CommRingCat.of R))} (a : W ⟶ T) (r : W' ⟶ W)
    (α : W'.left ⟶ P.left) (hα : α ≫ P.hom = (r ≫ a).left)
    (x : PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk M) (Over.mk a))
    (hx : PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
      (Over.homMk r rfl : Over.mk (r ≫ a) ⟶ Over.mk a) x = pointOf f L e (r ≫ a) α hα) :
    r.left ≫ (mapOf f L e a x).left = α := by
  let r' : Over.mk (r ≫ a).left ⟶ Over.mk a.left := Over.homMk r.left (by simp)
  have hinv : ∀ w, e.inv.app _ (e.hom.app (op (Over.mk (r ≫ a).left)) w) = w := fun w ↦ by
    rw [← CategoryTheory.comp_apply, Iso.hom_inv_id_app, CategoryTheory.id_apply]
  have hrest : PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
      (T.iteratedSliceBackward.map r')
      (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
        (sliceIso a).hom x) =
      (e.hom.app (op (Over.mk (r ≫ a).left)) (ULift.up (Over.homMk α hα))).down := by
    rw [← PseudofunctorPointFiber.restrict_comp]
    have hm : T.iteratedSliceBackward.map r' ≫ (sliceIso a).hom =
        (sliceIso (r ≫ a)).hom ≫ (Over.homMk r rfl : Over.mk (r ≫ a) ⟶ Over.mk a) := by
      ext
      dsimp [sliceIso, Over.iteratedSliceBackward, r']
      simp
    rw [hm, PseudofunctorPointFiber.restrict_comp, hx, pointOf,
      ← PseudofunctorPointFiber.restrict_comp, Iso.hom_inv_id,
      PseudofunctorPointFiber.restrict_id]
  have key : r' ≫ mapOf f L e a x = Over.homMk α hα := by
    have h1 := NatTrans.naturality_apply e.inv r'.op (toPresheaf f L
      (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M) (sliceIso a).hom x))
    change e.inv.app _ (toPresheaf f L (PseudofunctorPointFiber.restrict (relative f) (Core.mk L)
      (Core.mk M) (T.iteratedSliceBackward.map r') _)) = _ at h1
    have h2 : e.inv.app (op (Over.mk (r ≫ a).left))
        (e.hom.app _ (ULift.up (Over.homMk α hα))) =
        ((AlgebraicSpace.schemeYoneda T.left).obj P).map r'.op
          (e.inv.app _ (toPresheaf f L (PseudofunctorPointFiber.restrict (relative f) (Core.mk L)
            (Core.mk M) (sliceIso a).hom x))) := by
      rw [← h1]
      congr 1
      exact (congrArg (toPresheaf f L) hrest).symm
    rw [hinv] at h2
    exact (congrArg ULift.down h2).symm
  exact congrArg CommaMorphism.left key

include e in
/-- Formal versality at every locally finite-type field point of the family
gives Artinian lifting for every representing scheme over a locally
finite-type test. -/
theorem liftsArtinian_of_versal [LocallyOfFiniteType P.hom] [LocallyOfFiniteType T.hom]
    (hV : ∀ (K : Type u) [Field K] [Algebra R K] (p : ArtinianTest.residueBase R K ⟶ U),
      LocallyOfFiniteType p.left → ArtinianChartVersality.IsFormallyVersalAt f L p) :
    ArtinianLiftingSmooth.LiftsArtinian P.hom := by
  intro B' B _ _ _ _ _ _ φ hφ hel α β hαβ hlft
  let ρ' : CommRingCat.of R ⟶ CommRingCat.of B' := Spec.preimage (β ≫ T.hom)
  let : Algebra R B' := ρ'.hom.toAlgebra
  let : Algebra R B := (φ.comp ρ'.hom).toAlgebra
  let φₐ : B' →ₐ[R] B := { φ with commutes' := fun _ ↦ rfl }
  let εB : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hεB : Function.Surjective εB := residue_surjective
  let A := ArtinianTest.mk B' (εB.comp φₐ) (hεB.comp hφ)
  let Bt := ArtinianTest.mk B εB hεB
  let q : A ⟶ Bt := ArtinianTest.homMk φₐ rfl
  have hq : Function.Surjective (ArtinianTest.toAlgHom q) := hφ
  have hβ : β ≫ T.hom = (ArtinianTest.base A).hom := by
    change β ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap R B'))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let a : ArtinianTest.base A ⟶ T := Over.homMk β hβ
  let b : ArtinianTest.base Bt ⟶ T := ArtinianTest.baseMap q ≫ a
  have hαb : α ≫ P.hom = b.left := hαβ
  let y := pointOf f L e b α hαb
  let p := ArtinianTest.reduction Bt ≫ y.1
  have hp : LocallyOfFiniteType p.left := by
    have h1 : p.left ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField B))) :=
      Over.w p
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField B))) =
        (Spec.map (CommRingCat.ofHom (residue B)) ≫ α) ≫ P.hom ≫ T.hom := by
      rw [Category.assoc, reassoc_of% hαβ, ← Spec.map_preimage (β ≫ T.hom), ← Spec.map_comp,
        ← Spec.map_comp]
      rfl
    have : LocallyOfFiniteType (p.left ≫ U.hom) := by
      rw [h1, h2]
      infer_instance
    exact locallyOfFiniteType_of_comp p.left U.hom
  obtain ⟨x, hx⟩ := hV (ResidueField B) p hp q hq T M a b rfl y rfl
  exact ⟨(mapOf f L e a x).left, Over.w (mapOf f L e a x),
    map_mapOf f L e a (ArtinianTest.baseMap q) α hαb x hx⟩

/-- Versality at every locally finite-type field point of a locally finite-type
family makes every representing scheme of every actual point fibre smooth. -/
theorem pointFiberProperty_smooth_of_versal [IsNoetherianRing R]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType U.hom]
    (hV : ∀ (K : Type u) [Field K] [Algebra R K] (p : ArtinianTest.residueBase R K ⟶ U),
      LocallyOfFiniteType p.left → ArtinianChartVersality.IsFormallyVersalAt f L p)
    (T : Over (Spec (CommRingCat.of R))) (M : LineBundle ((relativeSpace f).obj T)) :
    PointFiberProperty f L @Smooth T M := by
  refine PointFiberProperty.of_finiteTypeAffine (fun B _ _ _ M ↦ ?_) T M
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : LocallyOfFinitePresentation U.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  obtain ⟨I, ⟨e⟩, -, -, hfp⟩ := exists_locallyOfFinitePresentation_pointFiberScheme f L M
  refine ⟨_, ⟨e⟩, ?_⟩
  have : LocallyOfFiniteType (affineBase R B).hom :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr ‹Algebra.FiniteType R B›)
  have : IsLocallyNoetherian (affineBase R B).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of B)))
  exact ArtinianLiftingSmooth.smooth_of_liftsArtinian _ (liftsArtinian_of_versal f L e hV)

/-- Versality at every locally finite-type field point of a locally finite-type
family gives smooth scheme representations of all actual point fibres. -/
theorem exists_smooth_pointFiberScheme_of_versal [IsNoetherianRing R]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType U.hom]
    (hV : ∀ (K : Type u) [Field K] [Algebra R K] (p : ArtinianTest.residueBase R K ⟶ U),
      LocallyOfFiniteType p.left → ArtinianChartVersality.IsFormallyVersalAt f L p)
    (T : Over (Spec (CommRingCat.of R))) (M : LineBundle ((relativeSpace f).obj T)) :
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf f L M) ∧
        Smooth P.hom := by
  obtain ⟨I, ⟨e⟩, -, -⟩ := hasAffinePointFiberSchemes f U T L M
  exact ⟨_, ⟨e⟩, pointFiberProperty_smooth_of_versal f L hV T M _ ⟨e⟩⟩

/-- Versality at a point passes to the restriction of the family along an open
immersion through which the point factors. -/
theorem isFormallyVersalAt_restrictBundle {V : Over (Spec (CommRingCat.of R))} (ι : V ⟶ U)
    [IsOpenImmersion ι.left] {K : Type u} [Field K] [Algebra R K]
    (p : ArtinianTest.residueBase R K ⟶ V)
    (h : ArtinianChartVersality.IsFormallyVersalAt f L (p ≫ ι)) :
    ArtinianChartVersality.IsFormallyVersalAt f (restrictBundle f L ι) p := by
  have : Mono ι := Over.mono_of_mono_left ι
  intro A B q hq T M a b w y hy
  let y' := PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι (Core.mk L)
    (Core.mk M) (Over.mk b) y
  have hy' : ArtinianTest.reduction B ≫ y'.1 = p ≫ ι := by
    change ArtinianTest.reduction B ≫ y.1 ≫ ι = p ≫ ι
    rw [← Category.assoc, hy]
  obtain ⟨x', hx'⟩ := h q hq T M a b w y' hy'
  have hres := ArtinianChartVersality.residueMap_of_restrict_eq f L q M w hx'
  rcases x' with ⟨a', d'⟩
  have hrange : Set.range a'.left ⊆ Set.range ι.left := by
    rintro _ ⟨z, rfl⟩
    have : Unique (PrimeSpectrum A.algebra) := PrimeSpectrum.unique_of_ringKrullDimLE_zero
    let c : (ArtinianTest.residueBase R K).left := (default : PrimeSpectrum K)
    have hz : z = (ArtinianTest.reduction A).left c :=
      Subsingleton.elim (α := PrimeSpectrum A.algebra) _ _
    have hc := congrArg (fun φ : ArtinianTest.residueBase R K ⟶ U ↦ φ.left c) (hres.trans hy')
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hc
    exact ⟨p.left c, by rw [hz]; exact hc.symm⟩
  obtain ⟨g, hg⟩ : ∃ g : ArtinianTest.base A ⟶ V, g ≫ ι = a' :=
    ⟨Over.homMk (IsOpenImmersion.lift ι.left a'.left hrange) (by
      rw [← Over.w ι, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w a'), by
      ext
      exact IsOpenImmersion.lift_fac _ _ _⟩
  subst hg
  refine ⟨⟨g, (PseudofunctorPointFiberAtlasRestriction.atlasComparison (relative f) ι (Core.mk L)
    g).symm ≪≫ d'⟩, ?_⟩
  apply PseudofunctorPointFiberAtlasRestriction.mapPoints_injective (relative f) ι (Core.mk L)
    (Core.mk M) (Over.mk b)
  change PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι (Core.mk L)
    (Core.mk M) (Over.mk b) (PseudofunctorPointFiber.restrict (relative f) _ (Core.mk M)
      (ArtinianChartLifting.testArrow q w) _) = y'
  rw [PseudofunctorPointFiberAtlasRestriction.mapPoints_restrict]
  have hmap : PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) ι (Core.mk L)
      (Core.mk M) (Over.mk a) ⟨g, (PseudofunctorPointFiberAtlasRestriction.atlasComparison
        (relative f) ι (Core.mk L) g).symm ≪≫ d'⟩ = ⟨g ≫ ι, d'⟩ := by
    simp [PseudofunctorPointFiberAtlasRestriction.mapPoints]
  rw [hmap]
  exact hx'

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.PointFiberArtinianLifting
