import Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesProof
import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityProof
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeTrivialityDescent
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # The theorem of the square for geometrically Picard-zero bundles over a one-point base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.OnePointSquare

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The proved tensor preservation, as a constant of the statement type. -/
theorem tensorPreservation : pullbackTensorComparisonIsIsoStatement.{u} :=
  @pullbackTensorComparisonIsIso.{u}

/-- The isomorphism class of a line bundle, for the proved tensor preservation. -/
abbrev cls {X : Scheme.{u}} (L : LineBundle X) :
    LineBundle.IsoClasses tensorPreservation X :=
  LineBundle.isoClass tensorPreservation L

/-- Pullback of isomorphism classes, for the proved tensor preservation. -/
abbrev pb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LineBundle.IsoClasses tensorPreservation Y →*
      LineBundle.IsoClasses tensorPreservation X :=
  LineBundle.pullbackHom tensorPreservation f

/-- The class `[m^*L] / ([p₁^*L] [p₂^*L])` on `A ×_S A`. -/
def squareClass (L : LineBundle A.X.left) :
    LineBundle.IsoClasses tensorPreservation (A.X ⨯ A.X).left :=
  pb ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd).left (cls L) /
    (pb (prod.fst : A.X ⨯ A.X ⟶ A.X).left (cls L) *
      pb (prod.snd : A.X ⨯ A.X ⟶ A.X).left (cls L))

/-- Pulling the square class back along a map into the product. -/
lemma pb_squareClass {Z : Over S} (a : Z ⟶ A.X ⨯ A.X) (L : LineBundle A.X.left) :
    pb a.left (squareClass A L) =
      pb ((a ≫ prod.fst) * (a ≫ prod.snd)).left (cls L) /
        (pb (a ≫ prod.fst).left (cls L) * pb (a ≫ prod.snd).left (cls L)) := by
  rw [squareClass, map_div, map_mul, LineBundle.pullbackHom_comp,
    LineBundle.pullbackHom_comp, LineBundle.pullbackHom_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul]

/-- Pulling the square class back along a pair of points. -/
lemma pb_squareClass_lift {Z : Over S} (x y : Z ⟶ A.X) (L : LineBundle A.X.left) :
    pb (prod.lift x y).left (squareClass A L) =
      pb (x * y).left (cls L) / (pb x.left (cls L) * pb y.left (cls L)) := by
  rw [pb_squareClass, prod.lift_fst, prod.lift_snd]

/-- The constant identity point pulls every class back to the trivial class. -/
lemma pb_one_left [Unique S] {Z : Over S} (L : LineBundle A.X.left) :
    pb (1 : Z ⟶ A.X).left (cls L) = 1 := by
  have e : Over.mkIdTerminal.from Z ≫ (1 : Over.mk (𝟙 S) ⟶ A.X) = (1 : Z ⟶ A.X) := by
    simp
  have h : Z.hom ≫ (1 : Over.mk (𝟙 S) ⟶ A.X).left = (1 : Z ⟶ A.X).left := by
    simpa only [Over.comp_left, Over.mkIdTerminal_from_left] using
      congrArg CommaMorphism.left e
  exact LineBundle.pullbackHom_eq_one_of_factor tensorPreservation
    Z.hom (1 : Over.mk (𝟙 S) ⟶ A.X).left h (cls L)

/-- The square class is trivial on the first axis `A × {0}`. -/
lemma squareClass_first_axis [Unique S] (L : LineBundle A.X.left) :
    pb (prod.lift (𝟙 A.X) (Over.mkIdTerminal.from A.X ≫ (1 : Over.mk (𝟙 S) ⟶ A.X))).left
      (squareClass A L) = 1 := by
  rw [pb_squareClass, prod.lift_fst, prod.lift_snd, MonObj.comp_one, mul_one,
    pb_one_left, mul_one, Over.id_left, LineBundle.pullbackHom_id, div_self']

/-- The square class is trivial on the second axis `{0} × A`. -/
lemma squareClass_second_axis [Unique S] (L : LineBundle A.X.left) :
    pb (prod.lift (Over.mkIdTerminal.from A.X ≫ (1 : Over.mk (𝟙 S) ⟶ A.X)) (𝟙 A.X)).left
      (squareClass A L) = 1 := by
  rw [pb_squareClass, prod.lift_fst, prod.lift_snd, MonObj.comp_one, one_mul,
    pb_one_left, one_mul, Over.id_left, LineBundle.pullbackHom_id, div_self']

/-- Over an algebraically closed field, a translation-invariant bundle has trivial square
class. -/
lemma squareClass_eq_one_of_algClosed {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left)
    (hL : GroupScheme.IsTranslationInvariant A.toGrp L) : squareClass A L = 1 := by
  obtain ⟨⟨i⟩, -⟩ := algClosedFieldTranslationInvariantPullbackIdentities K A L hL
  rw [squareClass, div_eq_one]
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ i)

/-- The square class of a geometrically Picard-zero bundle pulls back trivially to every
test scheme lying over a geometric point. -/
lemma pb_squareClass_geometric (L : LineBundle A.X.left) (hL : IsGeometricallyPicardZero A L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (W : Over (Spec (CommRingCat.of K))) (Ψ : (Over.map s).obj W ⟶ A.X ⨯ A.X) :
    pb Ψ.left (squareClass A L) = 1 := by
  let A' := (baseChange s).obj A
  let e := GroupScheme.baseChangePointsEquiv s A.toGrp W
  have key : ∀ x : W ⟶ A'.X,
      pb (e x).left (cls L) = pb x.left (cls (fibreLineBundle A L s)) := fun x ↦
    (LineBundle.pullbackHom_comp _ x.left (pullback.fst A.X.hom s) (cls L)).symm
  obtain ⟨a, b, rfl⟩ : ∃ a b : W ⟶ A'.X, Ψ = prod.lift (e a) (e b) :=
    ⟨e.symm (Ψ ≫ prod.fst), e.symm (Ψ ≫ prod.snd), by ext1 <;> simp⟩
  calc pb (prod.lift (e a) (e b)).left (squareClass A L)
      = pb (e a * e b).left (cls L) / (pb (e a).left (cls L) * pb (e b).left (cls L)) :=
        pb_squareClass_lift A (e a) (e b) L
    _ = pb (e (a * b)).left (cls L) / (pb (e a).left (cls L) * pb (e b).left (cls L)) := by
        have hm : e a * e b = e (a * b) := (map_mul e a b).symm
        rw [hm]
    _ = pb (a * b).left (cls (fibreLineBundle A L s)) /
          (pb a.left (cls (fibreLineBundle A L s)) * pb b.left (cls (fibreLineBundle A L s))) := by
        rw [key, key, key]
    _ = pb (prod.lift a b).left (squareClass A' (fibreLineBundle A L s)) :=
        (pb_squareClass_lift A' a b _).symm
    _ = 1 := by
        rw [squareClass_eq_one_of_algClosed A' (fibreLineBundle A L s) (hL K s)]
        exact map_one _

/-- A class that pulls back trivially gives a trivialization of the pulled-back module. -/
lemma nonempty_iso_of_pb_eq_one {X Y : Scheme.{u}} (f : X ⟶ Y) (N : LineBundle Y)
    (h : pb f (cls N) = 1) :
    Nonempty ((Scheme.Modules.pullback f).obj N.obj ≅
      Langlands.Scheme.Modules.structureSheaf X) := by
  have h' : cls ((LineBundle.pullback f).obj N) = cls (LineBundle.trivial X) := h
  obtain ⟨i⟩ := LineBundle.isoClass_eq_iff.mp h'
  exact ⟨(ObjectProperty.ι _).mapIso i⟩

/-- A representative of the square class of a geometrically Picard-zero bundle is trivial on
every fibre of `A ×_S A ⟶ S`. -/
lemma fibre_trivial (L : LineBundle A.X.left) (hL : IsGeometricallyPicardZero A L)
    (N : LineBundle (A.X ⨯ A.X).left) (hN : cls N = squareClass A L) (s : S) :
    Nonempty ((Scheme.Modules.pullback ((A.X ⨯ A.X).hom.fiberι s)).obj N.obj ≅
      Langlands.Scheme.Modules.structureSheaf ((A.X ⨯ A.X).hom.fiber s)) := by
  obtain ⟨hsm, hpr, hgc⟩ := product_geometry A.X A.X
  let k : Type u := S.residueField s
  let K : Type u := AlgebraicClosure k
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let f : (A.X ⨯ A.X).hom.fiber s ⟶ Spec (CommRingCat.of k) :=
    (A.X ⨯ A.X).hom.fiberToSpecResidueField s
  have : Smooth f := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsProper f := inferInstanceAs (IsProper (pullback.snd _ _))
  have : GeometricallyConnected f :=
    inferInstanceAs (GeometricallyConnected ((A.X ⨯ A.X).hom.fiberToSpecResidueField s))
  let s' : Spec (CommRingCat.of K) ⟶ S := g ≫ S.fromSpecResidueField s
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd f g)
  let Ψ : (Over.map s').obj W ⟶ A.X ⨯ A.X :=
    Over.homMk (pullback.fst f g ≫ (A.X ⨯ A.X).hom.fiberι s) (by
      change (pullback.fst f g ≫ (A.X ⨯ A.X).hom.fiberι s) ≫ (A.X ⨯ A.X).hom =
        pullback.snd f g ≫ g ≫ S.fromSpecResidueField s
      rw [Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc, pullback.condition,
        Category.assoc])
  have hc : pb (pullback.fst f g) (pb ((A.X ⨯ A.X).hom.fiberι s) (cls N)) = 1 := by
    rw [LineBundle.pullbackHom_comp, hN]
    exact pb_squareClass_geometric A L hL K s' W Ψ
  obtain ⟨i⟩ := nonempty_iso_of_pb_eq_one (pullback.fst f g)
    ((LineBundle.pullback ((A.X ⨯ A.X).hom.fiberι s)).obj N) hc
  exact fieldBaseChangeTrivialityDescent g f _
    ((LineBundle.pullback ((A.X ⨯ A.X).hom.fiberι s)).obj N).property ⟨i⟩

/-- **Theorem of the square over a one-point base.** If the base `S` has exactly one point
and `L` is geometrically Picard-zero on the abelian scheme `A`, then
`m^*L ≅ p₁^*L ⊗ p₂^*L` on `A ×_S A`. -/
theorem onePointSquare [Unique S] (L : LineBundle A.X.left)
    (hL : IsGeometricallyPicardZero A L) :
    let P : Over S := A.X ⨯ A.X
    let p1 : P ⟶ A.X := Limits.prod.fst
    let p2 : P ⟶ A.X := Limits.prod.snd
    let m : P ⟶ A.X := p1 * p2
    Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
      Langlands.Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback p1.left).obj L.obj)
        ((Scheme.Modules.pullback p2.left).obj L.obj)) := by
  intro P p1 p2 m
  obtain ⟨N, hN⟩ : ∃ N : LineBundle (A.X ⨯ A.X).left, cls N = squareClass A L :=
    LineBundle.IsoClasses.ind (motive := fun q ↦ ∃ N, cls N = q) (fun N ↦ ⟨N, rfl⟩) _
  have h1 := nonempty_iso_of_pb_eq_one _ N (by rw [hN]; exact squareClass_first_axis A L)
  have h2 := nonempty_iso_of_pb_eq_one _ N (by rw [hN]; exact squareClass_second_axis A L)
  have h3 := fibre_trivial A L hL N hN default
  obtain ⟨U, hU, ⟨e⟩⟩ := localTwoAxisTriviality S A.X A.X inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance 1 1 N default h1 h2 h3
  obtain rfl : U = ⊤ := by
    ext x
    rw [Subsingleton.elim x default]
    exact ⟨fun _ ↦ trivial, fun _ ↦ hU⟩
  have : IsIso (⊤ : S.Opens).ι := inferInstanceAs (IsIso S.topIso.hom)
  obtain ⟨e'⟩ := nonempty_iso_structureSheaf_of_pullback_isIso _ e
  have hsq : squareClass A L = 1 := by
    rw [← hN]
    exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ e')
  rw [squareClass, div_eq_one] at hsq
  obtain ⟨i⟩ := LineBundle.isoClass_eq_iff.mp hsq
  exact ⟨(ObjectProperty.ι _).mapIso i⟩

/-- **Theorem of the square over a local Artinian base.** For a local Artinian ring `B` and a
geometrically Picard-zero line bundle `L` on an abelian scheme `A` over `Spec B`,
`m^*L ≅ p₁^*L ⊗ p₂^*L` on `A ×_B A`. -/
theorem artinianLocalSquare (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (A : AbelianScheme (Spec (CommRingCat.of B))) (L : LineBundle A.X.left)
    (hL : IsGeometricallyPicardZero A L) :
    let P : Over (Spec (CommRingCat.of B)) := A.X ⨯ A.X
    let p1 : P ⟶ A.X := Limits.prod.fst
    let p2 : P ⟶ A.X := Limits.prod.snd
    let m : P ⟶ A.X := p1 * p2
    Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
      Langlands.Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback p1.left).obj L.obj)
        ((Scheme.Modules.pullback p2.left).obj L.obj)) :=
  haveI : Unique (Spec (CommRingCat.of B)) := inferInstanceAs (Unique (PrimeSpectrum B))
  onePointSquare A L hL

end Langlands.AbelianScheme.OnePointSquare
