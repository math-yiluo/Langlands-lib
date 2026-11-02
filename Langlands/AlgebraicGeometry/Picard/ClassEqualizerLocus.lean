import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.Picard.RelativePicardLocalRepresentatives
import Mathlib.CategoryTheory.Sites.Closed

/-! # The locus where two fppf Picard classes agree, as a sieve on a scheme

For line bundles `L` and `M` on `T ×_S X`, the morphisms `g : T' ⟶ T` along which the fppf
Picard classes of `L` and `M` agree form the fppf closure of the sieve of morphisms along which
the pullbacks of `L` and `M` are isomorphic. This file records that description as a sieve on
the underlying scheme of `T`, together with elementary facts about morphisms that cut out a
sieve.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-! ### Morphisms cutting out a sieve -/

/-- The morphism `ι : Z ⟶ Y` cuts out the sieve `E` on `Y`: a morphism `g : T ⟶ Y` factors
through `ι` exactly when `g` belongs to `E`. -/
def CutsOut {Y Z : Scheme.{u}} (ι : Z ⟶ Y) (E : Sieve Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g

namespace CutsOut

variable {Y Z : Scheme.{u}}

lemma congr_sieve {ι : Z ⟶ Y} {E E' : Sieve Y} (h : CutsOut ι E) (hE : E = E') :
    CutsOut ι E' :=
  hE ▸ h

/-- If every member of `E` factors through `j`, and `ι` cuts out the pullback of `E` along
`j`, then `ι ≫ j` cuts out `E`. -/
lemma comp {W : Scheme.{u}} {E : Sieve Y} (j : W ⟶ Y)
    (hj : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), E g → ∃ g' : T ⟶ W, g' ≫ j = g)
    {ι : Z ⟶ W} (hι : CutsOut ι (E.pullback j)) : CutsOut (ι ≫ j) E := by
  intro T g
  constructor
  · rintro ⟨k, rfl⟩
    have : (E.pullback j) (k ≫ ι) := (hι (k ≫ ι)).1 ⟨k, rfl⟩
    rw [← Category.assoc]
    exact this
  · intro hg
    obtain ⟨g', rfl⟩ := hj g hg
    obtain ⟨k, hk⟩ := (hι g').2 hg
    exact ⟨k, by rw [← Category.assoc, hk]⟩

/-- Cutting out is stable under base change. -/
lemma pullback {Y₀ Z₀ : Scheme.{u}} {E₀ : Sieve Y₀} {ι₀ : Z₀ ⟶ Y₀} (h : CutsOut ι₀ E₀)
    (φ : Y ⟶ Y₀) : CutsOut (pullback.snd ι₀ φ) (E₀.pullback φ) := by
  intro T g
  constructor
  · rintro ⟨k, rfl⟩
    exact (h _).1 ⟨k ≫ pullback.fst ι₀ φ, by simp [pullback.condition]⟩
  · intro hg
    obtain ⟨k₀, hk₀⟩ := (h (g ≫ φ)).2 hg
    exact ⟨pullback.lift k₀ g hk₀, pullback.lift_snd _ _ _⟩

end CutsOut

namespace RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-! ### The isomorphism locus on the underlying scheme -/

/-- The pullback of an isomorphism sieve is the isomorphism sieve of the pulled-back bundles. -/
lemma isomorphismSieve_pullback {T V : Over S} (φ : V ⟶ T)
    (L M : LineBundle ((relativeSpace f).obj T)) :
    (isomorphismSieve f T L M).pullback φ =
      isomorphismSieve f V ((LineBundle.pullback ((relativeSpace f).map φ)).obj L)
        ((LineBundle.pullback ((relativeSpace f).map φ)).obj M) := by
  ext W h
  change (classPresheaf f).map (h ≫ φ).op (classOf f T L) =
      (classPresheaf f).map (h ≫ φ).op (classOf f T M) ↔
    (classPresheaf f).map h.op (classOf f V _) = (classPresheaf f).map h.op (classOf f V _)
  rw [← map_classOf, ← map_classOf, op_comp, Functor.map_comp]
  rfl

/-- The sieve on the scheme `T.left` of morphisms `g` along which the pullbacks of `L` and `M`
to the fibre product are isomorphic. -/
def isoLocus (T : Over S) (L M : LineBundle ((relativeSpace f).obj T)) : Sieve T.left :=
  Sieve.overEquiv T (isomorphismSieve f T L M)

lemma isoLocus_iff {T : Over S} (L M : LineBundle ((relativeSpace f).obj T)) {T' : Scheme.{u}}
    (g : T' ⟶ T.left) :
    isoLocus f T L M g ↔
      Nonempty ((LineBundle.pullback
          ((relativeSpace f).map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T))).obj L ≅
        (LineBundle.pullback
          ((relativeSpace f).map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T))).obj M) := by
  rw [isoLocus, Sieve.overEquiv_iff, isomorphismSieve_iff]

lemma isoLocus_pullback {T V : Over S} (φ : V ⟶ T)
    (L M : LineBundle ((relativeSpace f).obj T)) :
    (isoLocus f T L M).pullback φ.left =
      isoLocus f V ((LineBundle.pullback ((relativeSpace f).map φ)).obj L)
        ((LineBundle.pullback ((relativeSpace f).map φ)).obj M) := by
  rw [isoLocus, isoLocus, ← Sieve.overEquiv_pullback, isomorphismSieve_pullback]

/-- The isomorphism locus only depends on the isomorphism classes of the bundles. -/
lemma isoLocus_congr {T : Over S} {L L' M M' : LineBundle ((relativeSpace f).obj T)}
    (eL : L ≅ L') (eM : M ≅ M') : isoLocus f T L M = isoLocus f T L' M' := by
  ext T' g
  rw [isoLocus_iff, isoLocus_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨(LineBundle.pullback _).mapIso eL.symm ≪≫ e ≪≫
      (LineBundle.pullback _).mapIso eM⟩,
    fun ⟨e⟩ ↦ ⟨(LineBundle.pullback _).mapIso eL ≪≫ e ≪≫
      (LineBundle.pullback _).mapIso eM.symm⟩⟩

/-- Two bundles are locally isomorphic exactly where the quotient bundle `L ⊗ M⁻¹` is
trivial. -/
lemma isoLocus_eq_tensor_inverse {T : Over S} (L M : LineBundle ((relativeSpace f).obj T)) :
    isoLocus f T L M =
      isoLocus f T (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
        L M.inverse) (LineBundle.trivial _) := by
  ext T' g
  rw [isoLocus, isoLocus, Sieve.overEquiv_iff, Sieve.overEquiv_iff]
  change (classPresheaf f).map _ (classOf f T L) = (classPresheaf f).map _ (classOf f T M) ↔
    (classPresheaf f).map _ (classOf f T _) = (classPresheaf f).map _ (classOf f T _)
  have key : ∀ a b : Group ((relativeSpace f).obj (Over.mk (g ≫ T.hom))), a = b ↔ a + -b = 0 :=
    fun a b ↦ add_neg_eq_zero.symm
  rw [classOf_tensor, classOf_inverse, classOf_trivial, classPresheaf_map_apply,
    classPresheaf_map_apply, classPresheaf_map_apply, classPresheaf_map_apply, map_zero,
    map_add, map_neg]
  exact key _ _

/-- Membership in the isomorphism locus of `N` and the trivial bundle means triviality of the
pullback of `N`. -/
lemma isoLocus_trivial_iff {T : Over S} (N : LineBundle ((relativeSpace f).obj T))
    {T' : Scheme.{u}} (g : T' ⟶ T.left) :
    isoLocus f T N (LineBundle.trivial _) g ↔
      Nonempty ((LineBundle.pullback
          ((relativeSpace f).map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T))).obj N ≅
        LineBundle.trivial _) := by
  rw [isoLocus_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ LineBundle.pullbackTrivialIso _⟩,
    fun ⟨e⟩ ↦ ⟨e ≪≫ (LineBundle.pullbackTrivialIso _).symm⟩⟩

/-! ### Equality of fppf classes -/

/-- The fppf Picard classes of `L` and `M` agree after restriction along `φ` exactly when the
underlying morphism of `φ` lies in the fppf closure of the isomorphism locus. -/
lemma map_sheafClassOf_eq_iff {T V : Over S} (φ : V ⟶ T)
    (L M : LineBundle ((relativeSpace f).obj T)) :
    (classSheafPresheaf f).map φ.op (sheafClassOf f T L) =
        (classSheafPresheaf f).map φ.op (sheafClassOf f T M) ↔
      Scheme.fppfTopology.close (isoLocus f T L M) φ.left := by
  rw [map_sheafClassOf, map_sheafClassOf, sheafClassOf_eq_iff_isomorphismSieve_mem,
    ← isomorphismSieve_pullback, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_pullback]
  rfl

/-- A morphism cutting out the fppf closure of the isomorphism locus cuts out the locus where
the fppf Picard classes of `L` and `M` agree. -/
theorem representsEqualizer_of_cutsOut {T : Over S} (L M : LineBundle ((relativeSpace f).obj T))
    {Z : Scheme.{u}} (ι : Z ⟶ T.left)
    (h : CutsOut ι (Scheme.fppfTopology.close (isoLocus f T L M))) :
    AlgebraicSpace.RepresentsEqualizer (F := classSheafPresheaf f)
      (Over.homMk ι : Over.mk (ι ≫ T.hom) ⟶ T) (sheafClassOf f T L) (sheafClassOf f T M) := by
  intro V φ
  rw [map_sheafClassOf_eq_iff, ← h φ.left]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.left, by simp⟩
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk k (by simp [← Over.w φ, ← hk]), ?_⟩
    ext
    simp [hk]

end RelativePicard

end Langlands.AlgebraicGeometry.Picard
