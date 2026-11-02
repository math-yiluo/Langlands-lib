import Langlands.AlgebraicGeometry.AlgebraicSpace.SpecFieldPoints
import Langlands.AlgebraicGeometry.Picard.ClassEqualizerLocus
import Langlands.AlgebraicGeometry.Picard.FieldPicardClassEqualizerImmersionStatement
import Langlands.AlgebraicGeometry.Descent.FppfImmersionLocusDescent
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas

/-! # Reducing the class equalizer immersion to Noetherian affine bases

The locus where a line bundle on `T ×_S X` becomes trivial fppf-locally is a sieve on the
scheme `T`. This file shows that the property "this locus is cut out by an immersion" is stable
under base change, descends along fppf coverings, and therefore reduces to affine `T`. Over a
field it further reduces to spectra of Noetherian algebras, by spreading out line bundles to
finitely generated subalgebras.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-! ### The fppf triviality locus -/

/-- The sieve on `T.left` of morphisms along which `N` becomes trivial fppf-locally. -/
def trivialLocus (T : Over S) (N : LineBundle ((relativeSpace f).obj T)) : Sieve T.left :=
  Scheme.fppfTopology.close (isoLocus f T N (LineBundle.trivial _))

lemma trivialLocus_isClosed (T : Over S) (N : LineBundle ((relativeSpace f).obj T)) :
    Scheme.fppfTopology.IsClosed (trivialLocus f T N) :=
  Scheme.fppfTopology.close_isClosed _

lemma trivialLocus_congr {T : Over S} {N N' : LineBundle ((relativeSpace f).obj T)}
    (e : N ≅ N') : trivialLocus f T N = trivialLocus f T N' := by
  rw [trivialLocus, trivialLocus, isoLocus_congr f e (Iso.refl _)]

lemma trivialLocus_pullback {T V : Over S} (φ : V ⟶ T) (N : LineBundle ((relativeSpace f).obj T)) :
    (trivialLocus f T N).pullback φ.left =
      trivialLocus f V ((LineBundle.pullback ((relativeSpace f).map φ)).obj N) := by
  rw [trivialLocus, trivialLocus, ← GrothendieckTopology.pullback_close, isoLocus_pullback,
    isoLocus_congr f (Iso.refl _) (LineBundle.pullbackTrivialIso _)]

/-! ### Immersions cutting out the triviality locus -/

/-- The fppf triviality locus of `N` is cut out by an immersion into `T.left`. -/
def HasImmersionLocus (T : Over S) (N : LineBundle ((relativeSpace f).obj T)) : Prop :=
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ T.left), IsImmersion ι ∧ CutsOut ι (trivialLocus f T N)

namespace HasImmersionLocus

/-- The property is stable under base change along morphisms of `Over S`. -/
lemma of_pullback {T V : Over S} (φ : V ⟶ T) {N₀ : LineBundle ((relativeSpace f).obj T)}
    {N : LineBundle ((relativeSpace f).obj V)}
    (e : (LineBundle.pullback ((relativeSpace f).map φ)).obj N₀ ≅ N)
    (h : HasImmersionLocus f T N₀) : HasImmersionLocus f V N := by
  obtain ⟨Z, ι, hι, hcut⟩ := h
  refine ⟨_, pullback.snd ι φ.left, inferInstance, ?_⟩
  rw [← trivialLocus_congr f e, ← trivialLocus_pullback]
  exact hcut.pullback φ.left

/-- Transport along a morphism with a retraction. -/
lemma of_retraction {T V : Over S} (φ : T ⟶ V) (ψ : V ⟶ T) (hφψ : φ ≫ ψ = 𝟙 T)
    (N : LineBundle ((relativeSpace f).obj T))
    (h : HasImmersionLocus f V ((LineBundle.pullback ((relativeSpace f).map ψ)).obj N)) :
    HasImmersionLocus f T N :=
  of_pullback f φ (LineBundle.pullbackCompEqIso _ _
    (by rw [← Functor.map_comp, hφψ, CategoryTheory.Functor.map_id]) N ≪≫
      (LineBundle.pullbackId _).app N) h

/-- The property descends along fppf coverings of `T.left`. -/
theorem of_cover {T : Over S} (N : LineBundle ((relativeSpace f).obj T)) (R : Sieve T.left)
    (hR : R ∈ Scheme.fppfTopology T.left)
    (h : ∀ ⦃V : Scheme.{u}⦄ (g : V ⟶ T.left), R g →
      HasImmersionLocus f (Over.mk (g ≫ T.hom))
        ((LineBundle.pullback
          ((relativeSpace f).map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T))).obj N)) :
    HasImmersionLocus f T N := by
  refine fppfImmersionLocusDescent T.left (trivialLocus f T N) (trivialLocus_isClosed f T N) R hR
    (fun V g hg ↦ ?_)
  obtain ⟨Z, ι, hι, hcut⟩ := h g hg
  refine ⟨Z, ι, hι, fun T' g' ↦ ?_⟩
  rw [hcut g', ← trivialLocus_pullback f (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T) N]
  rfl

/-- It suffices to treat bases with affine underlying scheme. -/
theorem of_isAffine
    (h : ∀ (T : Over S) [IsAffine T.left] (N : LineBundle ((relativeSpace f).obj T)),
      HasImmersionLocus f T N)
    (T : Over S) (N : LineBundle ((relativeSpace f).obj T)) : HasImmersionLocus f T N := by
  let 𝒰 := T.left.affineCover
  refine of_cover f N (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f)) ?_ ?_
  · apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ 𝒰.exists_eq x |>.imp fun i ⟨y, hy⟩ ↦ ⟨y, hy⟩,
      fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  · rintro V _ ⟨W, a, b, ⟨i⟩, rfl⟩
    have : IsAffine (Over.mk (𝒰.f i ≫ T.hom)).left := Scheme.isAffine_affineCover T.left i
    have hi := h (Over.mk (𝒰.f i ≫ T.hom))
      ((LineBundle.pullback
        ((relativeSpace f).map (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))).obj N)
    refine of_pullback f
      (Over.homMk a (by simp) : Over.mk ((a ≫ 𝒰.f i) ≫ T.hom) ⟶ Over.mk (𝒰.f i ≫ T.hom))
      (LineBundle.pullbackCompEqIso _ _ ?_ N) hi
    rw [← Functor.map_comp]
    rfl

/-! ### Spreading out over a field -/

section Field

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- Over a field, an affine base may be replaced by the spectrum of a `k`-algebra. -/
theorem of_isAffine_of_algebra
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (N : LineBundle ((relativeSpace X.hom).obj (specOver k A))),
      HasImmersionLocus X.hom (specOver k A) N)
    (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left]
    (N : LineBundle ((relativeSpace X.hom).obj T)) : HasImmersionLocus X.hom T N := by
  let φ : CommRingCat.of k ⟶ Γ(T.left, ⊤) := Spec.preimage (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra k Γ(T.left, ⊤) := φ.hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k Γ(T.left, ⊤))) =
      T.left.isoSpec.inv ≫ T.hom := by
    change Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let a : T ⟶ specOver k Γ(T.left, ⊤) :=
    Over.homMk (T.left.isoSpec.hom : T.left ⟶ Spec (CommRingCat.of Γ(T.left, ⊤)))
      (by simp [hspec])
  let b : specOver k Γ(T.left, ⊤) ⟶ T :=
    Over.homMk (T.left.isoSpec.inv : Spec (CommRingCat.of Γ(T.left, ⊤)) ⟶ T.left)
      (by simp [hspec])
  exact of_retraction X.hom a b (by ext; simp [a, b]) N (h _ _)

/-- Over a field, it suffices to treat spectra of Noetherian algebras. -/
theorem of_noetherian [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (h : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra k B]
      (N : LineBundle ((relativeSpace X.hom).obj (specOver k B))),
      HasImmersionLocus X.hom (specOver k B) N)
    (A : Type u) [CommRing A] [Algebra k A]
    (N : LineBundle ((relativeSpace X.hom).obj (specOver k A))) :
    HasImmersionLocus X.hom (specOver k A) N := by
  have hpb : IsPullback (pullback.snd (specOver k A).hom X.hom)
      (pullback.fst (specOver k A).hom X.hom) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    (IsPullback.of_hasPullback _ _).flip
  obtain ⟨B, hBfg, -, M₀, hM₀, hc⟩ :=
    NoetherianApproximation.lineBundleSubalgebraDescent X.hom (pullback.snd _ _)
      (pullback.fst _ _) hpb N.obj N.property ∅
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hBfg
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let φ : specOver k A ⟶ specOver k B :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap B A))) (by
      simp only [Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  let N₀ : LineBundle ((relativeSpace X.hom).obj (specOver k B)) :=
    (LineBundle.pullback (pullbackSymmetry (specOver k B).hom X.hom).hom).obj ⟨M₀, hM₀⟩
  have hc₁ : ((relativeSpace X.hom).map φ ≫ (pullbackSymmetry (specOver k B).hom X.hom).hom) ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k B))) =
        pullback.snd (specOver k A).hom X.hom := by
    rw [Category.assoc]
    erw [pullbackSymmetry_hom_comp_fst]
    exact relativeSpace_map_snd _ _
  have hc₂ : ((relativeSpace X.hom).map φ ≫ (pullbackSymmetry (specOver k B).hom X.hom).hom) ≫
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k B))) =
        pullback.fst (specOver k A).hom X.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
    rw [Category.assoc]
    erw [pullbackSymmetry_hom_comp_snd]
    simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left, φ,
      Over.homMk_left]
    exact pullback.lift_fst _ _ _
  obtain ⟨e⟩ := hc _ hc₁ hc₂
  exact of_pullback X.hom φ
    (LineBundle.pullbackCompEqIso ((relativeSpace X.hom).map φ)
      (pullbackSymmetry (specOver k B).hom X.hom).hom rfl ⟨M₀, hM₀⟩ ≪≫
        ObjectProperty.isoMk _ e) (h B N₀)

end Field

end HasImmersionLocus

open HasImmersionLocus in
/-- `FieldPicardClassEqualizerImmersionStatement` follows from its special case for the
triviality locus over spectra of Noetherian algebras. -/
theorem fieldPicardClassEqualizerImmersion_of_noetherian
    (h : ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))), IsProper X.hom →
      ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra k B]
        (N : LineBundle ((relativeSpace X.hom).obj (specOver k B))),
        HasImmersionLocus X.hom (specOver k B) N) :
    FieldPicardClassEqualizerImmersionStatement.{u} := by
  intro k _ X hX T L M
  have := hX
  obtain ⟨Z, ι, hι, hcut⟩ := of_isAffine X.hom
    (fun T' _ N' ↦ of_isAffine_of_algebra X (of_noetherian X (h k X hX)) T' N') T
    (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L M.inverse)
  refine ⟨Over.mk (ι ≫ T.hom), Over.homMk ι, hι, representsEqualizer_of_cutsOut X.hom L M ι ?_⟩
  rw [isoLocus_eq_tensor_inverse]
  exact hcut

end RelativePicard

end Langlands.AlgebraicGeometry.Picard
