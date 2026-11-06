import Langlands.GroupScheme.Rational.RegularConjugateFiniteGaloisStatement
import Langlands.GroupScheme.Rational.RegularConjugateCentralizerTorus
import Langlands.GroupScheme.ConjugacyTransporter
import Langlands.GroupScheme.Torus.Geometry
import Langlands.AlgebraicGeometry.SmoothFiniteGaloisPoint

/-! # Proof: finite Galois conjugacy to a point with toral centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Finite Galois conjugacy to a point with toral centralizer.** The centralizer of `x` is a
closed subgroup scheme, and a torus because over `E` it becomes isomorphic to the torus
`S_E`. The transporter from `x` to `z` is a scheme over `Spec L`; over `E` it is a translate of
the centralizer, hence smooth, so by fpqc descent it is smooth over `L` and therefore over `K`.
It is affine and nonempty, so it has a point over a finite Galois extension `L'/K`. -/
theorem regularConjugateFiniteGalois : RegularConjugateFiniteGaloisStatement.{u} := by
  intro K L _ _ _ _ _ G hG z S j hS hj hC x E _ _ q g hg
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, i, hi, hic⟩ := G.pointCentralizer_isClosedRepresentable x
  have hT : IsTorus T := isTorus_of_isRepresentedBy_pointCentralizer hS
    (isRepresentedBy_pointCentralizer_of_le _ hS hj hC) q g hg hi
  refine ⟨T, i, hT, hic, fun {Z} c hc => ?_, ?_⟩
  · have hc' : c ∈ (G.pointCentralizer x).carrier Z := (mem_pointCentralizer G x c).mpr hc
    rw [← hi.2] at hc'
    exact SubgroupFunctor.mem_range.mp hc'
  have : Smooth T.X.hom := hT.smooth
  -- The transporter over `E` is smooth, and descends along `Spec E ⟶ Spec L`.
  have hp' : Smooth (pullback.fst (q ≫ z) (G.conjugationOrbitMap x)).left :=
    smooth_transporter_fst_left hi g hg
  let : Algebra L E := (Spec.preimage q.left).hom.toAlgebra
  have hc : Spec.map (CommRingCat.ofHom (algebraMap L E)) = q.left := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc L E
  rw [hc] at h1 h2 h3
  have hp : Smooth (pullback.fst z (G.conjugationOrbitMap x)).left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((isPullback_pullback_comp q z (G.conjugationOrbitMap x)).map (Over.forget _))
      ⟨⟨h1, h2⟩, h3⟩ hp'
  -- The transporter is smooth over `K`, since `L` is étale over `K`.
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Smooth K L := {}
  have hKL : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : Smooth (pullback z (G.conjugationOrbitMap x)).hom := by
    rw [← Over.w (pullback.fst z (G.conjugationOrbitMap x))]
    exact MorphismProperty.comp_mem @Smooth _ _ hp hKL
  -- The transporter is affine and nonempty.
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))).left :=
    show IsAffine (Spec (CommRingCat.of L)) from inferInstance
  have : IsAffineHom (pullback.fst z (G.conjugationOrbitMap x)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback z (G.conjugationOrbitMap x)).map (Over.forget _)).flip
      (inferInstance : IsAffineHom (G.conjugationOrbitMap x).left)
  have : IsAffine (pullback z (G.conjugationOrbitMap x)).left :=
    isAffine_of_isAffineHom (pullback.fst z (G.conjugationOrbitMap x)).left
  let s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
      pullback z (G.conjugationOrbitMap x) :=
    pullback.lift q g (by rw [comp_conjugationOrbitMap, hg])
  let e0 : Spec (CommRingCat.of E) := (⟨⊥, inferInstance⟩ : PrimeSpectrum E)
  have : Nonempty (pullback z (G.conjugationOrbitMap x)).left := ⟨s.left e0⟩
  -- A point of the transporter over a finite Galois extension.
  obtain ⟨L', _, _, _, _, σ, hσ⟩ := Langlands.AlgebraicGeometry.exists_finiteGalois_point_of_smooth
    K (pullback z (G.conjugationOrbitMap x)).hom
  let σ' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶
      pullback z (G.conjugationOrbitMap x) := Over.homMk σ hσ
  refine ⟨L', inferInstance, inferInstance, inferInstance, inferInstance,
    σ' ≫ pullback.fst _ _, σ' ≫ pullback.snd _ _, ?_⟩
  rw [← comp_conjugationOrbitMap, Category.assoc, ← pullback.condition, Category.assoc]

end Langlands.GroupScheme
