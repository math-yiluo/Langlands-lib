import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionEtale
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module

/-! # Surjectivity of actual affine-chart Weil restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Algebra

/-- A formally smooth algebra maps to an Artinian algebra as soon as it maps to every
residue field of the reduced quotient. -/
theorem nonempty_algHom_of_isArtinianRing {B C D : Type u} [CommRing B] [CommRing C]
    [CommRing D] [Algebra B C] [Algebra B D] [Algebra.FormallySmooth B C] [IsArtinianRing D]
    (h : ∀ I : MaximalSpectrum (D ⧸ nilradical D),
      Nonempty (C →ₐ[B] (D ⧸ nilradical D) ⧸ I.asIdeal)) :
    Nonempty (C →ₐ[B] D) := by
  classical
  let N := nilradical D
  have : IsReduced (D ⧸ N) :=
    (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical ⊥)
  let e : (D ⧸ N) ≃ₐ[B] ∀ I : MaximalSpectrum (D ⧸ N), (D ⧸ N) ⧸ I.asIdeal :=
    (IsArtinianRing.equivPi (D ⧸ N)).restrictScalars B
  let f : C →ₐ[B] ∀ I : MaximalSpectrum (D ⧸ N), (D ⧸ N) ⧸ I.asIdeal :=
    AlgHom.pi fun I => (h I).some
  exact ⟨Algebra.FormallySmooth.lift N IsArtinianRing.isNilpotent_nilradical
    (e.symm.toAlgHom.comp f)⟩

end Langlands.Algebra

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- A scheme locally of finite type has a point with values in an algebraically closed
field over every point of the base hit by the scheme. -/
theorem nonempty_ringPoint_of_isAlgClosed (R : Type u) [CommRing R]
    (Y : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType Y.hom]
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L] (y : Y.left)
    (hy : Y.hom y = Spec.algebraMap R L (IsLocalRing.closedPoint L)) :
    Nonempty (RingPoint R Y L) := by
  let g := Spec.algebraMap R L
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.hom) (g := g) y
    (IsLocalRing.closedPoint L) hy
  have : JacobsonSpace (pullback Y.hom g).carrier :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd Y.hom g)
  obtain ⟨w, -, hw⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z, Set.mem_univ z⟩
    isClosed_univ.isLocallyClosed
  let s := pointOfClosedPoint (pullback.snd Y.hom g) w hw
  refine ⟨Over.homMk (s ≫ pullback.fst Y.hom g) ?_⟩
  change (s ≫ pullback.fst Y.hom g) ≫ Y.hom = g
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

/-- Every point of an affine spectrum is the image of the closed point of an algebraically
closed field. -/
theorem exists_isAlgClosed_point (A : Type u) [CommRing A] (t : Spec (CommRingCat.of A)) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra A K),
      Spec.algebraMap A K (IsLocalRing.closedPoint K) = t := by
  let κ := (Spec (CommRingCat.of A)).residueField t
  let K := AlgebraicClosure κ
  let φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField t
  let : Algebra A K := (Spec.preimage φ).hom.toAlgebra
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  have hφ : Spec.algebraMap A K = φ := Spec.map_preimage φ
  rw [hφ]
  change ((Spec (CommRingCat.of A)).fromSpecResidueField t)
    ((Spec.map (CommRingCat.ofHom (algebraMap κ K))) (IsLocalRing.closedPoint K)) = t
  rw [Subsingleton.elim ((Spec.map (CommRingCat.ofHom (algebraMap κ K)))
    (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint κ)]
  exact Scheme.fromSpecResidueField_apply t _

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The glued affine-chart Weil restriction of a quasi-affine étale surjective scheme is
surjective. -/
theorem affineChartWeilRestriction_surjective (Y : Over (Spec (CommRingCat.of B)))
    [LocallyOfFiniteType Y.hom] [Y.left.IsQuasiAffine] [Etale Y.hom] [Surjective Y.hom] :
    Surjective (affineChartWeilRestriction A B Y).hom := by
  classical
  constructor
  intro t
  obtain ⟨K, _, _, _, ht⟩ := exists_isAlgClosed_point A t
  let D := B ⊗[A] K
  have : IsArtinianRing (K ⊗[A] B) := isArtinian_of_tower K inferInstance
  have : IsArtinianRing D := (Algebra.TensorProduct.comm A K B).toRingEquiv.isArtinianRing
  let N := nilradical D
  let (I : MaximalSpectrum (D ⧸ N)) : Field ((D ⧸ N) ⧸ I.asIdeal) :=
    Ideal.Quotient.field I.asIdeal
  have hclosed : ∀ I : MaximalSpectrum (D ⧸ N), IsAlgClosed ((D ⧸ N) ⧸ I.asIdeal) := by
    intro I
    let φ : K →+* (D ⧸ N) ⧸ I.asIdeal :=
      (Ideal.Quotient.mk I.asIdeal).comp ((Ideal.Quotient.mk N).comp
        ((Algebra.TensorProduct.comm A K B).toRingEquiv.toRingHom.comp
          (algebraMap K (K ⊗[A] B))))
    have hφ : φ.IsIntegral := by
      refine RingHom.IsIntegral.trans _ (Ideal.Quotient.mk I.asIdeal)
        (RingHom.IsIntegral.trans _ (Ideal.Quotient.mk N)
          (RingHom.IsIntegral.trans (algebraMap K (K ⊗[A] B))
            (Algebra.TensorProduct.comm A K B).toRingEquiv.toRingHom ?_ ?_) ?_) ?_
      · exact Algebra.IsIntegral.isIntegral
      · exact RingHom.isIntegral_of_surjective _
          (Algebra.TensorProduct.comm A K B).toRingEquiv.surjective
      · exact RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
      · exact RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    exact IsAlgClosed.of_ringEquiv K _
      (RingEquiv.ofBijective φ (IsAlgClosed.ringHom_bijective_of_isIntegral φ hφ))
  have hy : ∀ I : MaximalSpectrum (D ⧸ N), ∃ y : Y.left,
      Y.hom y = Spec.algebraMap B ((D ⧸ N) ⧸ I.asIdeal) (IsLocalRing.closedPoint _) :=
    fun I => Y.hom.surjective _
  choose y hy using hy
  obtain ⟨U, hU, hEU⟩ := Picard.exists_isAffineOpen_of_finite_of_quasiAffine Y.left
    (Set.range y) (Set.finite_range y)
  let V : Y.left.affineOpens := ⟨U, hU⟩
  let X := openOver B Y U
  have : IsAffine X.left := hU
  have : Algebra.Etale B (AffineCoordinateRing B X) := affineCoordinate_etale B X
  have hpts : ∀ I : MaximalSpectrum (D ⧸ N),
      Nonempty (AffineCoordinateRing B X →ₐ[B] (D ⧸ N) ⧸ I.asIdeal) := by
    intro I
    have := hclosed I
    obtain ⟨p⟩ := nonempty_ringPoint_of_isAlgClosed B X ((D ⧸ N) ⧸ I.asIdeal)
      ⟨y I, hEU ⟨I, rfl⟩⟩ (by
        change (U.ι ≫ Y.hom) ⟨y I, hEU ⟨I, rfl⟩⟩ = _
        rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        exact hy I)
    exact ⟨affineSchemePointEquiv B X _ p⟩
  obtain ⟨f⟩ := Langlands.Algebra.nonempty_algHom_of_isArtinianRing hpts
  let q : RingPoint B X D := (affineSchemePointEquiv B X D).symm f
  let r : RingPoint A (affineWeilRestriction A B X) K :=
    (affineWeilRestrictionPointEquiv A B X K).symm q
  let p := r ≫ affineChartWeilRestrictionι A B Y V
  refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w p]
  exact ht

end Langlands.AlgebraicGeometry.PointTopology
