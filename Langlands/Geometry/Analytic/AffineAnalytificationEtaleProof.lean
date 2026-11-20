import Langlands.Geometry.Analytic.AffineAnalytificationEtaleStatement
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteGermComparisonProof
import Langlands.Geometry.Analytic.AffineAnalytificationQuasiFiniteProof
import Langlands.Geometry.Analytic.AnalytificationCenterProof
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Affine analytification and étale morphisms -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open AffinoidAtlasPresentation

/-- Detect flatness at the target primes for rings in independent universes. -/
private theorem flat_of_localRingHom {R : Type v} {S : Type w}
    [CommRing R] [CommRing S] (f : R →+* S)
    (h : ∀ (q : Ideal S) [q.IsPrime],
      (Localization.localRingHom (q.comap f) q f rfl).Flat) : f.Flat := by
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun q => Localization.AtPrime q)
    (fun q => Algebra.linearMap S _)
  intro q _
  algebraize_only [Localization.localRingHom (q.comap f) q f rfl]
  have : IsScalarTower R (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map (q.comap f) q f rfl x).symm
  have : Module.Flat (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) := h q
  exact Module.Flat.trans R (Localization.AtPrime (q.comap f)) (Localization.AtPrime q)

section Algebraic

variable {K : Type u} [Field K]
  {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]

private theorem finiteType_of_presentation
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B) :
    f.toRingHom.FiniteType := by
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact Algebra.FiniteType.of_restrictScalars_finiteType K A B

private theorem quasiFinite_of_formallyUnramified
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (hf : f.toRingHom.FormallyUnramified) : f.toRingHom.QuasiFinite := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra.FiniteType A B := finiteType_of_presentation Q f
  let : Algebra.FormallyUnramified A B := hf
  exact inferInstanceAs (Algebra.QuasiFinite A B)

private theorem etale_iff_unramified_and_flat_quasiFinite
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) :
    f.toRingHom.Etale ↔
      f.toRingHom.FormallyUnramified ∧ (f.toRingHom.Flat ∧ f.toRingHom.QuasiFinite) := by
  rw [RingHom.Etale.iff_flat_and_formallyUnramified]
  refine ⟨fun h => ⟨h.2.1, h.1, quasiFinite_of_formallyUnramified Q f h.2.1⟩, fun h => ?_⟩
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  exact ⟨h.2.1, h.1, RingHom.FinitePresentation.of_finiteType.mp
    (finiteType_of_presentation Q f)⟩

end Algebraic

/-- Every algebraic prime is the contraction of a point prime on an original chart. -/
private theorem exists_chart_with_center
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {B : Type w} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (q : PrimeSpectrum B) :
    ∃ (m : ℕ) (s : BanachSpectrum (algebra K Q m)),
      s.kernel.comap
        (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom =
        q.asIdeal := by
  have hcenter := (SchemeAnalytification.analytificationCenter.{u, w}.1 K B Q).1
  obtain ⟨y, hy⟩ := hcenter q
  obtain ⟨m, s, rfl⟩ := exists_chart K Q y
  have hk : (center K Q (chart K Q m s)).asIdeal = s.kernel.comap
      (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom := by
    ext a
    rfl
  exact ⟨m, s, hk.symm.trans (congrArg PrimeSpectrum.asIdeal hy)⟩

section Comparison

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

private theorem unramified_iff :
    f.toRingHom.FormallyUnramified ↔
      StrongHom.IsUnramified (A := presentation K Q) (B := presentation K P)
        (saturatedHom K P Q f) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  constructor
  · intro hf y
    have hfin := (affineAnalytificationQuasiFinite K A B P Q f).mp
      (quasiFinite_of_formallyUnramified Q f hf)
    obtain ⟨m, s, rfl⟩ := exists_chart K Q y
    apply (affineAnalytificationFiniteGermComparison K A B P Q f m s (hfin _)).1.mpr
    exact (Algebra.formallyUnramified_iff_forall (R := A) (A := B)).mp hf
      ⟨s.kernel.comap
        (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom,
        inferInstance⟩
  · intro hg
    change Algebra.FormallyUnramified A B
    apply (Algebra.formallyUnramified_iff_forall (R := A) (A := B)).mpr
    intro q
    obtain ⟨m, s, hs⟩ := exists_chart_with_center K Q q
    have hc :=
      (affineAnalytificationFiniteGermComparison K A B P Q f m s (hg _).isFiniteAt).1.mp (hg _)
    simpa only [hs] using hc

private theorem flat_quasiFinite_iff :
    (f.toRingHom.Flat ∧ f.toRingHom.QuasiFinite) ↔
      StrongHom.IsFlat (A := presentation K Q) (B := presentation K P)
        (saturatedHom K P Q f) := by
  constructor
  · rintro ⟨hf, hq⟩ y
    have hfin := (affineAnalytificationQuasiFinite K A B P Q f).mp hq
    obtain ⟨m, s, rfl⟩ := exists_chart K Q y
    apply (affineAnalytificationFiniteGermComparison K A B P Q f m s (hfin _)).2.mpr
    exact hf.localRingHom _ _ rfl
  · intro hg
    refine ⟨flat_of_localRingHom f.toRingHom ?_,
      (affineAnalytificationQuasiFinite K A B P Q f).mpr hg.isQuasifinite⟩
    intro q hq
    obtain ⟨m, s, hs⟩ := exists_chart_with_center K Q ⟨q, hq⟩
    change s.kernel.comap
      (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom =
        q at hs
    subst q
    exact
      (affineAnalytificationFiniteGermComparison K A B P Q f m s (hg _).isFiniteAt).2.mp (hg _)

end Comparison

/-- Affine analytification detects unramified, flat quasi-finite, and étale maps. -/
theorem affineAnalytificationEtale : AffineAnalytificationEtaleStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f
  have hu := unramified_iff K P Q f
  have hf := flat_quasiFinite_iff K P Q f
  exact ⟨hu, hf, (etale_iff_unramified_and_flat_quasiFinite P Q f).trans (and_congr hu hf)⟩

end Langlands.Analytic.AffineAnalytification
