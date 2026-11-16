import Langlands.GroupScheme.Torus.MaximalModuliOrbit
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality

/-! # Comparing supplied maximal-torus moduli with a normalizer quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {M : Over S} {K : CommGroupScheme M.left} {H : CommGroupScheme S}

/-- The normalizer quotient and the maximal-torus orbit have identical all-test fibers. -/
theorem normalizerQuotient_orbit_fiber_iff
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n)
    (U : Over S) (g h : U ⟶ G.X) :
    g ≫ Q.projection = h ≫ Q.projection ↔
      g ≫ maximalOrbit j huni i hH hi hmax = h ≫ maximalOrbit j huni i hH hi hmax := by
  rw [Q.fibers, maximalOrbit_fibers j huni hK hj hm i hH hi hmax, hn.2]

/-- The normalizer orbit descends to an actual morphism from any supplied quotient. -/
def normalizerQuotientComparison
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n) : Q.scheme ⟶ M := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  let : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  exact HomogeneousQuotientComparison.desc Q.projection (maximalOrbit j huni i hH hi hmax)
    (fun U g h hab =>
      (normalizerQuotient_orbit_fiber_iff j huni hK hj hm i hH hi hmax n hn Q U g h).mp hab)

/-- The descended comparison recovers the orbit after the quotient projection. -/
theorem projection_normalizerQuotientComparison
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n) :
    Q.projection ≫ normalizerQuotientComparison j huni hK hj hm i hH hi hmax n hn Q =
      maximalOrbit j huni i hH hi hmax := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  let : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  unfold normalizerQuotientComparison
  exact HomogeneousQuotientComparison.fac_desc _ _ _

/-- Equality of all-test fibers makes the descended comparison a scheme monomorphism. -/
theorem mono_normalizerQuotientComparison
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n) :
    Mono (normalizerQuotientComparison j huni hK hj hm i hH hi hmax n hn Q).left := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  let : QuasiCompact Q.projection.left := Q.quasiCompact_projection
  unfold normalizerQuotientComparison
  exact HomogeneousQuotientComparison.mono_desc_of_fiber_iff Q.projection
    (maximalOrbit j huni i hH hi hmax)
    (normalizerQuotient_orbit_fiber_iff j huni hK hj hm i hH hi hmax n hn Q)

/-- Etale-local conjugacy supplies local sections of the maximal-torus orbit over M. -/
theorem exists_etaleCover_maximalOrbit_lifts
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) :
    ∃ 𝒰 : M.left.Cover.{u} (Scheme.precoverage @Etale), ∀ k,
      ∃ g : SubgroupFunctor.etaleCoverObj (T := M) 𝒰 k ⟶ G.X,
        g ≫ maximalOrbit j huni i hH hi hmax = SubgroupFunctor.etaleCoverMap 𝒰 k := by
  let : Smooth ((baseChange M.hom).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom M.hom))
  let : IsAffineHom ((baseChange M.hom).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  obtain ⟨𝒰, h𝒰⟩ := EtaleLocallySubgroupConjugate.of_relativeTori
    (T := (CommGroupScheme.baseChange M.hom).obj H)
    (T' := K) (i := (baseChange M.hom).map i) (i' := j)
    (hH.baseChange M.hom) hK (hmax.baseChange M.hom) hm
  refine ⟨𝒰, fun k => ?_⟩
  let U := SubgroupFunctor.etaleCoverObj (T := M) 𝒰 k
  let a : U ⟶ M := SubgroupFunctor.etaleCoverMap 𝒰 k
  let eG := Descent.pullbackComparison M.hom a.left U.hom (Over.w a) G
  let eH := Descent.pullbackComparison M.hom a.left U.hom (Over.w a) H.toGrp
  have hc := (h𝒰 k).postcomp eG.hom
  change SubgroupConjugate
    ((baseChange a.left).map ((baseChange M.hom).map i) ≫
      (Descent.pullbackComparison M.hom a.left U.hom (Over.w a) G).hom)
    (familyHom j a) at hc
  rw [Descent.pullbackComparison_naturality M.hom a.left U.hom (Over.w a) i] at hc
  have hc' : SubgroupConjugate ((baseChange U.hom).map i) (familyHom j a) :=
    SubgroupConjugate.of_precomp_isos eH (Iso.refl _) hc
  obtain ⟨g, e, he⟩ := hc'
  let g₀ : U ⟶ G.X := baseChangeBasePointsEquiv U.hom G g
  refine ⟨g₀, ?_⟩
  apply huni.evaluate_injective hK hj hm
  rw [evaluate_maximalOrbit]
  have hg : SubgroupFunctor.conjugateFamily i g₀ =
      (baseChange U.hom).map i ≫ (((baseChange U.hom).obj G).innerIso g).hom := by
    simp only [SubgroupFunctor.conjugateFamily, SubgroupFunctor.conjugatePullback,
      g₀, MulEquiv.symm_apply_apply]
  rw [hg, he]
  exact SubgroupFunctor.range_iso_comp e (familyHom j a)

/-- A supplied normalizer quotient is isomorphic over the base to the supplied
universal maximal-torus parameter scheme. -/
def normalizerQuotientIso
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n) : Q.scheme ≅ M := by
  apply Classical.choice
  let d := normalizerQuotientComparison j huni hK hj hm i hH hi hmax n hn Q
  let : Mono d.left := mono_normalizerQuotientComparison j huni hK hj hm i hH hi hmax n hn Q
  have hd : Q.projection ≫ d = maximalOrbit j huni i hH hi hmax :=
    projection_normalizerQuotientComparison j huni hK hj hm i hH hi hmax n hn Q
  obtain ⟨𝒰, h𝒰⟩ := exists_etaleCover_maximalOrbit_lifts j huni hK hj hm i hH hi hmax
  choose g hg using h𝒰
  let : EffectiveEpiFamily 𝒰.X 𝒰.f := SubgroupFunctor.effectiveEpiFamily_etaleCover 𝒰
  let s := fun k => (g k ≫ Q.projection).left
  have hs (k : 𝒰.I₀) : s k ≫ d.left = 𝒰.f k := by
    change (g k ≫ Q.projection ≫ d).left = (SubgroupFunctor.etaleCoverMap 𝒰 k).left
    rw [hd, hg k]
  have hc {Z : Scheme.{u}} (k l : 𝒰.I₀)
      (a : Z ⟶ 𝒰.X k) (b : Z ⟶ 𝒰.X l) (hab : a ≫ 𝒰.f k = b ≫ 𝒰.f l) :
      a ≫ s k = b ≫ s l := by
    apply (cancel_mono d.left).mp
    simpa only [Category.assoc, hs] using hab
  let t := EffectiveEpiFamily.desc 𝒰.X 𝒰.f s hc
  have ht (k : 𝒰.I₀) : 𝒰.f k ≫ t = s k :=
    EffectiveEpiFamily.fac 𝒰.X 𝒰.f s hc k
  have htd : t ≫ d.left = 𝟙 M.left := by
    apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
    intro k
    rw [← Category.assoc, ht, hs, Category.comp_id]
  have hdt : d.left ≫ t = 𝟙 Q.scheme.left := by
    apply (cancel_mono d.left).mp
    rw [Category.assoc, htd, Category.comp_id, Category.id_comp]
  have hw : t ≫ Q.scheme.hom = M.hom := by
    rw [← Over.w d, ← Category.assoc, htd, Category.id_comp]
  exact ⟨⟨d, Over.homMk t hw, Over.OverMorphism.ext hdt, Over.OverMorphism.ext htd⟩⟩

/-- Relative quasi-affineness transfers from a supplied normalizer quotient
through the actual comparison isomorphism. -/
theorem quasiAffineOver_of_normalizerQuotient
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i)
    {N : GroupScheme S} (n : N ⟶ G) (hn : (torusNormalizer i).IsRepresentedBy n)
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n)
    (hQ : ∀ V : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine) :
    ∀ V : S.affineOpens, (M.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine :=
  quasiAffineOver_of_iso
    (normalizerQuotientIso j huni hK hj hm i hH hi hmax n hn Q).symm hQ

end Langlands.GroupScheme.TorusSubgroupModuli
