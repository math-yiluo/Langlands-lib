import Langlands.Geometry.Analytic.GroundFieldExtensionSemilinearPoints
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionDomainSections

/-! # Bounded local-domain pullbacks of the analytic coefficient lifts -/

noncomputable section

universe u u' u'' v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension (map iota domainPreservation spectrumProjection)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (M : Type u'') [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

variable (i : a.Index) (U : Domain L (chartAlgebra K L a i))
  (V : Domain M (chartAlgebra K M a i))

/-- The extended domain retains the scalar extension of the stored
full-domain algebra and of its bounded structural map. -/
def extendedLocalDomain : LocalDomain (atlas L M (atlas K L a)) :=
  ⟨i, ⟨PresentedAffinoidAlgebra.GroundFieldExtension.algebra L M U.algebra, map L M U.baseMap,
    spectrumProjection L M (chartAlgebra K L a i) ⁻¹' U.locus,
    domainPreservation L M _ _ _ _ U.represents⟩⟩

/-- A map of the chart loci gives the corresponding inclusion of local
domain loci in the glued spaces. -/
theorem towerLocalDomain_admissible_of_chart
    (h : MapsTo (spectrumProjection L M (chartAlgebra K L a i) ∘ towerChartHomeomorph K L M a i)
      V.locus U.locus) :
    (towerCompatibleHom K L M a).baseMap ''
      (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨towerChartHomeomorph K L M a i x, h hx, (towerHomeomorph_chart K L M a i x).symm⟩

/-- The bounded pullback of the analytic tower comparison between an actual
source domain and an extended full domain in the matching target chart. -/
def towerLocalDomainPullback
    (h : (towerCompatibleHom K L M a).baseMap '' (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus) :
    BoundedAlgHom M (PresentedAffinoidAlgebra.GroundFieldExtension.algebra L M U.algebra) V.algebra :=
  (towerCompatibleHom K L M a).toStrongHom.localDomainPullback ⟨i, V⟩
    (extendedLocalDomain K L M a i U) h

/-- Restriction to the ambient chart recovers the actual bounded tower map. -/
theorem towerLocalDomainPullback_comp_baseMap
    (h : (towerCompatibleHom K L M a).baseMap '' (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus) :
    (towerLocalDomainPullback K L M a i U V h).comp (map L M U.baseMap) =
      V.baseMap.comp (towerChartEquiv K L M a i).toBoundedAlgHom := by
  let T := towerCompatibleHom K L M a
  let U' : LocalDomain (atlas K M a) := ⟨i, V⟩
  let V' := extendedLocalDomain K L M a i U
  let h₀ := (towerAdmissible_iff K L M a i i).mpr Subset.rfl
  let h₁ := T.toStrongHom.localDomain_parent_admissible U' V' h
  refine (T.toStrongHom.localDomainPullback_comp_baseMap U' V' h).trans ?_
  refine (T.toStrongHom.localChartPullback_of_parent_admissible T.coherent U' i h₀ h₁).trans ?_
  exact congrArg V.baseMap.comp (towerCompatibleHom_pullback_same K L M a i h₀)

/-- Pullback to an actual scalar-extended domain, expressed on the original
section ring by preceding the tower restriction with the scalar embedding. -/
def towerLocalSectionPullback
    (h : (towerCompatibleHom K L M a).baseMap '' (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus) :
    BoundedRingHom U.algebra V.algebra :=
  (towerLocalDomainPullback K L M a i U V h).toBoundedRingHom.comp
    (iota L M U.algebra).toBoundedRingHom

/-- Its scalar rule is the actual embedding in the second step of the tower. -/
theorem towerLocalSectionPullback_scalar
    (h : (towerCompatibleHom K L M a).baseMap '' (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus) (c : L) :
    towerLocalSectionPullback K L M a i U V h (algebraMap L U.algebra c) =
      algebraMap M V.algebra (algebraMap L M c) := by
  let f := towerLocalDomainPullback K L M a i U V h
  change f (iota L M U.algebra (algebraMap L U.algebra c)) = _
  exact (congrArg f ((iota L M U.algebra).toAlgHom.commutes c)).trans
    (f.toAlgHom.commutes (algebraMap L M c))

/-- Its ambient rule is the full tower pullback evaluated on the original
scalar leg. -/
theorem towerLocalSectionPullback_baseMap
    (h : (towerCompatibleHom K L M a).baseMap '' (LocalDomain.locus (⟨i, V⟩ : LocalDomain (atlas K M a))) ⊆
      (extendedLocalDomain K L M a i U).locus) (b : chartAlgebra K L a i) :
    towerLocalSectionPullback K L M a i U V h (U.baseMap b) =
      V.baseMap (towerChartEquiv K L M a i (iota L M (chartAlgebra K L a i) b)) := by
  let f := towerLocalDomainPullback K L M a i U V h
  change f (iota L M U.algebra (U.baseMap b)) = _
  exact (congrArg f (PresentedAffinoidAlgebra.GroundFieldExtension.map_iota (L := M) U.baseMap b)).symm.trans
    (congrArg (fun q : BoundedAlgHom M (chartAlgebra L M (atlas K L a) i) V.algebra =>
      q (iota L M (chartAlgebra K L a i) b)) (towerLocalDomainPullback_comp_baseMap K L M a i U V h))

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open Set

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (B : PresentedAffinoidAlgebra K) {U : Domain L (algebra K L B)}
  (c : Domain.FiniteRationalCover U) (σ : domainCoverSectionSubgroup K L B c)

/-- The coefficient pullback maps the locus of the represented domain to
itself, as seen on the spectrum of its section algebra. -/
theorem coefficientHom_mapsTo_domain :
    MapsTo (BanachSpectrum.comap (coefficientHom K L B σ.val).toBoundedRingHom) U.locus U.locus := by
  intro x hx
  have hy : x ∈ range (BanachSpectrum.comap U.baseMap.toBoundedRingHom) :=
    U.represents.2.1.symm ▸ hx
  obtain ⟨y, rfl⟩ := hy
  exact (comap_domainSectionMap K L B c σ y) ▸
    U.represents.hasImageIn (BanachSpectrum.comap (domainSectionMap K L B c σ) y)

/-- Bounded restriction over an extended ambient map commutes with the
semilinear operators on the two full domain algebras. -/
theorem domainSectionMap_natural
    {A B : PresentedAffinoidAlgebra K}
    {U : Domain L (algebra K L A)} {V : Domain L (algebra K L B)}
    (cU : Domain.FiniteRationalCover U) (cV : Domain.FiniteRationalCover V)
    (τ : isometricAutomorphisms K L)
    (hU : τ ∈ domainCoverSectionSubgroup K L A cU)
    (hV : τ ∈ domainCoverSectionSubgroup K L B cV)
    (f : BoundedAlgHom K A B) (r : BoundedAlgHom L U.algebra V.algebra)
    (hr : r.comp U.baseMap = V.baseMap.comp (map K L f)) :
    r.toBoundedRingHom.comp (domainSectionMap K L A cU ⟨τ, hU⟩) =
      (domainSectionMap K L B cV ⟨τ, hV⟩).comp r.toBoundedRingHom := by
  apply semilinearDomainHom_ext K L A cU ⟨τ, hU⟩
  · intro t
    change r (domainSectionMap K L A cU ⟨τ, hU⟩ (algebraMap L U.algebra t)) = _
    exact (congrArg r (domainSectionMap_scalar K L A cU ⟨τ, hU⟩ t)).trans
      (r.toAlgHom.commutes (τ.val t))
  · intro t
    change domainSectionMap K L B cV ⟨τ, hV⟩ (r (algebraMap L U.algebra t)) = _
    exact (congrArg (domainSectionMap K L B cV ⟨τ, hV⟩) (r.toAlgHom.commutes t)).trans
      (domainSectionMap_scalar K L B cV ⟨τ, hV⟩ t)
  · intro b
    have hrb (d : algebra K L A) : r (U.baseMap d) = V.baseMap (map K L f d) :=
      congrArg (fun p : BoundedAlgHom L (algebra K L A) V.algebra => p d) hr
    change r (domainSectionMap K L A cU ⟨τ, hU⟩ (U.baseMap b)) =
      domainSectionMap K L B cV ⟨τ, hV⟩ (r (U.baseMap b))
    rw [domainSectionMap_baseMap, hrb (coefficientHom K L A τ b), hrb b, domainSectionMap_baseMap]
    exact congrArg (fun p : BoundedAlgHom K (algebra K L A) (algebra K L B) => V.baseMap (p b))
      (coefficientHom_natural K L τ f)

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

namespace Langlands.Analytic.SpaceOverField

open _root_.CategoryTheory Set CompleteUltrametricField PresentedAffinoidAlgebra IndexedAffinoidAtlas
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension

variable {K L : CompleteUltrametricField.{u}} (e : K ⟶ L)
variable (A : K.CompatibleCategory.{u, v}) (i : A.presentation.atlas.Index)

local notation "a" => A.presentation.atlas

variable {U : letI := e.normedAlgebra; Domain L (chartAlgebra K L A.presentation.atlas i)}
  (c : Domain.FiniteRationalCover U)
variable (σ : letI := e.normedAlgebra; ↥(domainCoverSectionSubgroup K L (A.presentation.atlas.algebra i) c))

private theorem coefficientLocalDomain_admissible :
    letI := e.normedAlgebra
    letI := (coefficientFieldMap (e := e) (Subtype.val σ)).normedAlgebra
    letI := scalarTower_of_comp_eq e (coefficientFieldMap (Subtype.val σ)) e (comp_coefficientFieldMap (Subtype.val σ))
    (towerCompatibleHom K L L (a)).baseMap ''
      (LocalDomain.locus (⟨i, U⟩ : IndexedAffinoidAtlas.LocalDomain (atlas K L (a)))) ⊆
      (extendedLocalDomain K L L (a) i U).locus := by
  let := e.normedAlgebra
  let d := coefficientFieldMap (e := e) (Subtype.val σ)
  let := d.normedAlgebra
  let := scalarTower_of_comp_eq e d e (comp_coefficientFieldMap (e := e) (Subtype.val σ))
  apply towerLocalDomain_admissible_of_chart K L L (a) i U U
  intro x hx
  have ht := congrArg (fun f : BoundedAlgHom K (chartAlgebra K L (a) i) (chartAlgebra K L (a) i) =>
      BanachSpectrum.comap f.toBoundedRingHom x)
    (towerProjectionPullback_eq_coefficientHom e (Subtype.val σ) ((a).algebra i))
  exact Eq.mpr (congrArg (fun y => y ∈ U.locus) ht)
    (coefficientHom_mapsTo_domain K L ((a).algebra i) c σ hx)

include σ in
/-- The bounded section pullback of the coefficient lift is computed by the
actual tower restriction to the full domain and the coefficient embedding. -/
def coefficientDomainSectionPullback : BoundedRingHom U.algebra U.algebra := by
  letI := e.normedAlgebra
  let d := coefficientFieldMap (e := e) (Subtype.val σ)
  letI := d.normedAlgebra
  letI := scalarTower_of_comp_eq e d e (comp_coefficientFieldMap (e := e) (Subtype.val σ))
  exact towerLocalSectionPullback K L L (a) i U U (coefficientLocalDomain_admissible e A i c σ)

/-- The analytic bounded pullback agrees on the entire represented section
algebra with the operator constructed by finite rational descent. -/
theorem coefficientDomainSectionPullback_eq_domainSectionMap :
    letI := e.normedAlgebra
    coefficientDomainSectionPullback e A i c σ = domainSectionMap K L ((a).algebra i) c σ := by
  let := e.normedAlgebra
  let d := coefficientFieldMap (e := e) (Subtype.val σ)
  let := d.normedAlgebra
  let := scalarTower_of_comp_eq e d e (comp_coefficientFieldMap (e := e) (Subtype.val σ))
  let h := coefficientLocalDomain_admissible e A i c σ
  apply semilinearDomainHom_ext K L ((a).algebra i) c σ
  · intro t
    exact towerLocalSectionPullback_scalar K L L (a) i U U h t
  · exact domainSectionMap_scalar K L ((a).algebra i) c σ
  · intro b
    have hs := towerLocalSectionPullback_baseMap K L L (a) i U U h b
    refine hs.trans ?_
    have hb := congrArg (fun f : BoundedAlgHom K (chartAlgebra K L (a) i) (chartAlgebra K L (a) i) =>
      U.baseMap (f b)) (towerProjectionPullback_eq_coefficientHom e (Subtype.val σ) ((a).algebra i))
    exact hb.trans (domainSectionMap_baseMap K L ((a).algebra i) c σ b).symm

section OpenSubgroup

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* CoefficientAutomorphisms e)
  (hρ : ∀ t : L, Continuous (fun g : G => (ρ g).val t))
  (g : letI := e.normedAlgebra
       ↥(domainCoverSectionOpenSubgroup K L (A.presentation.atlas.algebra i) c ρ hρ))

/-- The bounded operators of the common open subgroup, used in the
continuity and spectral estimates, are the analytic domain pullbacks. -/
theorem coefficientDomainSectionPullback_eq_openDomainSectionMap :
    letI := e.normedAlgebra
    coefficientDomainSectionPullback e A i c
      ⟨ρ (Subtype.val g),
        (mem_domainCoverSectionOpenSubgroup K L ((a).algebra i) c ρ hρ _).mp (Subtype.property g)⟩ =
      openDomainSectionMap K L ((a).algebra i) c ρ hρ g := by
  let := e.normedAlgebra
  exact coefficientDomainSectionPullback_eq_domainSectionMap e A i c _

end OpenSubgroup

/-- On an original atlas the map component of the analytic coefficient lift
is induced by the very strong tower comparison used on local domains. -/
theorem coefficientLiftMap_onPresentation (τ : CoefficientAutomorphisms e) :
    coefficientLiftMap e (CompatibleAtlasPresentation.localizationFunctor.obj A) τ =
      eqToHom (congrArg (fun f => (localizedExtend.{u, v} f).obj
        (CompatibleAtlasPresentation.localizationFunctor.obj A)) (comp_coefficientFieldMap τ⁻¹).symm) ≫
      CompatibleAtlasPresentation.localizationFunctor.map
        ((AffinoidAtlasPresentation.GroundFieldExtension.CompleteField.compatibleExtendComp
          e (coefficientFieldMap τ⁻¹)).hom.app A) := by
  unfold coefficientLiftMap
  exact congrArg (_ ≫ ·) (localizedExtendComp_hom_app e (coefficientFieldMap τ⁻¹) A)

end Langlands.Analytic.SpaceOverField
