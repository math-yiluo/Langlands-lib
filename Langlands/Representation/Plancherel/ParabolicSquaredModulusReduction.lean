import Langlands.Representation.Plancherel.StandardIntertwiningModulus
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Aubert.General.EqualCentralizerHaarBalance
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.Statement
import Langlands.Representation.Plancherel.ParabolicIntertwiningReduction

/-! # Conditional squared-modulus compatibility for actual rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Plancherel

open Aubert.General Aubert.General.RationalPointFamily StandardIntertwining

private theorem closedNormalizerCharacter_congr'
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {U V : Subgroup H}
    (hUV : U = V) (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (x : Subgroup.normalizer (U : Set H)) (y : Subgroup.normalizer (V : Set H))
    (hxy : (x : H) = y) :
    HaarModulus.closedNormalizerCharacter U hU x =
      HaarModulus.closedNormalizerCharacter V hV y := by
  subst V
  congr 1
  exact Subtype.ext hxy

variable {F : Type u} [Field F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {p' : P' ⟶ G} {l' : M ⟶ P'}
  {a : A.toGrp ⟶ M} {n : U ⟶ P} {n' : U' ⟶ P'}
  (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)

/-- A cocharacter of the split component, pushed into the presentation torus. -/
abbrev parabolicTorusCocharacter (ν : cocharacterLattice A) : cocharacterLattice r.data.T :=
  RealTorusSpace.cocharacterMapInt r.data.f ν

/-- The pushed cocharacter has the same ambient composite as the original one. -/
theorem parabolic_groupHom_torusCocharacter_comp (ν : cocharacterLattice A) :
    CommGroupScheme.groupHom (parabolicTorusCocharacter r ν) ≫ r.data.i =
      CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p := by
  change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom r.data.f) ≫
    r.data.i = _
  rw [Category.assoc, r.isCompatible.factor_comp]

include r' in
/-- The two split-component cocharacters, pushed into the first presentation
torus, have equal full dynamic centralizers: both are the common Levi. -/
theorem parabolic_centralizer_torusCocharacter_eq (hLevi : l ≫ p = l' ≫ p') :
    Dynamic.centralizer
        (CommGroupScheme.groupHom (parabolicTorusCocharacter r r.splitComponentCocharacter) ≫
          r.data.i) =
      Dynamic.centralizer
        (CommGroupScheme.groupHom (parabolicTorusCocharacter r r'.splitComponentCocharacter) ≫
          r.data.i) := by
  rw [parabolic_groupHom_torusCocharacter_comp r, parabolic_groupHom_torusCocharacter_comp r,
    ← r.levi_eq_splitComponentCocharacter, hLevi, ← r'.levi_eq_splitComponentCocharacter]

/-- The Levi image is the full centralizer of the first pushed cocharacter. -/
theorem parabolic_levi_eq_centralizer_torusCocharacter :
    SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer
        (CommGroupScheme.groupHom (parabolicTorusCocharacter r r.splitComponentCocharacter) ≫
          r.data.i) := by
  rw [parabolic_groupHom_torusCocharacter_comp r, r.levi_eq_splitComponentCocharacter]

/-- The presentation torus factors through the Levi `M`: it centralizes each of
its own cocharacters, and `l ≫ p` represents such a centralizer. -/
theorem parabolic_exists_torusLeviFactor :
    ∃ j : r.data.T.toGrp ⟶ M, j ≫ l ≫ p = r.data.i := by
  have := r.isCompatible.levi.isClosedSubgroup.mono
  have := r.isCompatible.parabolic.isClosedSubgroup.mono
  have : Mono (l ≫ p).hom.hom.left := by
    change Mono (l.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom
      (parabolicTorusCocharacter r r.splitComponentCocharacter) ≫ r.data.i)).IsRepresentedBy
        (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, parabolic_levi_eq_centralizer_torusCocharacter r⟩
  exact ⟨Dynamic.torusFactor r.data.i _ hrep, Dynamic.torusFactor_comp r.data.i _ hrep⟩

/-- The split component factors through every torus factor `j` of the
presentation torus through `M`, by the factor `r.data.f`. -/
theorem parabolic_groupHom_comp_torusLeviFactor
    (j : r.data.T.toGrp ⟶ M) (hj : j ≫ l ≫ p = r.data.i) :
    CommGroupScheme.groupHom r.data.f ≫ j = a := by
  have := r.isCompatible.levi.isClosedSubgroup.mono
  have := r.isCompatible.parabolic.isClosedSubgroup.mono
  have hc : CommGroupScheme.groupHom r.data.f ≫ j ≫ l ≫ p = a ≫ l ≫ p := by
    rw [hj, r.isCompatible.factor_comp]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (l.hom.hom.left ≫ p.hom.hom.left)).mp
  exact congrArg (fun z : A.toGrp ⟶ G => z.hom.hom.left) hc

/-- Injective restriction of rational characters from `M` to its split
component gives injective restriction to every torus factor of the
presentation torus. -/
theorem parabolic_characterRestrict_injective_of_splitComponent
    (j : r.data.T.toGrp ⟶ M) (hj : j ≫ l ≫ p = r.data.i)
    (ha : Function.Injective (characterRestrict a)) :
    Function.Injective (characterRestrict j) := by
  intro χ ψ hχψ
  apply ha
  rw [← parabolic_groupHom_comp_torusLeviFactor r j hj, characterRestrict_comp,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hχψ]

/-- If central split tori detect nonzero rational characters of connected
reductive groups, restriction from `M` to every torus factor of the
presentation torus is injective. -/
theorem parabolic_characterRestrict_injective_of_centralSplitTorusCharacter
    (hS : CentralSplitTorusCharacterStatement.{u})
    (j : r.data.T.toGrp ⟶ M) (hj : j ≫ l ≫ p = r.data.i) :
    Function.Injective (characterRestrict j) :=
  parabolic_characterRestrict_injective_of_splitComponent r j hj
    (characterRestrict_injective_of_centralSplitTorusCharacter hS
      r.isCompatible.levi.isConnectedReductive r.isCompatible.splitComponent)

variable [Smooth G.X.hom]

/-- The first radical image is the dynamic radical of the first pushed cocharacter. -/
theorem parabolic_radical_eq_unipotent_torusCocharacter
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    SubgroupFunctor.range (n ≫ p) =
      Dynamic.unipotent
        (CommGroupScheme.groupHom (parabolicTorusCocharacter r r.splitComponentCocharacter) ≫
          r.data.i) := by
  rw [parabolic_groupHom_torusCocharacter_comp r, r.range_comp_radical_eq hn]

include r' in
/-- The second radical image is the dynamic radical of the second split-component
cocharacter, pushed into the first presentation torus. -/
theorem parabolic_radical'_eq_unipotent_torusCocharacter (hLevi : l ≫ p = l' ≫ p')
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n') :
    SubgroupFunctor.range (n' ≫ p') =
      Dynamic.unipotent
        (CommGroupScheme.groupHom (parabolicTorusCocharacter r r'.splitComponentCocharacter) ≫
          r.data.i) := by
  rw [parabolic_groupHom_torusCocharacter_comp r, hLevi, r'.range_comp_radical_eq hn']

section Haar

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffine M.X.left]

local instance parabolicSquaredModulusAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance parabolicSquaredModulusTopology :
    TopologicalSpace (RationalPoint F G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint F G.X)]
  [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]

include r' in
/-- If restriction of rational characters from the Levi `M` to the presentation
torus is injective, the two actual radicals of a common Levi satisfy the
squared-modulus compatibility. The relative root system and the injectivity
remain explicit premises. -/
theorem parabolic_squaredModulusCompatibility_of_characterRestrict_injective
    (hLevi : l ≫ p = l' ≫ p')
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (hroot : haveI := r.isCompatible.maximalSplit.isSplitSubtorus.mono
      HasRelativeRootSystem r.data.i)
    (j : r.data.T.toGrp ⟶ M) (hj : j ≫ l ≫ p = r.data.i)
    (hinj : Function.Injective (characterRestrict j))
    (h : IsSemidirectDecomposition
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (hU : IsClosed ((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (rationalPoints G)))
    (h' : IsSemidirectDecomposition
      ((SubgroupFunctor.range p').carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (hU' : IsClosed ((SubgroupFunctor.range (n' ≫ p')).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (rationalPoints G)))
    [MeasurableSpace (((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).subgroupOf
        ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))]
    [BorelSpace (((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).subgroupOf
        ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))] :
    SquaredModulusCompatibility h hU h' hU' := by
  have := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := inferInstance
  let zeta := parabolicTorusCocharacter r r.splitComponentCocharacter
  let eta := parabolicTorusCocharacter r r'.splitComponentCocharacter
  have hEq := parabolic_centralizer_torusCocharacter_eq r r' hLevi
  have hZ : SubgroupFunctor.range (l ≫ p) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ r.data.i) :=
    (parabolic_levi_eq_centralizer_torusCocharacter r).le
  have hZ' : SubgroupFunctor.range (l ≫ p) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ r.data.i) := by
    rw [← hEq]
    exact hZ
  have hUeq := parabolic_radical_eq_unipotent_torusCocharacter r hn
  have hVeq := parabolic_radical'_eq_unipotent_torusCocharacter r r' hLevi hn'
  have hUc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ r.data.i)).carrier
      (Over.mk (𝟙 _)) : Set (RationalPoint F G.X)) := by
    rw [← hUeq]
    exact hU
  have hVc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ r.data.i)).carrier
      (Over.mk (𝟙 _)) : Set (RationalPoint F G.X)) := by
    rw [← hVeq]
    exact hU'
  have hCc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ r.data.i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ r.data.i)).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint F G.X)) := by
    rw [← hUeq, ← hVeq]
    exact hU.inter hU'
  have hUrep := Dynamic.Affine.isRepresentedBy_unipotentHom
    (CommGroupScheme.groupHom zeta ≫ r.data.i)
  have hVrep := Dynamic.Affine.isRepresentedBy_unipotentHom
    (CommGroupScheme.groupHom eta ≫ r.data.i)
  have hUcl := Dynamic.Affine.isClosedSubgroup_unipotentHom
    (CommGroupScheme.groupHom zeta ≫ r.data.i)
  have hVcl := Dynamic.Affine.isClosedSubgroup_unipotentHom
    (CommGroupScheme.groupHom eta ≫ r.data.i)
  have hCcl := isClosedSubgroup_subgroupIntersectionHom hUcl hVcl
  have hCrep := isRepresentedBy_subgroupIntersectionHom hUcl hVcl
  rw [hUrep.2, hVrep.2] at hCrep
  have := hUcl.isAffineHom
  have := hVcl.isAffineHom
  have := hCcl.isAffineHom
  have := hUcl.locallyOfFiniteType
  have := hVcl.locallyOfFiniteType
  have := hCcl.locallyOfFiniteType
  apply (squaredModulusCompatibility_iff h hU h' hU').mpr
  intro m
  obtain ⟨z, hz⟩ := m.property
  have key := centralizingHaarCharacter_values_square_of_centralizer_eq hroot hT zeta eta hEq
    (l ≫ p) hZ hZ' hUrep hVrep hCrep j hj
    (Lie.finiteCoordinates _) (Lie.finiteCoordinates _) (Lie.finiteCoordinates _)
    hUc hVc hCc hinj z
  have h1 : centralizingUnipotentHaarCharacter (CommGroupScheme.groupHom zeta ≫ r.data.i)
      (l ≫ p) hZ hUc z = HaarModulus.closedRestrictCharacter _ hU _ h.levi_le_normalizer m :=
    closedNormalizerCharacter_congr' (by rw [hUeq]) hUc hU _ _ hz
  have h2 : centralizingUnipotentHaarCharacter (CommGroupScheme.groupHom eta ≫ r.data.i)
      (l ≫ p) hZ' hVc z = HaarModulus.closedRestrictCharacter _ hU' _ h'.levi_le_normalizer m :=
    closedNormalizerCharacter_congr' (by rw [hVeq]) hVc hU' _ _ hz
  have h3 : centralizingUnipotentIntersectionHaarCharacter
      (CommGroupScheme.groupHom zeta ≫ r.data.i) (CommGroupScheme.groupHom eta ≫ r.data.i)
      (l ≫ p) hZ hZ' hCc z =
        HaarModulus.closedRestrictCharacter _ (hU.inter hU') _
          (levi_le_normalizer_intersection h h') m :=
    closedNormalizerCharacter_congr'
      (V := (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)) ⊓
        (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
      (by rw [hUeq, hVeq]; rfl) hCc (hU.inter hU') _ _ hz
  rw [h1, h2, h3] at key
  exact key

include r r' in
/-- The squared-modulus compatibility for the actual radicals of a common Levi
of a connected reductive group, assuming the relative root system statement
and that central split tori detect nonzero rational characters. -/
theorem parabolic_squaredModulusCompatibility_of_structural
    (hRS : RelativeRootSystemStatement.{u}) (hS : CentralSplitTorusCharacterStatement.{u})
    (hG : IsConnectedReductive G)
    (hLevi : l ≫ p = l' ≫ p')
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (h : IsSemidirectDecomposition
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (hU : IsClosed ((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (rationalPoints G)))
    (h' : IsSemidirectDecomposition
      ((SubgroupFunctor.range p').carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (hU' : IsClosed ((SubgroupFunctor.range (n' ≫ p')).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) : Set (rationalPoints G)))
    [MeasurableSpace (((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).subgroupOf
        ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))]
    [BorelSpace (((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).subgroupOf
        ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))] :
    SquaredModulusCompatibility h hU h' hU' := by
  obtain ⟨j, hj⟩ := parabolic_exists_torusLeviFactor r
  exact parabolic_squaredModulusCompatibility_of_characterRestrict_injective r r' hLevi hn hn'
    (hRS F G hG r.data.T r.data.i r.isCompatible.maximalSplit) j hj
    (parabolic_characterRestrict_injective_of_centralSplitTorusCharacter r hS j hj)
    h hU h' hU'

end Haar

section Analytic

universe uV uW

/-- The analytic part of `ConditionalParabolicIntertwiningInputs`, over exactly
the same data: for every admissible finite-length inducing representation, one
threshold `R` such that the actual standard integral converges on the whole
source at every parameter of the region `C R`, with local integrable domination
of the compact integrands on `C R`. The squared-modulus compatibility is
omitted. -/
def ConditionalParabolicAnalyticInputs : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P P' Q U U' V : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
      (p : P ⟶ G) (l : M ⟶ P) (p' : P' ⟶ G) (l' : M ⟶ P')
      (a : A.toGrp ⟶ M) (n : U ⟶ P) (n' : U' ⟶ P') (q : Q ⟶ G) (v : V ⟶ Q)
      (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a)
      (_hLevi : l ≫ p = l' ≫ p')
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
      (_hQ : (Dynamic.parabolic
        (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
      (_hv : LeviSubgroup.IsGeometricUnipotentRadical v),
      letI : Mono r.data.i.hom.hom.left :=
        r.isCompatible.maximalSplit.isSplitSubtorus.mono
      letI : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
        let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
        let := r.isCompatible.levi.isClosedSubgroup.mono
        let := r.isCompatible.parabolic.isClosedSubgroup.mono
        have : Mono (a ≫ l ≫ p).hom.hom.left := by
          change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
          infer_instance
        exact mono_of_mono_fac
          (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)
      ∀ [Fintype (relativeWeylGroup r.data.i)],
        let B := weylInducedCharacterForm r.isCompatible.splitComponent.1.isSplitSubtorus.1
          r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.f r.data.i
        let C := parabolicPointUnramifiedIntertwiningRegion r B n q v
        let Ppt := (SubgroupFunctor.range p).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let P'pt := (SubgroupFunctor.range p').carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let Mpt := parabolicLeviPointSubgroup p l
        let Upt := (SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        let U'pt := (SubgroupFunctor.range (n' ≫ p')).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))
        ∀ (h : IsSemidirectDecomposition Ppt Mpt Upt) (hU : IsClosed (Upt : Set (rationalPoints G)))
          (h' : IsSemidirectDecomposition P'pt Mpt U'pt)
          (_hU' : IsClosed (U'pt : Set (rationalPoints G)))
          (hP : IsClosed (Ppt : Set (rationalPoints G)))
          (_hP' : IsClosed (P'pt : Set (rationalPoints G)))
          (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
          (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (_hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
            g = (p : rationalPoints G) * (k : rationalPoints G))
          (hr : Continuous h.projection) (_hr' : Continuous h'.projection),
          let ν := parabolicLeviRationalNormCharacters r
          let hν := continuous_parabolicLeviRationalNormCharacters r
          ∀ [MeasurableSpace U'pt] [BorelSpace U'pt]
            [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
            [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
            [BorelSpace (QuotientSpace (U := Upt) U'pt)]
            (qν : Measure (QuotientSpace (U := Upt) U'pt))
            (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
            [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
            [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
            (_hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
            (π : SmoothRep.{0, u, uV} ℂ Mpt),
            π.IsAdmissible → π.HasFiniteLength →
            ∃ R : ℝ,
              (∀ χ : C R, domain h hU U'pt
                (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) ∧
              ∀ (hδ : IsUnimodularModulus Upt hU),
                CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr π U'pt qν (C R)

/-- The analytic inputs, together with the relative root system statement and
detection of nonzero rational characters by central split tori, give all
remaining inputs of the conditional intertwining theorem. -/
theorem conditionalParabolicIntertwiningInputs_of_analyticInputs
    (hRS : RelativeRootSystemStatement.{u}) (hS : CentralSplitTorusCharacterStatement.{u})
    (H : ConditionalParabolicAnalyticInputs.{u, uV}) :
    ConditionalParabolicIntertwiningInputs.{u, uV} := by
  intro F _ _ _ _ G hG _ _ _ A M P P' Q U U' V _ _ p l p' l' a n n' q v r r' hLevi hn hn' hQ hv
    _ B C Ppt P'pt Mpt Upt U'pt h hU h' hU' hP hP' K hK hPK hP'K hr hr' ν hν hM
    _ _ _ _ _ _ qν μU' μI _ _ _ _ _ _ hqν π hadm hfin
  obtain ⟨R, hfullC, hdom⟩ := H F G hG A M P P' Q U U' V p l p' l' a n n' q v r r' hLevi hn hn'
    hQ hv h hU h' hU' hP hP' K hK hPK hP'K hr hr' qν μU' μI hqν π hadm hfin
  have := hG.isAffineHom
  have := hG.smooth
  exact ⟨parabolic_squaredModulusCompatibility_of_structural r r' hRS hS hG hLevi hn hn'
    h hU h' hU', R, hfullC, hdom⟩

/-- The conditional intertwining theorem from its analytic inputs, the relative
root system statement and detection of nonzero rational characters by central
split tori. -/
theorem conditionalParabolicIntertwiningStatement_of_analyticInputs
    (hRS : RelativeRootSystemStatement.{u}) (hS : CentralSplitTorusCharacterStatement.{u})
    (H : ConditionalParabolicAnalyticInputs.{u, uV}) :
    ConditionalParabolicIntertwiningStatement.{u, uV, uW} :=
  conditionalParabolicIntertwiningStatement_of_inputs
    (conditionalParabolicIntertwiningInputs_of_analyticInputs hRS hS H)

end Analytic

end Langlands.Plancherel
