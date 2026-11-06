import Langlands.GroupScheme.RelativeParabolicQuotientFibers
import Langlands.GroupScheme.RelativeSelfNormalizerStatement
import Langlands.GroupScheme.SelfNormalizingProperAmbientStatement
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Relative parabolic normalizers from explicit generic statement inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Reductive group schemes have geometrically connected structure morphisms. -/
theorem IsReductive.geometricallyConnected {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsReductive G) : GeometricallyConnected G.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ f => ?_⟩
  exact (hG.isConnectedReductive_baseChange f).connectedSpace

namespace RelativeParabolicNormalizerReduction

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} {i : P ⟶ G}

/-- Geometric connectedness of the subgroup follows from the parabolic field
hypothesis, conditional on the exact parabolic-dynamic theorem. -/
theorem geometricallyConnected_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsReductive G)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    GeometricallyConnected P.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ f => ?_⟩
  let Gk := (GroupScheme.baseChange f).obj G
  let Pk := (GroupScheme.baseChange f).obj P
  let ik := (GroupScheme.baseChange f).map i
  have hGk : IsConnectedReductive Gk := hG.isConnectedReductive_baseChange f
  have hPk : IsParabolicSubgroup ik :=
    RelativeParabolicQuotientFibers.parabolic_atFieldPoint hP f
  let : Smooth Gk.X.hom := hGk.smooth
  let : IsAffineHom Gk.X.hom := hGk.isAffineHom
  let : IsClosedImmersion ik.hom.hom.left := hPk.isClosedSubgroup
  let : Mono ik.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hPD k Gk hGk Pk ik hPk.isClosedSubgroup).mp hPk
  exact ((dynamicConnected k Gk χ Pk ik).2 hGk.connectedSpace).1
    ⟨inferInstance, hχ⟩

/-- Relative field detection and the field self-normalizer theorem identify the
all-test normalizer of the original subgroup. The structural inputs stay explicit. -/
theorem normalizer_eq_of_statements
    (hrelative : RelativeSelfNormalizerStatement.{u})
    (hfield : ParabolicSelfNormalizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  apply hrelative _ G P i hi hPsmooth
    (geometricallyConnected_of_parabolicDynamic hPD hG hP)
  intro k _ b
  exact hfield k _ (hG.isConnectedReductive_baseChange b) _ _
    (RelativeParabolicQuotientFibers.parabolic_atFieldPoint hP b)

/-- The generic proper-ambient statement now applies to the original parabolic
subgroup, conditional on the exact normalizer and dynamic statement inputs. -/
theorem properAmbient_of_statements
    (hrelative : RelativeSelfNormalizerStatement.{u})
    (hfield : ParabolicSelfNormalizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    ∃ (Y : Over (Spec (CommRingCat.of R))) (r : G.X ⟶ Y),
      IsProper Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
        g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact hambient R G P i hG.geometricallyConnected hi hPsmooth
    (geometricallyConnected_of_parabolicDynamic hPD hG hP)
    (normalizer_eq_of_statements hrelative hfield hPD hG hPsmooth hi hP)

/-- A proper finite-presentation ambient map with exact right-coset fibres. -/
structure ProperAmbientMap (i : P ⟶ G) where
  scheme : Over (Spec (CommRingCat.of R))
  map : G.X ⟶ scheme
  proper : IsProper scheme.hom
  locallyOfFinitePresentation : LocallyOfFinitePresentation scheme.hom
  fibers : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
    g ≫ map = h ≫ map ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

/-- Retain an actual proper ambient map obtained from the explicit statement inputs. -/
def properAmbientOfStatements
    (hrelative : RelativeSelfNormalizerStatement.{u})
    (hfield : ParabolicSelfNormalizerStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    ProperAmbientMap i := by
  let hex := properAmbient_of_statements hrelative hfield hPD hambient hG hPsmooth hi hP
  let Y := Classical.choose hex
  let hr := Classical.choose_spec hex
  let r := Classical.choose hr
  have hs := Classical.choose_spec hr
  exact ⟨Y, r, hs.1, hs.2.1, hs.2.2⟩

end RelativeParabolicNormalizerReduction

end Langlands.GroupScheme
