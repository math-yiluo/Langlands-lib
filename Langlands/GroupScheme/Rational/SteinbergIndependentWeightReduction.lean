import Langlands.GroupScheme.Rational.SteinbergPrefixWeights
import Langlands.GroupScheme.Rational.IndependentWeightProductStatement
import Langlands.GroupScheme.Rational.SplitSteinbergImmersionStatement
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction

/-! # The actual Steinberg product as a translated independent-weight product -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ} (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

/-- On every test, moving representatives to the right gives the prefix-conjugated factors. -/
theorem steinbergProductPoint_eq_independentWeightProduct
    (T : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(T.left, ⊤)) :
    steinbergProductPoint e x n T c =
      IndependentWeightProduct.point (prefixRootHom e x n) T c *
        G.constantPoint (coxeterNormalizer e n) T := by
  let f : normalizerPoints p.inclusion →* (T ⟶ G.X) :=
    (G.constantPointHom T).comp (normalizerPoints p.inclusion).subtype
  have hp (j : Fin r) :
      G.constantPoint (prefixNormalizer e n j.castSucc) T =
        orderedPrefix r (fun i => toUnit T ≫ (n (e i)).point) j.castSucc := by
    change f (orderedPrefix r (fun i => (n (e i)).normalizerPoint) j.castSucc) = _
    rw [map_orderedPrefix]
    rfl
  have hn : G.constantPoint (coxeterNormalizer e n) T =
      (List.ofFn fun j => toUnit T ≫ (n (e j)).point).prod := by
    change f (List.ofFn fun j => (n (e j)).normalizerPoint).prod = _
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [steinbergProductPoint, interleaved_prod_eq_prefix_conjugates, hn,
    IndependentWeightProduct.point]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [prefixRootHom, NormalizedRootParametrization.scalarPoint_conjugateHom, hp]

/-- The actual ordered morphism is the prefix-root product followed by right translation. -/
theorem steinbergProduct_eq_independentWeightProduct :
    steinbergProduct e x n =
      IndependentWeightProduct.morphism (prefixRootHom e x n) ≫
        G.rightTranslation (coxeterNormalizer e n) := by
  rw [comp_rightTranslation]
  exact steinbergProductPoint_eq_independentWeightProduct e x n _ _

end SplitPinning

/-- The independent-weight immersion criterion implies the exact supplied split target. -/
theorem splitSteinbergImmersion_of_independentWeightProduct
    (h : IndependentWeightProductImmersionStatement.{u}) :
    SplitSteinbergImmersionStatement.{u} := by
  intro k _ G _ p _ r e x n
  have hc : IsClosedImmersion
      (IndependentWeightProduct.morphism (SplitPinning.prefixRootHom e x n)).left :=
    h k G p.torus p.isSplitTorus (AutomorphicAction.conjugation p.inclusion) r
      (SplitPinning.prefixRootHom e x n) (SplitPinning.prefixWeight e n)
      (SplitPinning.prefixWeight_linearIndependent e n)
      (SplitPinning.isClosedSubgroup_prefixRootHom e x n)
      (SplitPinning.prefixRootHom_torus_equivariant e x n)
  have : IsIso (G.rightTranslation (SplitPinning.coxeterNormalizer e n)).left :=
    inferInstanceAs (IsIso ((Over.forget _).map
      (G.rightTranslationIso (SplitPinning.coxeterNormalizer e n)).hom))
  rw [SplitPinning.steinbergProduct_eq_independentWeightProduct, Over.comp_left]
  infer_instance

end Langlands.GroupScheme
