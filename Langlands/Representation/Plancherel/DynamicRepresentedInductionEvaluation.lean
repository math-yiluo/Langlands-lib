import Langlands.Representation.Plancherel.DynamicCommonLeviPresentations
import Langlands.Representation.Plancherel.DynamicCommonLeviStructuralComparison
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Evaluation-preserving represented induction on a dynamic common Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviPresentations
open DynamicCommonLeviPresentationComparison

section PointImage

variable {F : Type u} [Field F] [TopologicalSpace F] [T2Space F]
  {G P M N : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance representedEvaluationPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (n : N ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication l n))
  {P' M' N' : Subgroup (rationalPoints G)}
  (h : IsSemidirectDecomposition P' M' N') (hN : IsClosed (N' : Set (rationalPoints G)))
  (hδ : IsUnimodularModulus N' hN)
  (eP : pointImage p = P') (eM : pointImage (l ≫ p) = M') (eN : pointImage (n ≫ p) = N')

local instance representedEvaluationLeviTopology [IsAffine M.X.left] :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

variable [IsAffine M.X.left] (e : rationalPoints M ≃ₜ* M')
  (he : ∀ m, (e m : rationalPoints G) = rationalPoints.map (l ≫ p) m)
  (B : SmoothRep.{0, u, uV} ℂ M')

set_option quotPrecheck false in
local notation "represented" =>
  (leviInductionFunctor p l n hp hn hl hmul).obj (SmoothRep.pullback e B)
set_option quotPrecheck false in
local notation "actual" => (DynamicNormalization.leviTwistedInductionFunctor h hN).obj B

private def representedPointInductionData :
    { E : (represented).representation.Equiv (actual).representation //
      ∀ (f : represented) (x : rationalPoints G), eval _ _ (E f) x = eval _ _ f x } := by
  subst P'
  subst M'
  subst N'
  let g := leviPointsEquiv p l hp hl
  have hg (m : pointImage (l ≫ p)) : e (g.symm m) = m := by
    apply Subtype.ext
    exact (he (g.symm m)).trans (congrArg Subtype.val (g.apply_symm_apply m))
  let σ₀ := SmoothRep.pullback g.symm (SmoothRep.pullback e B)
  let E : σ₀.representation.Equiv B.representation :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun m => by
      change (LinearEquiv.refl ℂ B).toLinearMap ∘ₗ B.representation (e (g.symm m)) =
        B.representation m ∘ₗ (LinearEquiv.refl ℂ B).toLinearMap
      rw [hg]
      rfl
  let h₀ := isSemidirectDecomposition_pointImage p l n hp.isClosedSubgroup hn hmul
  let hN₀ := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  let E₀ := normalizedInductionEquivOfEquiv h₀ hN₀ E
  let E₁ := normalizedInductionLeviEquiv h hN hδ B
  refine ⟨E₀.trans E₁, fun f x => ?_⟩
  exact (normalizedInductionLeviEquiv_eval h hN hδ B (E₀ f) x).trans
    (normalizedInductionEquivOfEquiv_eval h₀ hN₀ E f x)

/-- The represented normalized induction and the actual Levi-normalized
induction agree over identical parabolic, Levi and radical point images. -/
def representedPointInductionEquiv : (represented).representation.Equiv (actual).representation :=
  (representedPointInductionData p l n hp hl hn hmul h hN hδ eP eM eN e he B).val

/-- The comparison preserves the value at every ambient element. -/
theorem representedPointInductionEquiv_eval (f : represented) (x : rationalPoints G) :
    eval _ _ (representedPointInductionEquiv p l n hp hl hn hmul h hN hδ
      eP eM eN e he B f) x = eval _ _ f x :=
  (representedPointInductionData p l n hp hl hn hmul h hN hδ eP eM eN e he B).property f x

end PointImage

namespace DynamicCommonLeviPresentations

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (d : ParabolicData χ ψ T a)

include hG in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The displayed represented radical gives the multiplication isomorphism. -/
theorem multiplication_isIso : IsIso (subgroupMultiplication d.l d.n) := by
  let := hG.smooth
  exact d.r.isIso_subgroupMultiplication_of_radical d.radical

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem pointImage_parabolic : pointImage d.p = parabolic ψ :=
  (pointImage_eq_range_carrier d.p).trans
    (congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) d.realizes.parabolic)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem pointImage_radical : pointImage (d.n ≫ d.p) = radical ψ :=
  (pointImage_eq_range_carrier (d.n ≫ d.p)).trans
    (congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) d.realizes.radical)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem pointImage_levi : pointImage (d.l ≫ d.p) = levi χ :=
  (pointImage_eq_range_carrier (d.l ≫ d.p)).trans
    (congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) d.realizes.levi)

variable (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (B : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option quotPrecheck false in
local notation "represented" => (leviInductionFunctor d.p d.l d.n d.r.isCompatible.parabolic
  d.radical d.r.isCompatible.levi (multiplication_isIso hG d)).obj
    (SmoothRep.pullback (parameterHomeomorph χ) B)
set_option quotPrecheck false in
local notation "actual" => (DynamicNormalization.leviTwistedInductionFunctor
  (commonDecomposition χ ψ hψ) (radical_isClosed ψ)).obj B

/-- Every represented vertex uses the same intrinsic inducing representation
and compares to its actual ambient sections pointwise. -/
def representedDynamicInductionEquiv : (represented).representation.Equiv (actual).representation :=
  representedPointInductionEquiv d.p d.l d.n d.r.isCompatible.parabolic d.r.isCompatible.levi
    d.radical (multiplication_isIso hG d) (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (radical_unimodular ψ hG) (pointImage_parabolic d) (pointImage_levi d) (pointImage_radical d)
    (parameterHomeomorph χ) (fun m => by
      rw [d.levi_comp]
      exact dynamicCentralizerPointHomeomorph_apply_coe F G χ m) B

/-- The comparison uses the identity on the original coefficient carrier. -/
theorem representedDynamicInductionEquiv_eval (f : represented) (x : rationalPoints G) :
    eval _ _ (representedDynamicInductionEquiv hG d hψ B f) x = eval _ _ f x :=
  representedPointInductionEquiv_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f x

end DynamicCommonLeviPresentations

end Langlands.Plancherel
