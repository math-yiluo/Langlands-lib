import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement
import Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessStatement
import Langlands.Geometry.Building.Kottwitz.KernelTransport
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelStatement
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Torus.Induced

/-! # Reducing the unramified kernel clause of KP Proposition 11.5.3 to named inputs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- The first conjunct of `ZExtensionKottwitzKernelSurjectivityStatement`, verbatim: points
with coefficients in `K = UnramifiedClosure F` of groups over a compatible field `k`. -/
def ZExtensionUnramifiedKottwitzKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (z : ZExtension G),
    (reductiveKottwitz F k z.H z.isZExtension.source_reductive).ker.map
        (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F))) =
      (reductiveKottwitz F k G hG).ker

/-- The second conjunct of `ZExtensionKottwitzKernelSurjectivityStatement`, verbatim:
`F`-rational points and the rational maps. -/
def ZExtensionRationalKottwitzKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (z : ZExtension G),
    (reductiveKottwitzRational F z.H z.isZExtension.source_reductive).ker.map
        (rationalPoints.map z.p) =
      (reductiveKottwitzRational F G hG).ker

/-- The published statement is exactly the conjunction of its two named conjuncts. -/
theorem zExtensionKottwitzKernelSurjectivityStatement_iff :
    ZExtensionKottwitzKernelSurjectivityStatement.{u} ↔
      ZExtensionUnramifiedKottwitzKernelStatement.{u} ∧
        ZExtensionRationalKottwitzKernelStatement.{u} :=
  Iff.rfl

/-- KP Proposition 11.5.3, kernel clause over `K`, reduced to KP Lemma 11.5.1 (existence
with surjectivity, and functoriality) and right exactness of inertia coinvariants for a
central torus quotient. -/
def ZExtensionUnramifiedKernelReductionStatement : Prop :=
  ReductiveKottwitzExistenceStatement.{u} →
  ReductiveKottwitzFunctorialityStatement.{u} →
  CentralTorusInertiaExactnessStatement.{u} →
  ZExtensionUnramifiedKottwitzKernelStatement.{u}

/-- Proof of the reduction: `map_kernel_eq_of_kernel_lift` for the point map of `z.p`, with
the square from functoriality for `z.p`, and lifts through `Z(K)` from surjectivity of the
torus map, functoriality for `z.i` and `z.i ≫ z.p = 1` on points. -/
theorem zExtensionUnramifiedKernelReduction :
    ZExtensionUnramifiedKernelReductionStatement.{u} := by
  intro hexist hfunct hexact F _ _ _ _ k _ _ _ _ _ _ G hG z
  have hH : IsConnectedReductive z.H := z.isZExtension.source_reductive
  have hZ : IsConnectedReductive z.Z.toGrp :=
    z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting
  refine map_kernel_eq_of_kernel_lift
    (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F)))
    (reductiveKottwitz F k z.H hH) (reductiveKottwitz F k G hG)
    (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
      G hG z.H hH z.p).toAddMonoidHom.toMultiplicative
    ((hexist F k G hG).2.2.2.2.2 z).1 ?_ ?_
  · intro h
    exact congrArg Multiplicative.ofAdd ((hfunct F k).1 z.H G hH hG z.p h)
  · intro a ha
    have hker : a.toAdd ∈ LinearMap.ker
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H hH z.p) := by
      rw [LinearMap.mem_ker]
      exact congrArg Multiplicative.toAdd ha
    rw [(hexact.zExtension k (UnramifiedClosure F) (SeparableClosure F) z).2] at hker
    obtain ⟨b, hb⟩ := hker
    obtain ⟨x, hx⟩ := (hexist F k z.Z.toGrp hZ).2.2.2.1 (Multiplicative.ofAdd b)
    refine ⟨affinePointsTarget z.Z.toGrp z.i (CommAlgCat.of k (UnramifiedClosure F)) x,
      ?_, ?_⟩
    · rw [MonoidHom.mem_ker, affinePointsTarget_apply, affinePointsTarget_apply,
        Category.assoc]
      exact comp_quotient_eq_one z.isZExtension.quotient.2.2.2 x
    · apply Multiplicative.toAdd.injective
      rw [(hfunct F k).1 z.Z.toGrp z.H hZ hH z.i x, hx]
      exact hb

end Langlands.Geometry.Building.Kottwitz
