import Langlands.Representation.Jacquet.ScalarExtension
import Langlands.Representation.Plancherel.UnramifiedUniversalTwist
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Langlands.Representation.Plancherel.RationalParabolicCuspidality
import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups
import Langlands.Topology.CompactNormCharacter

/-! # Universal unramified twists and proper rational Jacquet vanishing -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uG uH uI uV u

section Universal

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance universalJacquetTensorAddCommGroup :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] E) :=
  TensorProduct.addCommGroup

/-- On a subgroup mapped into the full norm kernel, the universal action is
scalar extension of the original action, including after a group pullback. -/
def universalJacquetScalarExtensionEquiv
    (σ : Representation ℂ G E) (f : H →* G) (N : Subgroup H)
    (hN : N ≤ (commonNormKernel ν).comap f) :
    Jacquet.Localization.Coinvariants
        ((universalUnramifiedRepresentation ν σ).comp f) N 1 ≃ₗ[
          unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ]
        Jacquet.Localization.Coinvariants (σ.comp f) N 1 :=
  Jacquet.Localization.scalarExtensionEquiv (σ.comp f)
    ((universalUnramifiedRepresentation ν σ).comp f) N (by
      intro n b v
      change universalUnramifiedRepresentation ν σ (f n) (b ⊗ₜ[ℂ] v) =
        b ⊗ₜ[ℂ] σ (f n) v
      rw [universalUnramifiedRepresentation_tmul,
        unramifiedEvaluationRegular_eq_one_of_mem_commonNormKernel ν (hN n.property),
        one_mul])

/-- Vanishing survives the actual universal twist when the subgroup lies in
the full norm kernel after pullback. -/
theorem subsingleton_universalJacquet
    (σ : Representation ℂ G E) (f : H →* G) (N : Subgroup H)
    (hN : N ≤ (commonNormKernel ν).comap f)
    [Subsingleton (Jacquet.Localization.Coinvariants (σ.comp f) N 1)] :
    Subsingleton (Jacquet.Localization.Coinvariants
      ((universalUnramifiedRepresentation ν σ).comp f) N 1) :=
  (universalJacquetScalarExtensionEquiv ν σ f N hN).injective.subsingleton

end Universal

section Unipotent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

local instance unipotentJacquetPointTopology : TopologicalSpace (rationalPoints U) :=
  rationalPointTopology F U.X

/-- Continuous positive norms kill the image of an actual unipotent point
group: each point lies in a compact subgroup of the source. -/
theorem unipotentPointImage_le_commonNormKernel
    (hν : ∀ i, Continuous (ν i)) (hU : IsUnipotent U)
    (f : rationalPoints U →* G) (hf : Continuous f) :
    f.range ≤ commonNormKernel ν := by
  rintro _ ⟨x, rfl⟩
  apply (mem_commonNormKernel ν (f x)).mpr
  intro i
  obtain ⟨K, hK, hxK⟩ := exists_isCompact_subgroup_superset_of_isUnipotent U hU
    {x} (isCompact_singleton)
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact ((ν i).comp f)
    ((hν i).comp hf) K hK (hxK (Set.mem_singleton x))

end Unipotent

namespace RationalNormalized

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance rationalJacquetAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance rationalJacquetAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalJacquetLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The literal image of any geometric parabolic radical in the actual Levi
is killed by every rational norm, through the canonical point homeomorphism. -/
theorem properRadical_le_commonNormKernel
    {Q U : GroupScheme (Spec (CommRingCat.of F))} {q : Q ⟶ M} {n : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    (SubgroupFunctor.range (n ≫ q)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ≤
      (commonNormKernel (parabolicLeviRationalNormCharacters r)).comap
        (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom := by
  have hj : IsClosedSubgroup (n ≫ q) :=
    hn.1.isClosedSubgroup.comp hq.isClosedSubgroup
  let : IsClosedImmersion (n ≫ q).hom.hom.left := hj
  let : IsAffine U.X.left := isAffine_of_isAffineHom (n ≫ q).hom.hom.left
  let : Smooth U.X.hom := hn.1.smooth
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  let f : rationalPoints U →* parabolicLeviPointSubgroup p l :=
    (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom.comp
      (rationalPoints.map (n ≫ q))
  have hf : Continuous f :=
    (parabolicLeviPointHomeomorph r).continuous.comp
      (continuous_rationalPointMap F (n ≫ q).hom.hom)
  have hker := unipotentPointImage_le_commonNormKernel
    (parabolicLeviRationalNormCharacters r)
    (continuous_parabolicLeviRationalNormCharacters r) hn.1.isUnipotent f hf
  rintro m ⟨x, rfl⟩
  exact hker ⟨x, rfl⟩

variable {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance rationalJacquetTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) :=
  TensorProduct.addCommGroup

/-- The native coefficient Jacquet quotient of the actual universal inducing
Levi, along an actual geometric parabolic radical, is the scalar extension of
the original complex Jacquet quotient. -/
def universalProperJacquetScalarExtensionEquiv
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    {Q U : GroupScheme (Spec (CommRingCat.of F))} {q : Q ⟶ M} {n : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    Jacquet.Localization.Coinvariants
        ((universalRepresentation r σ).comp
          (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom)
        ((SubgroupFunctor.range (n ≫ q)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) 1 ≃ₗ[RegularAlgebra r]
      RegularAlgebra r ⊗[ℂ] Jacquet.Localization.Coinvariants
        (leviSchemeRepresentation r σ)
        ((SubgroupFunctor.range (n ≫ q)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) 1 :=
  universalJacquetScalarExtensionEquiv _ σ
    (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom _
    (properRadical_le_commonNormKernel r hq hn)

/-- The supercuspidality condition on the original actual Levi kills every
proper rational Jacquet quotient over the full universal coefficient algebra. -/
theorem universalRepresentation_properJacquet_subsingleton
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsSupercuspidal r σ)
    {Q U : GroupScheme (Spec (CommRingCat.of F))} {q : Q ⟶ M} {n : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hproper : SubgroupFunctor.range q ≠ ⊤)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    Subsingleton (Jacquet.Localization.Coinvariants
      ((universalRepresentation r σ).comp
        (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom)
      ((SubgroupFunctor.range (n ≫ q)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) 1) := by
  let := hσ.2 Q U q n hq hproper hn
  exact (universalProperJacquetScalarExtensionEquiv r σ hq hn).injective.subsingleton

end RationalNormalized

end Langlands.Plancherel
