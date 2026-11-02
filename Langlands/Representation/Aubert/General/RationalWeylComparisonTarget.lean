import Langlands.Representation.Aubert.General.RationalPointFamily
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Scheme and point-image relative Weyl comparisons

The two subgroup equalities are separate targets at actual local-field scope.
The quotient equivalence is constructed only from both equalities, and preserves
the underlying normalizer representative.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- Scheme-normalizing points normalize the actual image of the torus points. -/
theorem normalizerPoints_le_pointNormalizer :
    normalizerPoints i ≤ Group.RelativeWeyl.normalizer (torusPoints i) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro n ⟨σ, hσ⟩ g hg
  rcases (mem_torusPoints i g).mp hg with ⟨t, rfl⟩
  apply (mem_torusPoints i _).mpr
  refine ⟨t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom, ?_⟩
  have h := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom) hσ
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
    constantPoint_self] at h
  exact h.symm

/-- Equality of the scheme normalizer points and the actual point-image
normalizer. This is stronger than the elementary inclusion. -/
def HasPointNormalizerComparison : Prop :=
  normalizerPoints i = Group.RelativeWeyl.normalizer (torusPoints i)

/-- Equality of the scheme centralizer points and the full centralizer of
the actual point image. This does not replace the denominator by the torus. -/
def HasPointCentralizerComparison : Prop :=
  centralizerPoints i = Group.RelativeWeyl.centralizer (torusPoints i)

/-- Both comparisons, on a genuine maximal split torus in the actual
connected-reductive nonarchimedean local-field scope. -/
def RationalWeylComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
        HasPointNormalizerComparison i ∧ HasPointCentralizerComparison i

/-- The numerator comparison preserves the actual ambient point. -/
def normalizerEquiv (hN : HasPointNormalizerComparison i) :
    normalizerPoints i ≃* Group.RelativeWeyl.normalizer (torusPoints i) :=
  MulEquiv.subgroupCongr hN

@[simp] theorem normalizerEquiv_apply (hN : HasPointNormalizerComparison i)
    (n : normalizerPoints i) :
    (normalizerEquiv i hN n : RationalPoint k G.X) = n :=
  rfl

/-- Under both subgroup comparisons the entire restricted centralizer
denominator is transported, not just a subgroup contained in it. -/
theorem normalizerEquiv_map_denominator
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i) :
    ((centralizerPoints i).subgroupOf (normalizerPoints i)).map
        (normalizerEquiv i hN).toMonoidHom =
      Group.RelativeWeyl.denominator (torusPoints i) := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    change (m : RationalPoint k G.X) ∈
      Group.RelativeWeyl.centralizer (torusPoints i)
    exact hZ ▸ hm
  · intro hn
    refine ⟨(normalizerEquiv i hN).symm n, ?_, MulEquiv.apply_symm_apply _ _⟩
    change (n : RationalPoint k G.X) ∈ centralizerPoints i
    exact hZ.symm ▸ hn

/-- The scheme-point and actual image-subgroup relative Weyl groups agree
once both exact numerator and denominator comparisons have been supplied. -/
def weylEquiv (hN : HasPointNormalizerComparison i)
    (hZ : HasPointCentralizerComparison i) :
    relativeWeylGroup i ≃* Weyl i :=
  QuotientGroup.congr
    ((centralizerPoints i).subgroupOf (normalizerPoints i))
    (Group.RelativeWeyl.denominator (torusPoints i))
    (normalizerEquiv i hN) (normalizerEquiv_map_denominator i hN hZ)

@[simp] theorem weylEquiv_mk (hN : HasPointNormalizerComparison i)
    (hZ : HasPointCentralizerComparison i) (n : normalizerPoints i) :
    weylEquiv i hN hZ (QuotientGroup.mk n) =
      QuotientGroup.mk (normalizerEquiv i hN n) :=
  rfl

/-- Finiteness transfers to the actual quotient through the constructed
equivalence; this lemma proves no scheme-Weyl finiteness assertion. -/
theorem finite_weyl_of_scheme (hN : HasPointNormalizerComparison i)
    (hZ : HasPointCentralizerComparison i) [Finite (relativeWeylGroup i)] :
    Finite (Weyl i) :=
  Finite.of_surjective (weylEquiv i hN hZ) (weylEquiv i hN hZ).surjective

end Langlands.Aubert.General.RationalPointFamily
