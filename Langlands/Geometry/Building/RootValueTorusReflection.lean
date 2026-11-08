import Langlands.Geometry.Building.RootValueTorusNormalizer

/-! # Reflection transport for actual torus-restricted root functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Any normalizer shift gives the reflection constant on every ambient point
whenever its actual Weyl action negates the character. -/
theorem RootFunctionFamily.reflection_eq_of_normalizer_shift
    (φ : RootFunctionFamily T G) (a : characterLattice T)
    (n : normalizerPoints i) (v : V T)
    (ha : weylAction i n a = -a) (hshift : n • φ = v +ᵥ φ)
    (g : rationalPoints G) :
    φ a g = φ (-a) ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) +
      ((-eval T a v : ℝ) : WithTop ℝ) := by
  have ha' : weylAction i n⁻¹ (-a) = a := by
    rw [← ha, map_inv]
    exact (weylAction i n).symm_apply_apply a
  have hg : (n : rationalPoints G)⁻¹ *
      ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) *
        (n : rationalPoints G) = g := by group
  have h := congrArg
    (fun ψ : RootFunctionFamily T G =>
      ψ (-a) ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹)) hshift
  simpa only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply,
    ha', hg, eval_neg_char] using h

variable [IsAffineHom G.X.hom]
  (f : S ⟶ T) [Mono (CommGroupScheme.groupHom f ≫ i).hom.hom.left]

section CommonReflection

variable (nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i))
  (nT : normalizerPoints i)
  (hn : (nS : rationalPoints G) = (nT : rationalPoints G))
  {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
  (α : characterLattice S) (v : V S)
  (ha : weylAction (CommGroupScheme.groupHom f ≫ i) nS α = -α)
  (hshift : nT • φ = cocharacterMapReal f v +ᵥ φ)

include hn ha hshift

/-- A common reflecting representative with a supplied upper shift conjugates
the exact canonical subgroups at the resulting lower shifted depths. -/
theorem torusRestrictedRootDepthSubgroup_reflection_shift (r : ℝ) :
    torusRestrictedRootDepthSubgroup hφ f (-α) (r + eval S α v) =
      (torusRestrictedRootDepthSubgroup hφ f α r).map
        (MulAut.conj (nT : rationalPoints G)).toMonoidHom := by
  have hcongr :
      ∀ (ψ : RootFunctionFamily T G) (hψ : IsRootDatumValuation i ψ),
        nT • φ = ψ →
          torusRestrictedRootDepthSubgroup (hφ.normalizer_smul nT) f (-α) r =
            torusRestrictedRootDepthSubgroup hψ f (-α) r := by
    intro ψ hψ heq
    subst ψ
    rfl
  calc
    _ = torusRestrictedRootDepthSubgroup
        (hφ.vadd (cocharacterMapReal f v)) f (-α) r := by
      rw [torusRestrictedRootDepthSubgroup_vadd, eval_neg_char, sub_neg_eq_add]
    _ = torusRestrictedRootDepthSubgroup (hφ.normalizer_smul nT) f
        (weylAction (CommGroupScheme.groupHom f ≫ i) nS α) r := by
      rw [ha]
      exact (hcongr _ _ hshift).symm
    _ = _ := torusRestrictedRootDepthSubgroup_normalizer_smul f nS nT hn hφ α r

/-- The reflection comparison is an actual conjugation equivalence between
subgroups of the original ambient rational-point group. -/
def torusRestrictedRootReflectionPointsEquiv (r : ℝ) :
    ↥(torusRestrictedRootDepthSubgroup hφ f α r) ≃*
      ↥(torusRestrictedRootDepthSubgroup hφ f (-α) (r + eval S α v)) :=
  ((MulAut.conj (nT : rationalPoints G)).subgroupMap
    (torusRestrictedRootDepthSubgroup hφ f α r)).trans
    (MulEquiv.subgroupCongr
      (torusRestrictedRootDepthSubgroup_reflection_shift
        f nS nT hn hφ α v ha hshift r).symm)

@[simp] theorem torusRestrictedRootReflectionPointsEquiv_val (r : ℝ)
    (g : ↥(torusRestrictedRootDepthSubgroup hφ f α r)) :
    (torusRestrictedRootReflectionPointsEquiv
      (i := i) (φ := φ) f nS nT hn hφ α v ha hshift r g).val =
      (nT : rationalPoints G) * g.val * (nT : rationalPoints G)⁻¹ := by
  rfl

variable [Smooth G.X.hom]

/-- The supplied upper shift gives the exact lower reflection value law,
with constant minus the lower character evaluation. -/
theorem torusRestrictedRootFunctionFamily_reflection_shift
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (g : rationalPoints G) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α g =
      torusRestrictedRootFunctionFamily hS hT hE hφ f (-α)
        ((nS : rationalPoints G) * g * (nS : rationalPoints G)⁻¹) +
          ((-eval S α v : ℝ) : WithTop ℝ) := by
  exact RootFunctionFamily.reflection_eq_of_normalizer_shift
    (torusRestrictedRootFunctionFamily hS hT hE hφ f) α nS v ha
    (torusRestrictedRootFunctionFamily_normalizer_shift
      f nS nT hn hS hT hE hφ v hshift) g

end CommonReflection

variable [Smooth G.X.hom]

/-- Common upper reflecting representatives and shifts supply precisely V2
for the constructed family; their structural existence remains a premise. -/
theorem torusRestrictedRootFunctionFamily_reflection_of_common_lifts
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (hlift : ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i),
      ∀ nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i),
        RealizesReflection (CommGroupScheme.groupHom f ≫ i) α nS →
          ∃ (nT : normalizerPoints i) (v : V S),
            (nS : rationalPoints G) = (nT : rationalPoints G) ∧
              nT • φ = cocharacterMapReal f v +ᵥ φ) :
    ∀ α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i),
      ∀ nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i),
        RealizesReflection (CommGroupScheme.groupHom f ≫ i) α nS →
          ∃ c : ℝ, ∀ g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α,
            g ≠ 1 →
              torusRestrictedRootFunctionFamily hS hT hE hφ f α g =
                torusRestrictedRootFunctionFamily hS hT hE hφ f (-α)
                  ((nS : rationalPoints G) * g * (nS : rationalPoints G)⁻¹) +
                    (c : WithTop ℝ) := by
  intro α hα nS hreflect
  obtain ⟨nT, v, hn, hshift⟩ := hlift α hα nS hreflect
  refine ⟨-eval S α v, fun g _ _ => ?_⟩
  exact torusRestrictedRootFunctionFamily_reflection_shift
    f nS nT hn hφ α v hreflect.1 hshift hS hT hE g

end Langlands.Geometry.Building
