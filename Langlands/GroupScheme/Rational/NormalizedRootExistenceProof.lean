import Langlands.GroupScheme.Rational.NormalizedRootExistenceStatement
import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Reductive.PinnedRigidityReduction
import Langlands.GroupScheme.Reductive.RootScalingAutomorphism

/-! # Existence of root maps normalized by a supplied split pinning -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable (k : Type u) [Field k]

local instance : IsAffineHom (groupScheme (CommRingCat.of k) 1).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of k) 1

/-- The actual standard epsilon vector of the additive group is nonzero. -/
theorem standardEpsilon_ne_zero : standardEpsilon k ≠ 0 := by
  let e := coordinates (CommRingCat.of k) 1
  have he : RelativeRoot.IsNaturalVectorCoordinates e := isNaturalVectorCoordinates
  have hcoord :
      RelativeRoot.vectorLieCoordinates e he (CommAlgCat.of k k) (standardEpsilon k) =
        fun _ => (1 : k) :=
    (RelativeRoot.vectorLieCoordinates e he (CommAlgCat.of k k)).apply_symm_apply _
  intro h
  rw [h, LinearEquiv.map_zero] at hcoord
  exact zero_ne_one (congrFun hcoord 0)

end VectorGroup

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

/-- Every simple intrinsic root functor has an additive parametrization whose
actual differential is the prescribed pinning vector. -/
theorem nonempty_normalizedRootParametrization (a : p.base.support) :
    Nonempty (p.NormalizedRootParametrization a) := by
  classical
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  have ha := (p.root_mem_relativeRoots a).1
  have hhigh := p.hasNoHigherRoots a
  obtain ⟨U, j, hj, hjclosed, _, _⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero p.isSplitTorus
      p.inclusion (p.rootDatum.root a) ha
  let : IsAffineHom U.X.hom := hjclosed.isAffineHom
  let : Mono j.hom.hom := hj.1
  obtain ⟨n, e, he⟩ := RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots
    p.isSplitTorus p.inclusion ha hhigh hj
  have hn : n = 1 := by
    have hd := (((RelativeRoot.vectorLieCoordinates e he.1 (CommAlgCat.of k k)).symm.trans
      (RelativeRoot.representedRootLieEquiv p.isSplitTorus p.inclusion ha hhigh hj)).trans
        (p.pinning.trivialization a).symm).finrank_eq
    simpa using hd
  subst n
  let E := RelativeRoot.vectorGroupIso e he.1
  let f₀ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G := E.inv ≫ j
  have hf₀ : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).IsRepresentedBy f₀ := by
    refine ⟨by
      change Mono (E.inv.hom.hom ≫ j.hom.hom)
      infer_instance, ?_⟩
    change SubgroupFunctor.range (E.symm.hom ≫ j) = _
    rw [SubgroupFunctor.range_iso_comp]
    exact hj.2
  have hf₀closed : IsClosedSubgroup f₀ :=
    (IsClosedSubgroup.of_iso E.symm).comp hjclosed
  have hE (T : Over (Spec (CommRingCat.of k)))
      (v : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
      e T (v ≫ E.inv.hom.hom) = VectorGroup.coordinates (CommRingCat.of k) 1 T v := by
    have h := RelativeRoot.coordinates_comp_vectorGroupIso_hom e he.1 T
      (v ≫ E.inv.hom.hom)
    change VectorGroup.coordinates (CommRingCat.of k) 1 T
      ((v ≫ E.inv.hom.hom) ≫ E.hom.hom.hom) = _ at h
    simpa only [Category.assoc, ← Grp.comp_hom_hom, E.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] using h.symm
  have hf₀equiv (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ p.torus.X)
      (c : Γ(T.left, ⊤)) :
      (t ≫ p.inclusion.hom.hom) *
          (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ f₀.hom.hom) *
          (t ≫ p.inclusion.hom.hom)⁻¹ =
        VectorGroup.scalarPoint (CommRingCat.of k) T
          (VectorGroup.charValue (p.rootDatum.root a) T t * c) ≫ f₀.hom.hom := by
    simp only [f₀, Grp.comp_hom_hom, ← Category.assoc]
    rw [← RelativeRoot.subgroupAction_act_comp p.inclusion (p.rootDatum.root a) j hj]
    apply congrArg (fun v : T ⟶ U.X => v ≫ j.hom.hom)
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    rw [he.2, hE, hE]
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, VectorGroup.coordinates_scalarPoint]
    rfl
  let L := (RelativeRoot.representedRootLieEquiv p.isSplitTorus p.inclusion ha hhigh hf₀).trans
    (p.pinning.trivialization a).symm
  let c : k := L (VectorGroup.standardEpsilon k)
  have hc : c ≠ 0 := by
    intro hc
    exact VectorGroup.standardEpsilon_ne_zero k (L.injective (hc.trans L.map_zero.symm))
  have hd₀ : Lie.targetMapLinear f₀ (CommRingCat.of k) (VectorGroup.standardEpsilon k) =
      c • p.pinning.rootVector a := by
    have h := p.pinning.trivialization_apply_val a c
    have hcvec : p.pinning.trivialization a c =
        RelativeRoot.representedRootLieEquiv p.isSplitTorus p.inclusion ha hhigh hf₀
          (VectorGroup.standardEpsilon k) :=
      (p.pinning.trivialization a).apply_symm_apply _
    rw [hcvec] at h
    exact h
  let s : p.base.support → kˣ := fun _ => (Units.mk0 c hc)⁻¹
  let σ := p.rootScalingIso s
  have hi : p.inclusion ≫ σ.hom = p.inclusion := p.rootScalingIso_inclusion s
  let τ := RelativeRoot.rootIsoOfFixesTorus p.inclusion (p.rootDatum.root a) f₀ hf₀ σ hi
  have hτ : τ.hom ≫ f₀ = f₀ ≫ σ.hom :=
    RelativeRoot.rootHomOfFixesTorus_comp p.inclusion (p.rootDatum.root a) f₀ hf₀ σ.hom hi
  refine ⟨{
    hom := f₀ ≫ σ.hom
    represents := ?_
    isClosedSubgroup := hf₀closed.comp (IsClosedSubgroup.of_iso σ)
    torus_equivariant := ?_
    derivative := ?_
  }⟩
  · rw [← hτ]
    refine ⟨by
      let := hf₀.1
      change Mono (τ.hom.hom.hom ≫ f₀.hom.hom)
      infer_instance, ?_⟩
    rw [SubgroupFunctor.range_iso_comp]
    exact hf₀.2
  · intro T t z
    have ht : (t ≫ p.inclusion.hom.hom) ≫ σ.hom.hom.hom = t ≫ p.inclusion.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun f : p.torus.toGrp ⟶ G => t ≫ f.hom.hom) hi
    have h := congrArg (fun v : T ⟶ G.X => v ≫ σ.hom.hom.hom) (hf₀equiv T t z)
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, ht,
      Grp.comp_hom_hom, Category.assoc] using h
  · have hcomp :
        Lie.targetMapLinear (f₀ ≫ σ.hom) (CommRingCat.of k) (VectorGroup.standardEpsilon k) =
          Lie.targetMapLinear σ.hom (CommRingCat.of k)
            (Lie.targetMapLinear f₀ (CommRingCat.of k) (VectorGroup.standardEpsilon k)) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp only [lieKernelTargetLinear_val, Grp.comp_hom_hom, Category.assoc]
    rw [hcomp, hd₀, map_smul]
    change c • Lie.targetMapLinear (p.rootScalingIso s).hom (CommRingCat.of k)
      (p.pinning.rootVector a) = _
    rw [p.rootScalingIso_rootVector]
    change c • (c⁻¹ • p.pinning.rootVector a) = _
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Choose the actual rational simple-reflection witnesses already contained
in the supplied root datum. -/
def simpleReflectionRepresentative (a : p.base.support) : p.SimpleReflectionRepresentative a :=
  let h := p.isRootDatum.2.2 a
  { point := h.choose
    torusAut := h.choose_spec.choose
    normalizes := h.choose_spec.choose_spec.1
    characterAut_eq := h.choose_spec.choose_spec.2 }

end SplitPinning

/-- The exact arbitrary-field existence statement, with no additional premise. -/
theorem normalizedRootExistence : NormalizedRootExistenceStatement.{u} := by
  intro k _ G _ p
  exact ⟨⟨fun a => Classical.choice (p.nonempty_normalizedRootParametrization a)⟩,
    ⟨p.simpleReflectionRepresentative⟩⟩

end Langlands.GroupScheme
