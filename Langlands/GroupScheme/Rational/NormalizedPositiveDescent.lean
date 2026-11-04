import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility
import Langlands.GroupScheme.Rational.FppfQuotientAction
import Langlands.GroupScheme.Rational.TangentWeightTransport
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.PositiveCentralDescent
import Langlands.GroupScheme.Lie.WeightSupportGalois
import Langlands.GroupScheme.GeometricConnectedness

/-! # Positive descent for an actual normalized subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AutomorphicAction

section Equivariance

variable {B B' : Scheme.{u}} {H U G : GroupScheme B}
    {d : AutomorphicAction H U} {c : AutomorphicAction H G}
    {i : U ⟶ G} (hi : d.IsEquivariant c i)

include hi in
/-- Restriction of the acting group preserves all-test equivariance. -/
theorem IsEquivariant.restrict {J : GroupScheme B} (t : J ⟶ H) :
    (d.restrict t).IsEquivariant (c.restrict t) i := by
  intro V s x
  simpa only [restrict_act] using hi (s ≫ t.hom.hom) x

include hi in
/-- Arbitrary scheme base change preserves all-test equivariance. -/
theorem IsEquivariant.baseChange (b : B' ⟶ B) :
    (d.baseChange b).IsEquivariant (c.baseChange b)
      ((GroupScheme.baseChange b).map i) := by
  intro V s x
  apply (baseChangePointsEquiv b G V).injective
  rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_act,
    baseChangePointsEquiv_act, baseChangePointsEquiv_comp]
  exact hi _ _

end Equivariance
end AutomorphicAction

section SourcePositivity

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {M U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M.X.hom] [Smooth M.X.hom] [ConnectedSpace M.X.left]
    [IsAffineHom U.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ M) [Mono t.hom.hom.left]
    (j : M ⟶ G) (d : AutomorphicAction M U) (i : U ⟶ G) [Mono i.hom.hom]
    (hi : d.IsEquivariant (AutomorphicAction.conjugation j) i)

include hi in
/-- Weyl averaging gives a central positive direction on the actual source
weight spaces of a normalized monomorphic subgroup. -/
theorem HasRelativeRootSystem.exists_centralCocharacter_positive_on_source
    (hroot : HasRelativeRootSystem t) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T)
    (hpos : ∀ χ : characterLattice T,
      RelativeRoot.actionWeightSpace (d.restrict t) χ ≠ ⊥ →
        0 < latticePairing T χ ν) :
    ∃ νc : cocharacterLattice T, νc ∈ centralCocharacters t ∧
      ∀ χ : characterLattice T,
        RelativeRoot.actionWeightSpace (d.restrict t) χ ≠ ⊥ →
          0 < latticePairing T χ νc := by
  have hit : (d.restrict t).IsEquivariant
      (AutomorphicAction.conjugation (t ≫ j)) i := by
    intro V s x
    simpa only [AutomorphicAction.restrict_conjugation] using hi.restrict t s x
  have hs (χ : characterLattice T) :=
    RelativeRoot.mem_actionWeightSupport_range_iff
      (AutomorphicAction.conjugation (t ≫ j)) (d.restrict t) i
      (fun V s x => hit s x) χ
  obtain ⟨νc, hc, hp⟩ := hroot.exists_centralCocharacter_positive
    t j (SubgroupFunctor.range i) hi.isStable_range hT ν
    (fun χ hχ => hpos χ ((hs χ).mp hχ))
  exact ⟨νc, hc, fun χ hχ => hp χ ((hs χ).mpr hχ)⟩

end SourcePositivity

namespace RelativeRoot

section GaloisRange

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffineHom G.X.hom]
    (d : AutomorphicAction T.toGrp U) (c : AutomorphicAction T.toGrp G)
    (i : U ⟶ G) [Mono i.hom.hom] (hi : d.IsEquivariant c i)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T

local instance : IsAffineHom ((GroupScheme.baseChange b).obj U).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom b)
  infer_instance

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

set_option backward.isDefEq.respectTransparency true in
include hi in
/-- Galois transport preserves and reflects ambient support for the range of
an actual descended equivariant monomorphic subgroup. -/
theorem mem_actionWeightSupport_range_galois_iff
    (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    characterLattice.galoisRepresentation k K T σ χ ∈
        actionWeightSupport (S := T_K) (c.baseChange b)
          (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) ↔
      χ ∈ actionWeightSupport (S := T_K) (c.baseChange b)
        (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) := by
  let : Mono ((GroupScheme.baseChange b).map i).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))
  have hiK : (d.baseChange b).IsEquivariant (c.baseChange b)
      ((GroupScheme.baseChange b).map i) := by
    intro V s x
    exact hi.baseChange b s x
  have hs (ψ : characterLattice T_K) :=
    mem_actionWeightSupport_range_iff (S := T_K) (c.baseChange b) (d.baseChange b)
      ((GroupScheme.baseChange b).map i) (fun V s x => hiK s x) ψ
  rw [hs, hs]
  exact actionWeightSpace_galois_ne_bot_iff k K d σ χ

end GaloisRange
end RelativeRoot

section PositiveDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
    {M U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M.X.hom] [Smooth M.X.hom] [ConnectedSpace M.X.left]
    [IsAffineHom U.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ M) [Mono t.hom.hom.left]
    (j : M ⟶ G) (d : AutomorphicAction M U) (i : U ⟶ G) [Mono i.hom.hom]
    (hi : d.IsEquivariant (AutomorphicAction.conjugation j) i)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "M_K" => Functor.obj (GroupScheme.baseChange b) M
local notation "t_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) t
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "d_K" => d.baseChange b

local instance : IsAffineHom ((GroupScheme.baseChange b).obj U).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom b)
  infer_instance

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : IsAffineHom (M_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd M.X.hom b)
  infer_instance

local instance : Smooth (M_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd M.X.hom b)
  infer_instance

local instance : ConnectedSpace (M_K).X.left :=
  M.connectedSpace_baseChange_of_smooth_affine b

local instance : Mono (i_K).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))

local instance : Mono (t_K).hom.hom.left := by
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : Mono (t_K).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map t.hom.hom))
  exact Over.mono_left_of_mono _

include hi in
/-- A positive direction on the actual descended source can be made central
and descended over the original field, preserving every source weight. -/
theorem exists_centralCocharacter_positive_on_descended_source
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    ∃ νc : cocharacterLattice T, νc ∈ centralCocharacters t ∧
      ∀ χ : characterLattice T_K,
        RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
          0 < latticePairing T_K χ (cocharacterLattice.baseChange b T νc) := by
  have hiK : (d_K).IsEquivariant (AutomorphicAction.conjugation j_K) i_K := by
    intro V s x
    have h := hi.baseChange b s x
    simpa only [AutomorphicAction.baseChange_conjugation] using h
  obtain ⟨νw, hw, hp⟩ :=
    HasRelativeRootSystem.exists_centralCocharacter_positive_on_source
      (T := T_K) t_K j_K d_K i_K hiK hroot hT ν hpos
  let Φ : Set (characterLattice T_K) :=
    {χ | RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥}
  have hΦ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) (hχ : χ ∈ Φ) :
      characterLattice.galoisRepresentation k K T σ χ ∈ Φ :=
    (RelativeRoot.restricted_actionWeightSpace_galois_ne_bot_iff k K d t σ χ).mpr hχ
  exact exists_centralCocharacter_positive_of_galois_stable
    k K T t Φ hΦ νw hw hp

section SplitComponent

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ t = a)

include hi ha hf in
/-- The descended central positive direction has an actual integral factor
through the specified split component and the supplied lift. -/
theorem IsSplitComponent.exists_positiveCocharacter_on_source
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    ∃ ζ : cocharacterLattice A,
      ∀ χ : characterLattice T_K,
        RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
          0 < latticePairing T_K χ
            (cocharacterLattice.baseChange b T (RealTorusSpace.cocharacterMapInt f ζ)) := by
  obtain ⟨νc, hc, hp⟩ :=
    exists_centralCocharacter_positive_on_descended_source k K T t j d i hi hroot hT ν hpos
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters f hf] at hc
  obtain ⟨ζ, hζ⟩ := hc
  exact ⟨ζ, fun χ hχ => by rw [hζ]; exact hp χ hχ⟩

include hi ha hf in
/-- A chosen actual integral cocharacter of the specified split component,
positive on every weight of the descended source after extension. -/
def IsSplitComponent.positiveSourceCocharacter
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    cocharacterLattice A :=
  Classical.choose
    (ha.exists_positiveCocharacter_on_source k K T t j d i hi f hf hroot hT ν hpos)

include hi ha hf in
/-- The chosen split-component cocharacter pairs positively with every
original source weight after extension and postcomposition with the lift. -/
theorem IsSplitComponent.positiveSourceCocharacter_spec
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ
          (cocharacterLattice.baseChange b T (RealTorusSpace.cocharacterMapInt f
            (ha.positiveSourceCocharacter k K T t j d i hi f hf hroot hT ν hpos))) :=
  Classical.choose_spec
    (ha.exists_positiveCocharacter_on_source k K T t j d i hi f hf hroot hT ν hpos)

include hi ha hf in
/-- Every actual source weight restricts nontrivially to the extended
specified split component. -/
theorem IsSplitComponent.sourceCharacterRestriction_ne_zero
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν)
    (χ : characterLattice T_K)
    (hχ : RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥) :
    (CommGroupScheme.baseChange b).map f ≫ χ ≠ 0 := by
  intro hzero
  obtain ⟨ζ, hp⟩ :=
    ha.exists_positiveCocharacter_on_source k K T t j d i hi f hf hroot hT ν hpos
  have hz : latticePairing T_K χ
      (cocharacterLattice.baseChange b T (RealTorusSpace.cocharacterMapInt f ζ)) = 0 := by
    change gmEndEquiv K
      (((Gm.commBaseChangeIso b).inv ≫
        (CommGroupScheme.baseChange b).map (ζ ≫ f)) ≫ χ) = 0
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, hzero,
      Limits.comp_zero, map_zero]
  have hpχ := hp χ hχ
  omega

end SplitComponent
end PositiveDescent

end Langlands.GroupScheme
