import Langlands.GroupScheme.Rational.PositiveCompatibleCocharacter
import Langlands.GroupScheme.Rational.NormalizedPositiveDescent
import Langlands.GroupScheme.Rational.NormalizedWeightSum

/-! # Whole-torus centralizer refinement preserving actual source weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Pairing

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The integral form obtained by postcomposition with a specified torus map,
base change, and pairing with an actual character over the extension. -/
def extendedSourceWeightForm (f : A ⟶ T)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    cocharacterLattice A →+ ℤ :=
  (latticePairing _ χ).toAddMonoidHom.comp
    ((cocharacterLattice.baseChange (algebraBaseMap k K) T).comp
      (RealTorusSpace.cocharacterMapInt f).toAddMonoidHom)

@[simp]
theorem extendedSourceWeightForm_apply (f : A ⟶ T)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (ζ : cocharacterLattice A) :
    extendedSourceWeightForm (k := k) (K := K) f χ ζ =
      latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
        (cocharacterLattice.baseChange (algebraBaseMap k K) T
          (RealTorusSpace.cocharacterMapInt f ζ)) := rfl

end Pairing

section SourceRefinement

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (t : T.toGrp ⟶ G) (d : AutomorphicAction T.toGrp U)
    (i : U ⟶ G) [Mono i.hom.hom]
    (hi : d.IsEquivariant (AutomorphicAction.conjugation t) i)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "t_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) t
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "d_K" => d.baseChange b

local instance positiveSourceRefinementSourceIsAffineHomU :
    IsAffineHom ((GroupScheme.baseChange b).obj U).X.hom := by
  change IsAffineHom (Limits.pullback.snd U.X.hom b)
  infer_instance

local instance positiveSourceRefinementSourceIsAffineHomG :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

local instance positiveSourceRefinementSourceLocallyOfFiniteTypeG :
    LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd G.X.hom b)
  infer_instance

local instance positiveSourceRefinementSourceMonoI : Mono (i_K).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))

include hi in
/-- An actual source-positive direction of a specified split torus can be
refined to its whole-torus centralizer while preserving all original source
weights over a supplied splitting extension. -/
theorem IsSplitTorus.exists_compatible_cocharacter_positive_on_source
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G)
    (f : A ⟶ T) (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice A)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) d_K χ ≠ ⊥ →
        0 < extendedSourceWeightForm (k := k) (K := K) f χ ν) :
    ∃ ζ : cocharacterLattice A,
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ a) = torusCentralizer a ∧
        Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ a) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ a) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ a) ∧
        ∀ χ : characterLattice T_K,
          RelativeRoot.actionWeightSpace (S := T_K) d_K χ ≠ ⊥ →
            0 < extendedSourceWeightForm (k := k) (K := K) f χ ζ := by
  classical
  have hiK : (d_K).IsEquivariant (AutomorphicAction.conjugation t_K) i_K := by
    intro V s x
    have h := hi.baseChange b s x
    simpa only [AutomorphicAction.baseChange_conjugation] using h
  let F := RelativeRoot.actionWeightSupport (S := T_K)
    (AutomorphicAction.conjugation t_K) (SubgroupFunctor.range i_K)
  have hF : F.Finite :=
    IsSplitTorus.finite_actionWeightSupport (k := K) (T := T_K) hT t_K
      (SubgroupFunctor.range i_K)
  obtain ⟨ζ, hZ, hP, hU, hp⟩ :=
    hA.exists_compatible_cocharacter_on_finite a ν
      (extendedSourceWeightForm (k := k) (K := K) f) hF.toFinset
  refine ⟨ζ, hZ, hP, hU, ?_⟩
  intro χ hχ
  have hmem : χ ∈ F :=
    (RelativeRoot.mem_actionWeightSupport_range_iff (k := K) (S := T_K)
      (AutomorphicAction.conjugation t_K) d_K i_K
      (fun V s x => hiK s x) χ).mpr hχ
  exact hp χ (hF.mem_toFinset.mpr hmem) (hpos χ hχ)

include hi in
/-- A chosen actual whole-torus centralizing cocharacter preserving every
original source weight over the supplied extension. -/
def compatiblePositiveSourceCocharacter
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G)
    (f : A ⟶ T) (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice A)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) d_K χ ≠ ⊥ →
        0 < extendedSourceWeightForm (k := k) (K := K) f χ ν) : cocharacterLattice A :=
  (hA.exists_compatible_cocharacter_positive_on_source k K t d i hi a f hT ν hpos).choose

include hi in
/-- The chosen refinement has the full specified-torus centralizer, the two
dynamic inclusions and strict positivity on every original source weight. -/
theorem compatiblePositiveSourceCocharacter_spec
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G)
    (f : A ⟶ T) (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice A)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) d_K χ ≠ ⊥ →
        0 < extendedSourceWeightForm (k := k) (K := K) f χ ν) :
    let ζ := compatiblePositiveSourceCocharacter k K t d i hi hA a f hT ν hpos
    Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ a) = torusCentralizer a ∧
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ a) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a) ∧
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ a) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ a) ∧
      ∀ χ : characterLattice T_K,
        RelativeRoot.actionWeightSpace (S := T_K) d_K χ ≠ ⊥ →
          0 < extendedSourceWeightForm (k := k) (K := K) f χ ζ :=
  (hA.exists_compatible_cocharacter_positive_on_source k K t d i hi a f hT ν hpos).choose_spec

end SourceRefinement

section NormalizedSource

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
    {M U G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M.X.hom] [Smooth M.X.hom] [ConnectedSpace M.X.left]
    [IsAffineHom U.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (t : T.toGrp ⟶ M) [Mono t.hom.hom.left]
    (j : M ⟶ G) (d : AutomorphicAction M U) (i : U ⟶ G) [Mono i.hom.hom]
    (hi : d.IsEquivariant (AutomorphicAction.conjugation j) i)
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ t = a)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "t_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) t
local notation "d_K" => d.baseChange b

local instance positiveSourceRefinementNormalizedIsAffineHomU :
    IsAffineHom ((GroupScheme.baseChange b).obj U).X.hom := by
  change IsAffineHom (Limits.pullback.snd U.X.hom b)
  infer_instance

local instance positiveSourceRefinementNormalizedMonoT : Mono (t_K).hom.hom.left := by
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : Mono (t_K).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map t.hom.hom))
  exact Over.mono_left_of_mono _

include hi ha hf in
/-- Integral positive descent followed by source-weight refinement yields a
cocharacter of the original specified component with its full ambient torus
centralizer and strict positivity on every original source weight. -/
theorem IsSplitComponent.exists_centralizingPositiveSourceCocharacter
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    ∃ ζ : cocharacterLattice A,
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ a ≫ j) =
          torusCentralizer (a ≫ j) ∧
        ∀ χ : characterLattice T_K,
          RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
            0 < extendedSourceWeightForm (k := k) (K := K) f χ ζ := by
  obtain ⟨νA, hp⟩ :=
    ha.exists_positiveCocharacter_on_source k K T t j d i hi f hf hroot hT ν hpos
  have hit : (d.restrict t).IsEquivariant
      (AutomorphicAction.conjugation (t ≫ j)) i := by
    intro V s x
    simpa only [AutomorphicAction.restrict_conjugation] using hi.restrict t s x
  have hp' (χ : characterLattice T_K)
      (hχ : RelativeRoot.actionWeightSpace (S := T_K)
        ((d.restrict t).baseChange b) χ ≠ ⊥) :
      0 < extendedSourceWeightForm (k := k) (K := K) f χ νA := by
    apply hp χ
    simpa only [AutomorphicAction.baseChange_restrict] using hχ
  obtain ⟨ζ, hZ, _, _, hζ⟩ :=
    IsSplitTorus.exists_compatible_cocharacter_positive_on_source
      k K (t ≫ j) (d.restrict t) i hit ha.1.1.1 (a ≫ j) f hT νA hp'
  refine ⟨ζ, hZ, ?_⟩
  intro χ hχ
  apply hζ χ
  simpa only [AutomorphicAction.baseChange_restrict] using hχ

include hi ha hf in
/-- A chosen integral cocharacter of the specified component with the full
ambient torus centralizer and positive extended source weights. -/
def IsSplitComponent.centralizingPositiveSourceCocharacter
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) : cocharacterLattice A :=
  (ha.exists_centralizingPositiveSourceCocharacter
    k K T t j d i hi f hf hroot hT ν hpos).choose

include hi ha hf in
/-- The chosen cocharacter has the full ambient centralizer of the specified
component and strictly positive pairing with every original source weight. -/
theorem IsSplitComponent.centralizingPositiveSourceCocharacter_spec
    (hroot : HasRelativeRootSystem (T := T_K) t_K)
    (hT : IsSplitTorus (T_K).toGrp)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ : characterLattice T_K,
      RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
        0 < latticePairing T_K χ ν) :
    let ζ := ha.centralizingPositiveSourceCocharacter
      k K T t j d i hi f hf hroot hT ν hpos
    Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ a ≫ j) =
        torusCentralizer (a ≫ j) ∧
      ∀ χ : characterLattice T_K,
        RelativeRoot.actionWeightSpace (S := T_K) ((d_K).restrict t_K) χ ≠ ⊥ →
          0 < extendedSourceWeightForm (k := k) (K := K) f χ ζ :=
  (ha.exists_centralizingPositiveSourceCocharacter
    k K T t j d i hi f hf hroot hT ν hpos).choose_spec

end NormalizedSource

end Langlands.GroupScheme
