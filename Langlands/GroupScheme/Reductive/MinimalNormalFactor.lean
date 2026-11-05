import Langlands.GroupScheme.Reductive.RootCentralizerReduction
import Langlands.GroupScheme.Reductive.NormalSemisimpleReduction
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Derived.Basic

/-! # Minimal normal almost-simple factors from actual-root inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A nontrivial semisimple group is noncommutative, with nontriviality
measured by its full functor of points. -/
theorem IsSemisimple.noncommutative_of_range_ne_bot
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    ¬ ∀ (U : Over (Spec (CommRingCat.of k))) (x y : U ⟶ G.X), Commute x y := by
  intro hcomm
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  let f : G ⟶ Z := hz.isRepresentedBy.factorHom (𝟙 G) (by
    intro U x _ V a y
    exact hcomm V (a ≫ x) y)
  have hf : f ≫ z = 𝟙 G := hz.isRepresentedBy.factorHom_comp _ _
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp hz.1 (by
    rw [hf]
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance)
  let : IsClosedImmersion f.hom.hom.left := hfc
  let : IsFinite Z.X.hom := hfin
  let : IsFinite G.X.hom := by
    rw [← f.hom.hom.w]
    infer_instance
  have hid : (𝟙 G.X : G.X ⟶ G.X) = 1 :=
    finiteTargetOverHom_eq_one_algClosed G G (𝟙 G.X) (by simp)
  apply hnt
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    change x = 1
    calc
      x = x ≫ (𝟙 G.X) := (Category.comp_id _).symm
      _ = 1 := by rw [hid, MonObj.comp_one]
  · intro hx
    refine ⟨x, ?_⟩
    change x ≫ (𝟙 G.X) = x
    exact Category.comp_id _

/-- Closed generation by a normal subgroup and its full centralizer transfers
normality of its internal closed subgroups to the ambient semisimple group. -/
theorem isNormal_range_comp_of_actual_roots
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G H K : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (a : K ⟶ H) (ha : IsClosedSubgroup a)
    (han : (SubgroupFunctor.range a).IsNormal) :
    (SubgroupFunctor.range (a ≫ h)).IsNormal := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hnc, hnrep⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range (a ≫ h) (ha.comp hh)).1
  have hH : SubgroupFunctor.range h ≤ SubgroupFunctor.range n := by
    intro U x hx
    rw [hnrep.2]
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.normalizer_range_le_comap a h U
    rw [SubgroupFunctor.normalizer_eq_top_of_isNormal han]
    trivial
  have hC : (AutomorphicAction.conjugation h).fixedSubgroup ≤ SubgroupFunctor.range n := by
    intro U x hx
    rw [hnrep.2]
    apply SubgroupFunctor.centralizer_le_normalizer
    intro V b y hy
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    have hc := (mem_conjugation_fixedSubgroup_iff h x).mp hx V b (z ≫ a.hom.hom)
    simpa only [Grp.comp_hom_hom, Category.assoc] using hc.symm
  apply SubgroupFunctor.isNormal_of_normalizer_eq_top
  rw [← hnrep.2]
  exact range_eq_top_of_normal_and_centralizer hRoots hDichotomy hG T t hSplit hMax
    h hh hn n hnc hH hC

/-- An actual closed normal almost-simple subgroup of the ambient group. -/
structure NormalAlmostSimpleFactor (G : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  isAlmostSimple : IsAlmostSimple group
  isClosedSubgroup : IsClosedSubgroup inclusion
  isNormal : (SubgroupFunctor.range inclusion).IsNormal

/-- The explicit centre and root premises produce a normal almost-simple
factor in every nontrivial semisimple group over an algebraically closed field. -/
theorem exists_normalAlmostSimpleFactor_of_actual_roots
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    Nonempty (NormalAlmostSimpleFactor G) := by
  classical
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  obtain ⟨T, t, hMax⟩ := TorusExistence.exists_isMaximalTorus G
  have hSplit : IsSplitSubtorus t :=
    ⟨hMax.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting, hMax.2.1⟩
  let P : ℕ → Prop := fun n =>
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G)
      (hH : IsConnectedReductive H),
      IsClosedSubgroup h ∧ (SubgroupFunctor.range h).IsNormal ∧
      SubgroupFunctor.range h ≠ ⊥ ∧
      @Lie.dimension k _ H hH.isAffineHom = n
  have hExists : ∃ n, P n := by
    refine ⟨Lie.dimension G, G, 𝟙 G, hG.isConnectedReductive, ?_, ?_, hnt, rfl⟩
    · change IsClosedImmersion (𝟙 G.X.left)
      infer_instance
    · intro U x y _ _
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨x * y * x⁻¹, ?_⟩
      change (x * y * x⁻¹) ≫ (𝟙 G.X) = x * y * x⁻¹
      exact Category.comp_id _
  obtain ⟨H, h, hH, hh, hn, hntH, hdim⟩ := Nat.find_spec hExists
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : IsClosedImmersion h.hom.hom.left := hh
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  have hSemi : IsSemisimple H :=
    hG.of_normalSubgroup_of_normalReductiveCenterStatement hCenter h hh hn
  have hntId : SubgroupFunctor.range (𝟙 H) ≠ ⊥ := by
    intro hz
    have hz' := (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) h).2 hz
    exact hntH (by simpa only [Category.id_comp] using hz')
  refine ⟨⟨H, h, ⟨hSemi, hSemi.noncommutative_of_range_ne_bot hntId, ?_⟩, hh, hn⟩⟩
  intro K a ha hKs hKc han
  let : Smooth K.X.hom := hKs
  let : ConnectedSpace K.X.left := hKc
  let : IsClosedImmersion a.hom.hom.left := ha
  let : IsAffineHom K.X.hom := by
    rw [← a.hom.hom.w]
    infer_instance
  by_cases hzero : SubgroupFunctor.range a = ⊥
  · exact Or.inl hzero
  right
  have hKan : (SubgroupFunctor.range (a ≫ h)).IsNormal :=
    isNormal_range_comp_of_actual_roots hRoots hDichotomy hG T t hSplit hMax
      h hh hn a ha han
  have hKnt : SubgroupFunctor.range (a ≫ h) ≠ ⊥ :=
    fun hz => hzero ((SubgroupFunctor.range_comp_eq_bot_iff a h).1 hz)
  have hKred : IsConnectedReductive K :=
    hG.isConnectedReductive.of_normalSubgroup (a ≫ h) (ha.comp hh) hKan
  have hKdim : P (Lie.dimension K) :=
    ⟨K, a ≫ h, hKred, ha.comp hh, hKan, hKnt, rfl⟩
  have hle : Lie.dimension H ≤ Lie.dimension K := by
    rw [hdim]
    exact Nat.find_min' hExists hKdim
  have hiso : IsIso a := by
    by_contra hproper
    exact (Nat.not_lt_of_ge hle) (Lie.dimension_lt_of_proper_closedSubgroup a ha hproper)
  let := hiso
  calc
    SubgroupFunctor.range a = SubgroupFunctor.range ((asIso a).hom ≫ 𝟙 H) := by
      rw [Category.comp_id]
      rfl
    _ = SubgroupFunctor.range (𝟙 H) := SubgroupFunctor.range_iso_comp (asIso a) (𝟙 H)
    _ = ⊤ := SubgroupFunctor.range_id H

/-- Choose the actual normal almost-simple factor constructed by Lie-dimension
minimality under the three explicit structural premises. -/
def normalAlmostSimpleFactorOfActualRoots
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G)
    (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) : NormalAlmostSimpleFactor G :=
  Classical.choice (exists_normalAlmostSimpleFactor_of_actual_roots
    hCenter hRoots hDichotomy hG hnt)

end Langlands.GroupScheme
