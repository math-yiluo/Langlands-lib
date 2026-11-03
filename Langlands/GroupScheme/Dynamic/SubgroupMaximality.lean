import Langlands.GroupScheme.Dynamic.SubgroupLimit
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof

/-! # Fixed centralizer intersections and dynamic maximality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H Z : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : H ⟶ G) (z : Z ⟶ G)

/-- Pulling back a subgroup along `j` detects its range on all tests. -/
theorem mem_range_intersectionFst_iff {T : Over S} (x : T ⟶ H.X) :
    x ∈ (SubgroupFunctor.range (subgroupIntersectionFst j z)).carrier T ↔
      x ≫ j.hom.hom ∈ (SubgroupFunctor.range z).carrier T := by
  let hpb := subgroupIntersection_isPullback j z
  change (∃ y : T ⟶ (subgroupIntersection j z).X,
    y ≫ (subgroupIntersectionFst j z).hom.hom = x) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    refine SubgroupFunctor.mem_range.mpr
      ⟨y ≫ (subgroupIntersectionSnd j z).hom.hom, ?_⟩
    simp only [Category.assoc, hpb.w]
  · rintro ⟨y, hy⟩
    exact SubgroupFunctor.mem_range.mpr
      ⟨hpb.lift x y hy.symm, hpb.lift_fst x y hy.symm⟩

/-- The first projection of a closed intersection is closed. -/
theorem isClosedSubgroup_intersectionFst (hzc : IsClosedSubgroup z) :
    IsClosedSubgroup (subgroupIntersectionFst j z) := by
  change IsClosedImmersion (subgroupIntersectionFst j z).hom.hom.left
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme j z).flip hzc

/-- Fixedness for the induced conjugation action is ambient centralization. -/
theorem normalizedConjugation_fixed_iff [Mono j.hom.hom]
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    {T : Over S} (x : T ⟶ H.X) :
    (AutomorphicAction.ofNormalizedConjugation j χ hn).IsFixed x ↔
      x ≫ j.hom.hom ∈ (centralizer χ).carrier T := by
  rw [AutomorphicAction.isFixed_iff_universal, mem_centralizer]
  change (lift (snd T (Gm S).X) (fst T (Gm S).X ≫ x) ≫
      SubgroupFunctor.normalizedConjugation j χ hn = fst T (Gm S).X ≫ x) ↔ _
  rw [← cancel_mono j.hom.hom,
    SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  simp only [orbit, Category.assoc]

/-- The first intersection projection represents the fixed subgroup of
the actual normalized conjugation action on `H`. -/
theorem isRepresentedBy_intersectionFst_fixed [Mono j.hom.hom]
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ)) :
    (AutomorphicAction.ofNormalizedConjugation j χ hn).fixedSubgroup.IsRepresentedBy
      (subgroupIntersectionFst j z) := by
  have : IsClosedImmersion (subgroupIntersectionFst j z).hom.hom.left :=
    isClosedSubgroup_intersectionFst j z hzc
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_intersectionFst_iff, hz.2, AutomorphicAction.mem_fixedSubgroup,
    normalizedConjugation_fixed_iff]

/-- An actual closed fixed-subgroup model, obtained by intersecting `H`
with a representative of the ambient dynamic centralizer. -/
def subgroupCentralizerFixedModel [Mono j.hom.hom]
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ)) :
    Σ C : GroupScheme S, {f : C ⟶ H //
      (AutomorphicAction.ofNormalizedConjugation j χ hn).fixedSubgroup.IsRepresentedBy f ∧
        IsClosedSubgroup f} :=
  ⟨subgroupIntersection j z, subgroupIntersectionFst j z,
    isRepresentedBy_intersectionFst_fixed χ j z hz hzc hn,
    isClosedSubgroup_intersectionFst j z hzc⟩

/-- Normalization of `H` by `Z` makes the intersection normal in `Z`. -/
theorem range_intersectionSnd_isNormal
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range z)) :
    (SubgroupFunctor.range (subgroupIntersectionSnd j z)).IsNormal := by
  intro T g x _ hx
  let hpb := subgroupIntersection_isPullback j z
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : (y ≫ (subgroupIntersectionSnd j z).hom.hom) ≫ z.hom.hom ∈
      (SubgroupFunctor.range j).carrier T := by
    refine SubgroupFunctor.mem_range.mpr
      ⟨y ≫ (subgroupIntersectionFst j z).hom.hom, ?_⟩
    simp only [Category.assoc, hpb.w]
  have hc := hn T (g ≫ z.hom.hom) _ (SubgroupFunctor.mem_range.mpr ⟨g, rfl⟩) hy
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hc
  have he : w ≫ j.hom.hom =
      (g * (y ≫ (subgroupIntersectionSnd j z).hom.hom) * g⁻¹) ≫ z.hom.hom := by
    simpa only [MonObj.mul_comp, GrpObj.inv_comp] using hw
  exact SubgroupFunctor.mem_range.mpr
    ⟨hpb.lift w _ he, hpb.lift_snd w _ he⟩

/-- A normal subgroup of a represented group stays normalized by its ambient image. -/
theorem range_comp_isNormalizedBy_of_isNormal {P : GroupScheme S}
    (v : H ⟶ P) (p : P ⟶ G) (hn : (SubgroupFunctor.range v).IsNormal) :
    (SubgroupFunctor.range (v ≫ p)).IsNormalizedBy (SubgroupFunctor.range p) := by
  intro T g x hg hx
  obtain ⟨g', rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨x', rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    (hn T g' (x' ≫ v.hom.hom) (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.mpr ⟨x', rfl⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
  simpa only [Grp.comp_hom_hom, ← Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] using
    congrArg (fun f => f ≫ p.hom.hom) hy

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G H Z : GroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : H ⟶ G) (z : Z ⟶ G)

/-- A smooth affine normalized subgroup has smooth centralizer intersection. -/
theorem subgroupIntersection_smooth [Mono j.hom.hom]
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hH : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom) :
    Smooth (subgroupIntersection j z).X.hom := by
  let e : (Gm (Spec (CommRingCat.of k))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of k)
        (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  exact Diagonalizable.fixedSubgroup_smooth_of_actingIso
    Diagonalizable.FixedSmooth.fixedSubgroupSmooth
    (AutomorphicAction.ofNormalizedConjugation j χ hn) e hH hAff
    (subgroupIntersectionFst j z)
    (isRepresentedBy_intersectionFst_fixed χ j z hz hzc hn)
    (isClosedSubgroup_intersectionFst j z hzc)

/-- A smooth connected unipotent normalized subgroup of `P(χ)` has trivial
centralizer intersection if the latter centralizer has trivial unipotent radical. -/
theorem range_intersectionSnd_eq_bot_of_trivialRadical [IsSeparated G.X.hom]
    (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hnZ : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range z))
    (hp : SubgroupFunctor.range j ≤ parabolic χ)
    (hH : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom)
    (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H)
    (hZ : HasTrivialUnipotentRadical Z) :
    SubgroupFunctor.range (subgroupIntersectionSnd j z) = ⊥ := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have := hc
  exact hZ (subgroupIntersection j z) (subgroupIntersectionSnd j z)
    (isClosedSubgroup_intersectionSnd j z hj)
    (subgroupIntersection_smooth χ j z hz hzc hn hH hAff)
    (subgroupIntersection_connectedSpace χ j z hj hz hzc hn hp)
    (subgroupIntersection_isUnipotent χ j z hj hz hzc hn hp hu)
    (range_intersectionSnd_isNormal j z hnZ)

/-- Every point of such a subgroup contracts to the identity on its original test. -/
theorem range_le_unipotent_of_trivialCentralizerRadical [IsSeparated G.X.hom]
    (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hnZ : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range z))
    (hp : SubgroupFunctor.range j ≤ parabolic χ)
    (hH : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom)
    (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H)
    (hZ : HasTrivialUnipotentRadical Z) :
    SubgroupFunctor.range j ≤ unipotent χ := by
  have hb := range_intersectionSnd_eq_bot_of_trivialRadical χ j z
    hj hz hzc hn hnZ hp hH hAff hc hu hZ
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  let q := subgroupCentralizerLimit χ j z hj hz hzc hn hp
  have hq : (y ≫ q.hom.hom) ≫ (subgroupIntersectionSnd j z).hom.hom = 1 := by
    have hmem := (SubgroupFunctor.mem_range
      (f := subgroupIntersectionSnd j z)).mpr ⟨y ≫ q.hom.hom, rfl⟩
    rwa [hb, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
  apply (limit_eq_one_iff χ ⟨y ≫ j.hom.hom, hp T ⟨y, rfl⟩⟩).mp
  rw [← subgroupCentralizerLimit_comp χ j z hj hz hzc hn hp y]
  change (y ≫ q.hom.hom) ≫
    ((subgroupIntersectionFst j z).hom.hom ≫ j.hom.hom) = 1
  rw [(subgroupIntersection_isPullback j z).w, ← Category.assoc, hq,
    MonObj.one_comp]

/-- The normal-subgroup form of maximality, for an arbitrary actual
representative of the dynamic parabolic in an affine group. -/
theorem normal_subgroup_range_comp_le_unipotent [IsAffineHom G.X.hom]
    {P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
    (hP : (parabolic χ).IsRepresentedBy p) (hpc : IsClosedSubgroup p)
    (v : H ⟶ P) (hvc : IsClosedSubgroup v)
    (hn : (SubgroupFunctor.range v).IsNormal)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hH : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H)
    (hZ : HasTrivialUnipotentRadical Z) :
    SubgroupFunctor.range (v ≫ p) ≤ unipotent χ := by
  have : IsClosedImmersion p.hom.hom.left := hpc
  have : IsClosedImmersion v.hom.hom.left := hvc
  have hj : IsClosedSubgroup (v ≫ p) := by
    change IsClosedImmersion (v.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have hAff : IsAffineHom H.X.hom := by
    have h : IsAffineHom ((v.hom.hom.left ≫ p.hom.hom.left) ≫ G.X.hom) := inferInstance
    simpa only [Category.assoc, Over.w] using h
  have hnP := range_comp_isNormalizedBy_of_isNormal v p hn
  have hχP : SubgroupFunctor.range χ ≤ SubgroupFunctor.range p := by
    rw [hP.2]
    exact (range_le_centralizer χ).trans (centralizer_le_parabolic χ)
  have hzP : SubgroupFunctor.range z ≤ SubgroupFunctor.range p := by
    rw [hz.2, hP.2]
    exact centralizer_le_parabolic χ
  have hp : SubgroupFunctor.range (v ≫ p) ≤ parabolic χ := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ v.hom.hom, Category.assoc _ _ _⟩
  exact range_le_unipotent_of_trivialCentralizerRadical χ (v ≫ p) z
    hj hz hzc (fun T g x hg hx => hnP T g x (hχP T hg) hx)
    (fun T g x hg hx => hnP T g x (hzP T hg) hx)
    hp hH hAff hc hu hZ

end Langlands.GroupScheme.Dynamic
