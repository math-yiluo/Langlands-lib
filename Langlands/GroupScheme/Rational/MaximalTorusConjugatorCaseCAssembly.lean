import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseC
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Cartan.LieInduction
import Langlands.GroupScheme.Rational.SubgroupProductGeometry
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.HomogeneousQuotientFiber

/-! # Case C data from a conjugator into a Lie-element centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance caseCAssemblyIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A point `c` of `G_K` over an algebraically closed field `Ω` over `K` whose image in `G` is
dense and which conjugates the base change of the torus `j₀` into the all-test centralizer of
the `K`-rational Lie element `Y` of `G_K`, over every test scheme over `Ω`. -/
def HasCentralizerConjugator (j₀ : T₀.toGrp ⟶ G) (Y : lieKernel G_K K) : Prop :=
  ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra K Ω) (_ : IsAlgClosed Ω)
    (c : Over.mk (algebraBaseMap K Ω) ⟶ (G_K).X),
    DenseRange (baseChangePointsEquiv (algebraBaseMap k K) G
      (Over.mk (algebraBaseMap K Ω)) c).left ∧
    ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
      (t : V ⟶ (G_K).X),
      t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V →
        (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (Lie.elementCentralizer G_K Y).carrier V

variable {G}

/-- If `c` conjugates the base change of a torus `j₀` into the centralizer `C` of `Y`, it
conjugates it into the identity component of `C`: the conjugated torus is connected and
contains the identity. -/
theorem conj_mem_range_identityComponent_of_mem_elementCentralizer
    {j₀ : T₀.toGrp ⟶ G} (hj₀ : IsMaximalTorus j₀)
    [LocallyOfFiniteType (G_K).X.hom] {Y : lieKernel G_K K}
    [Smooth (Lie.elementCentralizerGroup G_K Y).X.hom]
    {Ω : Type u} [Field Ω] [Algebra K Ω] (c : Over.mk (algebraBaseMap K Ω) ⟶ (G_K).X)
    (hc : ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
      (t : V ⟶ (G_K).X),
      t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V →
        (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (Lie.elementCentralizer G_K Y).carrier V)
    (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
    (t : V ⟶ (G_K).X)
    (ht : t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V) :
    (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (SubgroupFunctor.range
      (identityComponentι (Lie.elementCentralizerGroup G_K Y) ≫
        Lie.elementCentralizerGroupι G_K Y)).carrier V := by
  let b := algebraBaseMap k K
  let β := algebraBaseMap K Ω
  let C := Lie.elementCentralizerGroup G_K Y
  let ιC := Lie.elementCentralizerGroupι G_K Y
  have hrep := Lie.elementCentralizerGroup_isRepresentedBy G_K Y
  have : Mono ιC.hom.hom := hrep.1
  let T₀K := (CommGroupScheme.baseChange b).obj T₀
  let j₀K : T₀K.toGrp ⟶ G_K := (GroupScheme.baseChange b).map j₀
  have hrange₀ : (SubgroupFunctor.range j₀).baseChange b = SubgroupFunctor.range j₀K :=
    (SubgroupFunctor.range_baseChangeHom b j₀).symm
  have : Smooth T₀.toGrp.X.hom := hj₀.1.smooth
  have : IsAffineHom T₀.toGrp.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G T₀.toGrp j₀ hj₀.2.1
  have : ConnectedSpace T₀.toGrp.X.left := hj₀.1.connectedSpace
  have : Smooth T₀K.toGrp.X.hom := by
    change Smooth (pullback.snd T₀.toGrp.X.hom b)
    infer_instance
  have : IsAffineHom T₀K.toGrp.X.hom := by
    change IsAffineHom (pullback.snd T₀.toGrp.X.hom b)
    infer_instance
  have : ConnectedSpace T₀K.toGrp.X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine T₀.toGrp b
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd T₀K.toGrp.X.hom β ≫ β)
  have hP : ConnectedSpace P.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine T₀K.toGrp β
  let pr₁ : P ⟶ T₀K.toGrp.X := Over.homMk (pullback.fst _ _) pullback.condition
  let pr₂ : P ⟶ Over.mk β := Over.homMk (pullback.snd _ _) rfl
  let f : P ⟶ (G_K).X := (pr₂ ≫ c) * (pr₁ ≫ j₀K.hom.hom) * (pr₂ ≫ c)⁻¹
  have hf : f ∈ (Lie.elementCentralizer G_K Y).carrier P :=
    hc P pr₂ _ (by rw [hrange₀]; exact ⟨pr₁, rfl⟩)
  rw [← hrep.2] at hf
  obtain ⟨f', hf'⟩ := SubgroupFunctor.mem_range.1 hf
  let u := CartesianMonoidalCategory.toUnit (Over.mk β)
  let a : Over.mk β ⟶ P := Over.homMk
    (pullback.lift (u ≫ η[T₀K.toGrp.X]).left (𝟙 _) (by
      rw [Category.id_comp, Over.w]
      rfl)) (by
      simp only [P, Over.mk_hom]
      rw [pullback.lift_snd_assoc, Category.id_comp])
  have ha₁ : a ≫ pr₁ = u ≫ η[T₀K.toGrp.X] := by
    ext
    exact pullback.lift_fst _ _ _
  have ha₂ : a ≫ pr₂ = 𝟙 _ := by
    ext
    exact pullback.lift_snd _ _ _
  have ha : a ≫ f = u ≫ η[(G_K).X] := by
    simp only [f, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ha₁, ha₂,
      Category.id_comp]
    rw [Category.assoc, IsMonHom.one_hom]
    show c * 1 * c⁻¹ = 1
    simp
  have ha' : a ≫ f' = u ≫ η[C.X] := by
    apply (cancel_mono ιC.hom.hom).1
    rw [Category.assoc, hf', ha, Category.assoc, IsMonHom.one_hom]
  have hsub : Set.range f'.left ⊆ Set.range (identityComponentι C).hom.hom.left := by
    rw [IdentityComponent.range_identityComponentι]
    refine (isConnected_range f'.left.continuous).isPreconnected.subset_connectedComponent ?_
    obtain ⟨ω⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    refine ⟨a.left ω, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ha', Over.comp_left, Scheme.Hom.comp_apply,
      IdentityComponent.unit_left_apply]
  let f'' := FiniteEtaleImage.liftOver (identityComponentι C).hom.hom f' hsub
  rw [hrange₀] at ht
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.1 ht
  let l : V ⟶ P := Over.homMk (pullback.lift s.left y.left (by
    rw [Over.w s]
    exact (Over.w y).symm)) (by
      simp only [P, Over.mk_hom]
      rw [pullback.lift_snd_assoc]
      exact Over.w y)
  have hl₁ : l ≫ pr₁ = s := by
    ext
    exact pullback.lift_fst _ _ _
  have hl₂ : l ≫ pr₂ = y := by
    ext
    exact pullback.lift_snd _ _ _
  refine SubgroupFunctor.mem_range.2 ⟨l ≫ f'', ?_⟩
  rw [Grp.comp_hom_hom, Category.assoc, FiniteEtaleImage.liftOver_fac_assoc, hf']
  simp only [f, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hl₁, hl₂]

section Data

variable [Smooth G.X.hom]

local instance caseCAssemblySmooth : Smooth (G_K).X.hom := by
  change Smooth (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A centralizer conjugator for a `K`-rational Lie element of `G_K` with smooth centralizer
and proper tangent centralizer gives the conjugation data of Case C: the subgroup is the
identity component of the centralizer. -/
theorem conjugationData_of_hasCentralizerConjugator [ConnectedSpace G.X.left]
    {j₀ : T₀.toGrp ⟶ G} (hj₀ : IsMaximalTorus j₀) {Y : lieKernel G_K K}
    [Smooth (Lie.elementCentralizerGroup G_K Y).X.hom]
    (hY : Lie.elementCentralizerLie G_K Y ≠ ⊤) (hc : HasCentralizerConjugator G j₀ Y) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of K))) (_ : Smooth H.X.hom)
      (_ : IsAffineHom H.X.hom) (_ : ConnectedSpace H.X.left) (i : H ⟶ G_K),
      IsClosedSubgroup i ∧ Lie.dimension H < Lie.dimension G ∧
      ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra K Ω) (_ : IsAlgClosed Ω)
        (c : Over.mk (algebraBaseMap K Ω) ⟶ (G_K).X),
        DenseRange (baseChangePointsEquiv (algebraBaseMap k K) G
          (Over.mk (algebraBaseMap K Ω)) c).left ∧
        ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
          (t : V ⟶ (G_K).X),
          t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V →
            (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (SubgroupFunctor.range i).carrier V := by
  obtain ⟨Ω, _, _, _, c, hcd, hc⟩ := hc
  let C := Lie.elementCentralizerGroup G_K Y
  have hrep := Lie.elementCentralizerGroup_isRepresentedBy G_K Y
  have hcl := Lie.isClosedSubgroup_elementCentralizerGroupι G_K Y
  have : ConnectedSpace (G_K).X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine G (algebraBaseMap k K)
  refine ⟨identityComponent C, inferInstance, inferInstance, inferInstance,
    identityComponentι C ≫ Lie.elementCentralizerGroupι G_K Y,
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hcl, ?_, Ω, inferInstance,
    inferInstance, inferInstance, c, hcd,
    fun V y t ht => conj_mem_range_identityComponent_of_mem_elementCentralizer hj₀ c hc V y t ht⟩
  rw [← SubgroupProductOrbit.lie_dimension_baseChange G (algebraBaseMap k K)]
  exact Lie.dimension_identityComponent_lt_of_lie_ne_top hrep hcl hY

end Data

end Langlands.GroupScheme
