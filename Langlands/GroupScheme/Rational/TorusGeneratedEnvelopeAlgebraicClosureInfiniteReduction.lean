import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureStatement
import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # Reduction of the infinite-field envelope compatibility -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace EnvelopeInfiniteReduction

/-! ### Every closed torus lies in a maximal torus -/

section Maximal

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- `n` is the cardinality of the index type of a splitting, over some extension field, of
some closed subgroup of `G` through which `i₀` factors. -/
def IsClosedTorusRankAbove {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i₀ : S.toGrp ⟶ G) (n : ℕ) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsClosedSubgroup i ∧
    (∃ f : S.toGrp ⟶ T.toGrp, f ≫ i = i₀) ∧
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (I : Type u) (_ : Finite I),
      Nonempty ((GroupScheme.baseChange (algebraBaseMap k K)).obj T.toGrp ≅
        splitTorus (Spec (CommRingCat.of K)) I) ∧ Nat.card I = n

/-- Every closed torus of a smooth affine group over a field factors through a maximal
torus. -/
theorem exists_isMaximalTorus_factor [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i₀ : S.toGrp ⟶ G)
    (hS : IsTorus S.toGrp) (hi₀ : IsClosedSubgroup i₀) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (f : S.toGrp ⟶ T.toGrp), IsMaximalTorus i ∧ f ≫ i = i₀ := by
  classical
  let N := Module.finrank k (Additive (lieKernel G k))
  have hbound : ∀ n, IsClosedTorusRankAbove G i₀ n → n ≤ N := by
    rintro n ⟨T, i, hi, -, K, _, _, I, _, ⟨e⟩, rfl⟩
    exact TorusExistence.card_le_finrank G i hi K I e
  obtain ⟨K₀, _, _, I₀, _, ⟨e₀⟩⟩ := hS
  have h0 : IsClosedTorusRankAbove G i₀ (Nat.card I₀) :=
    ⟨S, i₀, hi₀, ⟨𝟙 _, Category.id_comp _⟩, K₀, inferInstance, inferInstance, I₀,
      inferInstance, ⟨e₀⟩, rfl⟩
  obtain ⟨T, i, hi, ⟨g, hg⟩, K, _, _, I, _, ⟨e⟩, hI⟩ :=
    Nat.findGreatest_spec (P := IsClosedTorusRankAbove G i₀) (hbound _ h0) h0
  refine ⟨T, i, g, ⟨⟨K, inferInstance, inferInstance, I, inferInstance, ⟨e⟩⟩, hi, ?_⟩, hg⟩
  intro T' i' f hT' hi' hf
  obtain ⟨K', _, _, I', _, ⟨e'⟩⟩ := hT'
  have hrank' : IsClosedTorusRankAbove G i₀ (Nat.card I') :=
    ⟨T', i', hi', ⟨g ≫ f, by rw [Category.assoc, hf, hg]⟩, K', inferInstance, inferInstance,
      I', inferInstance, ⟨e'⟩, rfl⟩
  have hI' : Nat.card I' ≤ Nat.card I :=
    hI ▸ Nat.le_findGreatest (hbound _ hrank') hrank'
  let E := TorusBaseChange.commonExtension k K K'
  let : Field E.carrier := E.field
  let : Algebra k E.carrier := (E.leftHom.comp (algebraMap k K)).toAlgebra
  obtain ⟨eE⟩ := TorusExistence.nonempty_splitIso_extension E.leftHom rfl T.toGrp I e
  obtain ⟨eE'⟩ :=
    TorusExistence.nonempty_splitIso_extension E.rightHom E.compatible.symm T'.toGrp I' e'
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono f.hom.hom := by
    have hc : f.hom.hom ≫ i'.hom.hom = i.hom.hom := congrArg (fun g => g.hom.hom) hf
    exact mono_of_mono_fac hc
  have hmono : Mono ((GroupScheme.baseChange (algebraBaseMap k E.carrier)).map f).hom.hom := by
    change Mono ((Over.pullback _).map f.hom.hom)
    infer_instance
  have := splitTorus.isIso_of_mono_of_iso eE eE' _ hmono hI'
  exact TorusExistence.isIso_of_isIso_baseChange E.carrier f

end Maximal

/-! ### Points landing in a closed subgroup -/

section Points

variable {K : Type u} [Field K] {H G : GroupScheme (Spec (CommRingCat.of K))}

/-- A base point whose image lies in the image of a closed subgroup factors through it. -/
theorem mem_range_of_range_subset {inc : H ⟶ G} (hinc : IsClosedSubgroup inc)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (hx : Set.range x.left ⊆ Set.range inc.hom.hom.left) :
    x ∈ (SubgroupFunctor.range inc).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
  let f := x.left
  let g := inc.hom.hom.left
  have : IsClosedImmersion g := hinc
  let p := pullback.fst f g
  have : Surjective p := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun y => hx ⟨y, rfl⟩
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
    (inferInstance : IsReduced (Spec (CommRingCat.of K)))
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  have hw : g ≫ G.X.hom = H.X.hom := Over.w inc.hom.hom
  have hfg : (inv p ≫ pullback.snd f g) ≫ g = f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  refine ⟨Over.homMk (inv p ≫ pullback.snd f g) ?_, ?_⟩
  · change (inv p ≫ pullback.snd f g) ≫ H.X.hom = 𝟙 _
    rw [← hw, ← Category.assoc, hfg]
    exact Over.w x
  · apply Over.OverMorphism.ext
    exact hfg

end Points

/-! ### Conjugating a fixed point -/

section Conjugation

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Conjugation of a fixed base point `s` by the universal point: `g ↦ g s g⁻¹`. -/
def conjByPoint (s : Over.mk (𝟙 S) ⟶ G.X) : G.X ⟶ G.X :=
  𝟙 G.X * G.constantPoint s G.X * (𝟙 G.X)⁻¹

/-- On a point `g`, the conjugation morphism takes the value `g s g⁻¹`. -/
theorem comp_conjByPoint (s : Over.mk (𝟙 S) ⟶ G.X) {T : Over S} (g : T ⟶ G.X) :
    g ≫ conjByPoint G s = g * G.constantPoint s T * g⁻¹ := by
  unfold conjByPoint
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
    G.constantPoint_naturality]

/-- At base points, conjugating `s` by `g` is the inner automorphism of `g` applied to `s`. -/
theorem comp_conjByPoint_base (s g : Over.mk (𝟙 S) ⟶ G.X) :
    g ≫ conjByPoint G s = s ≫ (G.innerIso g).hom.hom.hom := by
  rw [comp_conjByPoint, comp_innerIso_hom, constantPoint_self, constantPoint_self]

end Conjugation

end EnvelopeInfiniteReduction

open EnvelopeInfiniteReduction

/-- Grothendieck's theorem on maximal tori under field extension, conjugacy of maximal tori
over an algebraically closed field, and density of conjugators onto ground-field maximal tori
together give the infinite-field compatibility of the closed torus envelope with algebraic
closure. -/
theorem torusGeneratedEnvelopeAlgebraicClosureInfinite_of
    (hbc : MaximalTorusBaseChangeStatement.{u})
    (hconj : MaximalTorusConjugacyStatement.{u})
    (hdense : RationalMaximalTorusConjugateDensityStatement.{u}) :
    TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement.{u} := by
  intro k _ _ G _ _ _
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let GK := F.obj G
  rw [closedTorusEnvelope_baseChange_eq_iff_containsTori K G]
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom GK.X.hom := TorusExistence.isAffineHom_baseChange K G
  have : ConnectedSpace GK.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  let D := smoothTorusGeneratedEnvelope G
  let inc := F.map D.inclusion
  have hinc : IsClosedSubgroup inc := D.closed.baseChange b
  have hE : (closedTorusEnvelope G).baseChange b = SubgroupFunctor.range inc := by
    rw [SubgroupFunctor.range_baseChangeHom, D.represents.2]
  rw [hE]
  -- Base changes of closed `k`-tori lie in `D_K`.
  have hkt : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsTorus T.toGrp → IsClosedSubgroup j →
        SubgroupFunctor.range (F.map j) ≤ SubgroupFunctor.range inc := by
    intro T j hT hj
    have hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range D.inclusion := by
      rw [D.represents.2]
      exact closedTorusEnvelope_containsTori G T j hT hj
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    exact fun U _ hx => hle _ hx
  -- A maximal `k`-torus and its extension.
  obtain ⟨T₀, j₀, hj₀⟩ := TorusExistence.exists_isMaximalTorus G
  have hj₀K : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T₀) (F.map j₀) :=
    (hbc k K G T₀ j₀ hj₀.1 hj₀.2.1).1 hj₀
  -- Every `K`-conjugate of `(T₀)_K` lies in `D_K`.
  have hconjle : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ GK.X,
      SubgroupFunctor.range (F.map j₀ ≫ (GK.innerIso g).hom) ≤ SubgroupFunctor.range inc := by
    intro g
    have hTK : IsTorus (F.obj T₀.toGrp) := hj₀.1.baseChange
    have : Smooth (F.obj T₀.toGrp).X.hom := hTK.smooth
    have : IsReduced (F.obj T₀.toGrp).X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        K _ (F.obj T₀.toGrp).X.hom
    apply SubgroupFunctor.range_le_of_algClosed_points hinc
    rintro _ ⟨t, rfl⟩
    let s := t ≫ (F.map j₀).hom.hom
    have hpt : ∀ g' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ GK.X,
        t ≫ (F.map j₀ ≫ (GK.innerIso g').hom).hom.hom = g' ≫ conjByPoint GK s := by
      intro g'
      rw [comp_conjByPoint_base, Grp.comp_hom_hom, Category.assoc]
    change t ≫ (F.map j₀ ≫ (GK.innerIso g).hom).hom.hom ∈ _
    rw [hpt g]
    apply mem_range_of_range_subset hinc
    let c := (conjByPoint GK s).left
    let Z := c ⁻¹' Set.range inc.hom.hom.left
    have : IsClosedImmersion inc.hom.hom.left := hinc
    have hZclosed : IsClosed Z :=
      inc.hom.hom.left.isClosedEmbedding.isClosed_range.preimage c.continuous
    have hsub : (⋃ (g' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ GK.X)
        (_ : ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsTorus T.toGrp ∧ IsClosedSubgroup j ∧
            SubgroupFunctor.range (F.map j₀ ≫ (GK.innerIso g').hom) =
              SubgroupFunctor.range (F.map j)),
        Set.range g'.left) ⊆ Z := by
      simp only [Set.iUnion_subset_iff]
      rintro g' ⟨T, j, hT, hj, hrange⟩ _ ⟨y, rfl⟩
      have hmem : g' ≫ conjByPoint GK s ∈
          (SubgroupFunctor.range inc).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
        apply hkt T j hT hj
        rw [← hrange, ← hpt g']
        exact ⟨t, rfl⟩
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a.left y, ?_⟩
      have hl := congrArg (fun q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ GK.X => q.left y) ha
      change (a ≫ inc.hom.hom).left y = (g' ≫ conjByPoint GK s).left y at hl
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using hl
    have hZ : Z = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (hdense k G T₀ j₀ hj₀).closure_eq]
      exact closure_minimal hsub hZclosed
    rintro _ ⟨y, rfl⟩
    have hy : g.left y ∈ Z := hZ ▸ Set.mem_univ _
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hy
  -- Every closed `K`-torus lies in a maximal one, which is a conjugate of `(T₀)_K`.
  intro S i hS hi
  obtain ⟨S', i', f, hi', hf⟩ := exists_isMaximalTorus_factor GK i hS hi
  obtain ⟨g, φ, hg⟩ := hconj K GK ((CommGroupScheme.baseChange b).obj T₀) S' (F.map j₀) i' hj₀K hi'
  have hi'eq : i' = CommGroupScheme.groupHom φ.inv ≫ (CommGroupScheme.groupHom φ.hom ≫ i') := by
    rw [← Category.assoc]
    change i' = CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ i'
    rw [φ.inv_hom_id]
    exact (Category.id_comp i').symm
  calc SubgroupFunctor.range i = SubgroupFunctor.range (f ≫ i') := by rw [hf]
    _ ≤ SubgroupFunctor.range i' := SubgroupFunctor.range_comp_le f i'
    _ ≤ SubgroupFunctor.range (CommGroupScheme.groupHom φ.hom ≫ i') := by
      conv_lhs => rw [hi'eq]
      exact SubgroupFunctor.range_comp_le _ _
    _ = SubgroupFunctor.range (F.map j₀ ≫ (GK.innerIso g).hom) := by rw [hg]
    _ ≤ SubgroupFunctor.range inc := hconjle g

end Langlands.GroupScheme
