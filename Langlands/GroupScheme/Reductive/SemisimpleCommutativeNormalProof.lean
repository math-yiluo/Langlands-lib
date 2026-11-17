import Langlands.GroupScheme.Reductive.SemisimpleCommutativeNormalStatement
import Langlands.GroupScheme.Rational.NormalSolvableCentrality
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalExistsProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Adjoint.CenterQuotientCore
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Semisimple groups and commutative normal subgroups: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SemisimpleCommutativeNormal

variable {k : Type u} [Field k]

/-- A smooth connected group scheme over a field whose structure morphism is finite is
trivial: its identity morphism is the unit morphism. -/
theorem id_eq_one_of_isFinite (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsFinite H.X.hom] :
    (𝟙 H.X : H.X ⟶ H.X) = 1 := by
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let s : Spec (CommRingCat.of k) ⟶ H.X.left := η[H.X].left
  have hs : s ≫ H.X.hom = 𝟙 _ := η[H.X].w
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id H.X.hom s hs
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  have hdisc : DiscreteTopology H.X.left := by
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of k)))
    have h := H.X.hom.isDiscrete_preimage_singleton y
    have hpre : H.X.hom ⁻¹' {y} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [hpre] at h
    exact isDiscrete_univ_iff.mp h
  have hsub : Subsingleton H.X.left :=
    Set.subsingleton_univ_iff.mp (isPreconnected_univ.subsingleton)
  have : Surjective s := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  have : IsIso H.X.hom := by
    have hp : H.X.hom = inv s := by
      rw [← Category.id_comp H.X.hom, ← IsIso.inv_hom_id s, Category.assoc, hs,
        Category.comp_id]
    rw [hp]
    infer_instance
  apply Over.OverMorphism.ext
  apply (cancel_mono H.X.hom).mp
  exact (Over.w (𝟙 H.X)).trans (Over.w (1 : H.X ⟶ H.X)).symm

/-- **First direction.** In a semisimple group every smooth connected commutative normal
closed subgroup is trivial. -/
theorem range_eq_bot_of_isSemisimple {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G) (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
    (hj : IsClosedSubgroup j) (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (hcomm : IsCommMonObj H.X) (hn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range j = ⊥ := by
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  have hcent : IsCentral j :=
    (isSolvableGroupScheme_of_isCommMonObj H).isCentral_of_normal_of_isConnectedReductive_field
      hG.isConnectedReductive j hj hn
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsFinite Z.X.hom := hfin
  have hmem : 𝟙 H.X ≫ j.hom.hom ∈ (SubgroupFunctor.range z).carrier H.X := by
    rw [hz.2]
    exact hcent H.X (𝟙 H.X)
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hmem
  have hyl : y.left ≫ z.hom.hom.left = j.hom.hom.left := by
    have h := congrArg (fun r => r.left) hy
    simpa only [Over.comp_left, Over.id_left, Category.id_comp] using h
  have : IsFinite (y.left ≫ z.hom.hom.left) := by
    rw [hyl]
    infer_instance
  have : IsFinite y.left := IsFinite.of_comp y.left z.hom.hom.left
  have : IsFinite H.X.hom := by
    rw [← Over.w y]
    infer_instance
  exact CenterQuotient.range_eq_bot_of_id_eq_one j (id_eq_one_of_isFinite H)

/-- Without commutative normal subgroup varieties, the ground-field unipotent radical
is trivial: the last nontrivial universal commutator of a unipotent normal subgroup
generates a commutative normal subgroup variety. -/
theorem hasTrivialUnipotentRadical_of_noCommutativeNormal
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hNo : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
        IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
          SubgroupFunctor.range j = ⊥) :
    HasTrivialUnipotentRadical G := by
  intro U u hu hs hc hU hn
  have : IsClosedImmersion u.hom.hom.left := hu
  have : IsAffineHom U.X.hom := by
    rw [← Over.w u.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  have huRep : (SubgroupFunctor.range u).IsRepresentedBy u :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let a := AutomorphicAction.conjugation (𝟙 G)
  have hst : a.IsStable (SubgroupFunctor.range u) := by
    intro T g x hx
    simpa only [a, AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] using hn T g x (Subgroup.mem_top _) hx
  let aU := a.onRepresentedSubgroup u huRep hst
  by_contra hne
  have hU1 : SubgroupFunctor.range (𝟙 U) ≠ ⊥ := fun h1 =>
    hne (CenterQuotient.range_eq_bot_of_id_eq_one u
      (CenterQuotient.id_eq_one_of_range_id_eq_bot h1))
  obtain ⟨W, w, -, hw, hWs, -, -, hWc, hWcent, hWst, hWne, -⟩ :=
    hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent aU inferInstance hU1 hU
  have : IsClosedImmersion w.hom.hom.left := hw
  have : Mono w.hom.hom := Over.mono_of_mono_left _
  have hWcomm : IsCommMonObj W.X := hWcent.isCommMonObj
  have hnorm : (SubgroupFunctor.range (w ≫ u)).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy := hWst T g (y ≫ w.hom.hom) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hy
    refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hv]
    change aU.act g (y ≫ w.hom.hom) ≫ u.hom.hom = _
    rw [AutomorphicAction.onRepresentedSubgroup_act_comp]
    simp only [a, AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id, Category.assoc]
  have hwu : IsClosedSubgroup (w ≫ u) := hw.comp hu
  have hbot := hNo W (w ≫ u) hwu hWs hWc hWcomm hnorm
  have : IsClosedImmersion (w ≫ u).hom.hom.left := hwu
  have : Mono (w ≫ u).hom.hom := Over.mono_of_mono_left _
  have hone : (𝟙 W.X : W.X ⟶ W.X) = 1 := by
    apply (cancel_mono (w ≫ u).hom.hom).mp
    have h1 : 𝟙 W.X ≫ (w ≫ u).hom.hom ∈
        (SubgroupFunctor.range (w ≫ u)).carrier W.X :=
      SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    rw [h1, MonObj.one_comp]
  exact hWne (CenterQuotient.range_eq_bot_of_id_eq_one w hone)

/-- Without commutative normal subgroup varieties, a connected reductive group over any
field is semisimple: its geometric solvable radical is a central torus, hence trivial. -/
theorem isSemisimple_of_noCommutativeNormal
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (hNo : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
        IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
          SubgroupFunctor.range j = ⊥) :
    IsSemisimple G := by
  obtain ⟨R, r, hr⟩ := reductiveGeometricSolvableRadicalExists k G hG
  obtain ⟨hRT, hRC⟩ :=
    hr.isTorus_and_isCentral_of_structural algClosedReductiveNormalSolvableTorus hG
  have hRcomm : IsCommMonObj R.X := hRT.isCommMonObj
  have hbot : SubgroupFunctor.range r = ⊥ :=
    hNo R r hr.1.isClosedSubgroup hr.1.smooth hr.1.connectedSpace hRcomm hRC.range_isNormal
  have hGbar := hG.baseChange_toAlgebraicClosure
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
    hGbar.isAffineHom
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
    hGbar.smooth
  have htriv : HasTrivialSolvableRadical
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) := by
    intro H j hj hs hc hsol hn
    have hle := hr.2.greatest H j hj hs hc hsol hn
    rw [SubgroupFunctor.range_baseChangeHom, hbot, SubgroupFunctor.bot_baseChange] at hle
    apply SubgroupFunctor.ext
    intro T
    rw [SubgroupFunctor.bot_carrier]
    apply le_antisymm _ bot_le
    intro x hx
    have h : x ∈ (⊥ : SubgroupFunctor _).carrier T := hle T hx
    rwa [SubgroupFunctor.bot_carrier] at h
  exact IsSemisimple.of_fieldExtension (K := AlgebraicClosure k)
    ⟨hGbar, htriv.hasFiniteCenter⟩

end SemisimpleCommutativeNormal

open SemisimpleCommutativeNormal in
/-- **Semisimple groups have no commutative normal subgroup varieties** (Milne,
*Algebraic Groups* (2017), Proposition 19.3), with the converse over perfect fields. -/
theorem semisimpleCommutativeNormalSubgroup :
    SemisimpleCommutativeNormalSubgroupStatement.{u} := by
  intro k _ G hs ha hc
  dsimp only
  refine ⟨fun hG => ?_, fun hp hNo => ?_⟩
  · intro H j hj hHs hHc hcomm hn
    exact range_eq_bot_of_isSemisimple hG H j hj hHs hHc hcomm hn
  · have : IsAffineHom G.X.hom := ha
    have : PerfectField k := hp
    have hCR : IsConnectedReductive G :=
      (perfectFieldPseudoReductive k G).mp
        ⟨hs, ha, hc, hasTrivialUnipotentRadical_of_noCommutativeNormal hNo⟩
    exact isSemisimple_of_noCommutativeNormal hCR hNo

end Langlands.GroupScheme
