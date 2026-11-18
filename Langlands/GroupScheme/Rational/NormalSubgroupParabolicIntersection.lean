import Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerStatement
import Langlands.GroupScheme.Rational.NormalSubgroupIntersectionStatement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.Absolute.RationalNormalizer
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.SubgroupIntersectionDescent
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization

/-! # Normal subgroups meet parabolic and Borel subgroups well, given the normalizer theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace NormalSubgroupParabolicIntersection

section General

variable {S : Scheme.{u}}

/-- If `h` is a monomorphism and `u ≫ h` lies in the range of `z ≫ h`, then `u` lies in the
range of `z`. -/
theorem mem_range_of_comp_mem_range_comp {H G Z : GroupScheme S} {h : H ⟶ G}
    [Mono h.hom.hom] (z : Z ⟶ H) {V : Over S} {u : V ⟶ H.X}
    (hu : u ≫ h.hom.hom ∈ (SubgroupFunctor.range (z ≫ h)).carrier V) :
    u ∈ (SubgroupFunctor.range z).carrier V := by
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hu
  refine SubgroupFunctor.mem_range.mpr ⟨t, ?_⟩
  apply (cancel_mono h.hom.hom).mp
  rw [Category.assoc, ← Grp.comp_hom_hom]
  exact ht

/-- The range of a composite lies in the range of the second map. -/
theorem range_comp_le {H G Z : GroupScheme S} (z : Z ⟶ H) (h : H ⟶ G) :
    SubgroupFunctor.range (z ≫ h) ≤ SubgroupFunctor.range h := by
  intro V x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨t ≫ z.hom.hom, by rw [Category.assoc, Grp.comp_hom_hom]⟩

end General

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, the rational points of a group scheme locally of finite
type factor through its reduced subgroup. -/
theorem range_carrier_base_le_reducedSubgroupι
    {Q G : GroupScheme (Spec (CommRingCat.of K))} [LocallyOfFiniteType Q.X.hom] (r : Q ⟶ G) :
    (SubgroupFunctor.range r).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≤
      (SubgroupFunctor.range (reducedSubgroupι Q ≫ r)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
  intro x hx
  obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  refine SubgroupFunctor.mem_range.mpr ⟨ReducedSubgroup.liftOver w, ?_⟩
  rw [Grp.comp_hom_hom, ReducedSubgroup.reducedSubgroupι_hom_hom, ← Category.assoc,
    ReducedSubgroup.liftOver_fac]

/-- Over an algebraically closed field `K`, let `G` be smooth connected affine, `h : H ⟶ G` a
smooth connected normal closed subgroup, and `p : P ⟶ G` a smooth closed subgroup through which
a Borel subgroup `j` of `G` factors. Assuming the normalizer theorem
`BorelContainingSubgroupSelfNormalizerStatement`, the scheme-theoretic intersection `H ∩ P` is
smooth and connected, and a Borel subgroup of `H` factors through it. -/
theorem exists_borel_parabolicIntersection_algClosed
    (hI1 : BorelContainingSubgroupSelfNormalizerStatement.{u})
    {G H P B : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [Smooth P.X.hom]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal)
    (p : P ⟶ G) (hp : IsClosedSubgroup p)
    (j : B ⟶ G) (hj : IsBorelSubgroup j) (f : B ⟶ P) (hf : f ≫ p = j) :
    Smooth (subgroupIntersection h p).X.hom ∧
      ConnectedSpace (subgroupIntersection h p).X.left ∧
      ∃ (C : GroupScheme (Spec (CommRingCat.of K))) (c : C ⟶ H)
        (e : C ⟶ subgroupIntersection h p),
        IsBorelSubgroup c ∧ e ≫ subgroupIntersectionFst h p = c := by
  have : IsAffineHom H.X.hom := hh.isAffineHom
  have : IsAffineHom P.X.hom := hp.isAffineHom
  have : Mono h.hom.hom.left := hh.mono
  have : Mono h.hom.hom := Over.mono_of_mono_left _
  -- The intersection `Q = H ∩ P`, its reduced subgroup `Z`, and their inclusions into `H`.
  set Q := subgroupIntersection h p with hQdef
  set q := subgroupIntersectionFst h p with hqdef
  have hq : IsClosedSubgroup q := isClosedSubgroup_subgroupIntersectionFst h hp
  have : LocallyOfFiniteType Q.X.hom := hq.locallyOfFiniteType
  have : IsAffineHom Q.X.hom := hq.isAffineHom
  let iZ := reducedSubgroupι Q
  let z : reducedSubgroup Q ⟶ H := iZ ≫ q
  have hι : IsClosedSubgroup iZ :=
    (inferInstance : IsClosedImmersion (reducedSubgroupι Q).hom.hom.left)
  have hz : IsClosedSubgroup z := hι.comp hq
  have hzh : IsClosedSubgroup (z ≫ h) := hz.comp hh
  -- Step 1: a Borel subgroup of `H` that factors through `Z`.
  obtain ⟨C₀, c₀, hc₀⟩ := (borelConjugacy K H).1
  have : Smooth C₀.X.hom := hc₀.smooth
  have : ConnectedSpace C₀.X.left := hc₀.connectedSpace
  obtain ⟨B', i', f', hi', hf'⟩ := solvableSubgroupBorelContainment K G C₀ (c₀ ≫ h)
    (hc₀.isClosedSubgroup.comp hh) hc₀.isSolvableGroupScheme
  obtain ⟨g, φ, hg⟩ := (borelConjugacy K G).2 B' B i' j hi' hj
  let c := c₀ ≫ (hh.isRepresentedBy_range.conjugateIso hn g).hom
  have hc : IsBorelSubgroup c := hc₀.comp_iso _
  have hcd : c ≫ h = (f' ≫ φ.hom ≫ f) ≫ p := by
    simp only [c, Category.assoc, SubgroupFunctor.IsRepresentedBy.conjugateIso_hom_comp, hf]
    rw [← Category.assoc c₀ h, ← hf', Category.assoc, hg]
  let e₀ : C₀ ⟶ Q := pullback.lift c (f' ≫ φ.hom ≫ f) hcd
  have he₀ : e₀ ≫ q = c := pullback.lift_fst _ _ _
  have : IsReduced C₀.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ C₀.X.hom
  let c' := ReducedSubgroup.liftHom e₀
  have hc' : c' ≫ z = c := by
    simp only [c', z, iZ, ReducedSubgroup.liftHom_fac_assoc, he₀]
  -- Step 2: the normalizer theorem applied to `Z` in `H`.
  have hgeo : IsGeometricBorelSubgroup c :=
    ⟨hc, borelAlgClosedFieldExtensionStatement K (AlgebraicClosure K) H inferInstance
      inferInstance inferInstance C₀ c hc⟩
  obtain ⟨hZconn, hZnorm⟩ := hI1 K H (reducedSubgroup Q) C₀ z c c' hz inferInstance hgeo hc'
  -- Step 3: `P` normalizes `Z` inside `G`.
  have hkey : ∀ x ∈ (SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))),
      ∀ y ∈ (SubgroupFunctor.range (z ≫ h)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))),
        x * y * x⁻¹ ∈
          (SubgroupFunctor.range (z ≫ h)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    intro x hx y hy
    have hyh : y ∈ (SubgroupFunctor.range h).carrier _ := range_comp_le z h _ hy
    have hyp : y ∈ (SubgroupFunctor.range p).carrier _ := by
      have hzp : z ≫ h = (iZ ≫ subgroupIntersectionSnd h p) ≫ p := by
        simp only [z, q, Category.assoc, subgroupIntersection_condition]
      rw [hzp] at hy
      exact range_comp_le _ p _ hy
    have h1 : x * y * x⁻¹ ∈ (SubgroupFunctor.range h).carrier _ :=
      hn _ x y (Subgroup.mem_top _) hyh
    have h2 : x * y * x⁻¹ ∈ (SubgroupFunctor.range p).carrier _ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hyp) (Subgroup.inv_mem _ hx)
    have h3 : x * y * x⁻¹ ∈ (SubgroupFunctor.range (q ≫ h)).carrier _ := by
      have := range_subgroupIntersectionHom h p
      change SubgroupFunctor.range (q ≫ h) = _ at this
      rw [this]
      exact ⟨h1, h2⟩
    have h4 := range_carrier_base_le_reducedSubgroupι (q ≫ h) h3
    simpa only [z, Category.assoc] using h4
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hnc, hnrep⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range (z ≫ h) hzh).1
  have : IsReduced P.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ P.X.hom
  have hPN : SubgroupFunctor.range p ≤ (SubgroupFunctor.range (z ≫ h)).normalizer := by
    rw [← hnrep.2]
    apply SubgroupFunctor.range_le_of_algClosed_points hnc
    rw [hnrep.2, SubgroupFunctor.normalizer_range_carrier_base_eq_algClosed_points hzh]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hkey x hx y
    · intro hy
      have := hkey x⁻¹ (Subgroup.inv_mem _ hx) _ hy
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
  -- Step 4: every point of `Q` normalizes `Z` in `H`, so it lies in `Z`.
  have hQZ : SubgroupFunctor.range q ≤ SubgroupFunctor.range z := by
    rw [← hZnorm]
    intro V x hx
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [SubgroupFunctor.mem_normalizer]
    intro V' a y hy
    have hxp : (a ≫ w ≫ q.hom.hom) ≫ h.hom.hom ∈ (SubgroupFunctor.range p).carrier V' := by
      refine SubgroupFunctor.mem_range.mpr ⟨a ≫ w ≫ (subgroupIntersectionSnd h p).hom.hom, ?_⟩
      simp only [Category.assoc, ← Grp.comp_hom_hom, q, subgroupIntersection_condition]
    have hxN := hPN V' hxp
    have hyh : y ≫ h.hom.hom ∈ (SubgroupFunctor.range (z ≫ h)).carrier V' := by
      obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hy
      exact SubgroupFunctor.mem_range.mpr ⟨t, by rw [Grp.comp_hom_hom, Category.assoc]⟩
    have h1 := (SubgroupFunctor.mem_normalizer.mp hxN) V' (𝟙 V') _ hyh
    rw [Category.id_comp] at h1
    constructor
    · apply mem_range_of_comp_mem_range_comp (h := h) z
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      exact h1.1
    · apply mem_range_of_comp_mem_range_comp (h := h) z
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      exact h1.2
  -- Step 5: `Z ≅ Q`, so `Q` is smooth and connected.
  have hrange : SubgroupFunctor.range z = SubgroupFunctor.range q :=
    le_antisymm (range_comp_le iZ q) hQZ
  let eZQ := hz.sourceIsoOfRangeEq hq hrange
  refine ⟨smooth_of_over_iso (X := Q.X) (Y := (reducedSubgroup Q).X)
    ((Grp.forget _).mapIso eZQ.symm) inferInstance, ?_,
    C₀, c, e₀, hc, he₀⟩
  exact (Scheme.homeoOfIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eZQ))).connectedSpace_iff.1
    hZconn

/-- Over an algebraically closed field `K`, let `G` be smooth connected affine, `h : H ⟶ G` a
smooth connected normal closed subgroup and `j : B ⟶ G` a Borel subgroup. Assuming the
normalizer theorem `BorelContainingSubgroupSelfNormalizerStatement`, the first projection of the
scheme-theoretic intersection `H ∩ B` is a Borel subgroup of `H`. -/
theorem isBorelSubgroup_borelIntersection_algClosed
    (hI1 : BorelContainingSubgroupSelfNormalizerStatement.{u})
    {G H B : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal)
    (j : B ⟶ G) (hj : IsBorelSubgroup j) :
    IsBorelSubgroup (subgroupIntersectionFst h j) := by
  have : Smooth B.X.hom := hj.smooth
  obtain ⟨hsm, hconn, C, c, e, hc, he⟩ :=
    exists_borel_parabolicIntersection_algClosed hI1 h hh hn j hj.isClosedSubgroup j hj (𝟙 B)
      (Category.id_comp j)
  -- `H ∩ B` is solvable: its rational points embed into those of `B`.
  have : IsClosedImmersion (subgroupIntersectionSnd h j).hom.hom.left :=
    MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme h j) hh
  have : Mono (subgroupIntersectionSnd h j).hom.hom := Over.mono_of_mono_left _
  have hsol : IsSolvableGroupScheme (subgroupIntersection h j) := by
    rw [isSolvableGroupScheme_iff_rationalPoints]
    have := (isSolvableGroupScheme_iff_rationalPoints B).mp hj.isSolvableGroupScheme
    let ρ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (subgroupIntersection h j).X) →*
        (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B.X) :=
      { toFun := fun y => y ≫ (subgroupIntersectionSnd h j).hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun y y' => MonObj.mul_comp _ _ _ }
    exact Group.isSolvable_of_isSolvable_injective (f := ρ)
      (fun y y' hyy' => (cancel_mono (subgroupIntersectionSnd h j).hom.hom).1 hyy')
  -- By maximality of the Borel subgroup `C` of `H`, the factorization `e` is an isomorphism.
  have : IsIso e := hc.maximal _ _ e
    (isClosedSubgroup_subgroupIntersectionFst h hj.isClosedSubgroup) hsm hconn hsol he
  have hfst : subgroupIntersectionFst h j = (asIso e).symm.hom ≫ c := by
    rw [← he, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc]
  rw [hfst]
  exact hc.iso_comp _

end AlgClosed

section Descent

variable {k : Type u} [Field k]

/-- Clauses (ii) and (iii) of Conrad's Exercise 5.5.1 over an arbitrary field `k`, assuming the
normalizer theorem `BorelContainingSubgroupSelfNormalizerStatement`: for a smooth connected
affine `G` and a smooth connected normal closed subgroup `h : H ⟶ G`, the scheme-theoretic
intersection of `H` with a parabolic subgroup of `G` is a connected parabolic subgroup of `H`,
and its intersection with a geometric Borel subgroup of `G` is a geometric Borel subgroup of
`H`. This is the second conjunct of `NormalSubgroupIntersectionStatement` for `k` and `G`. -/
theorem normalSubgroupParabolicIntersection_of_borelSelfNormalizer
    (hI1 : BorelContainingSubgroupSelfNormalizerStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (hGs : Smooth G.X.hom) (hGa : IsAffineHom G.X.hom) (hGc : ConnectedSpace G.X.left) :
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
      IsClosedSubgroup h → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range h).IsNormal →
      (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        IsParabolicSubgroup p →
        ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ H),
          IsParabolicSubgroup q ∧ ConnectedSpace Q.X.left ∧
            SubgroupFunctor.range (q ≫ h) =
              SubgroupFunctor.range h ⊓ SubgroupFunctor.range p) ∧
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsGeometricBorelSubgroup b →
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ H),
          IsGeometricBorelSubgroup c ∧
            SubgroupFunctor.range (c ≫ h) =
              SubgroupFunctor.range h ⊓ SubgroupFunctor.range b := by
  intro H h hh hHs hHc hn
  -- Base change to the algebraic closure `K` of `k`.
  let β := toAlgebraicClosure k
  let F := GroupScheme.baseChange β
  have : Smooth (F.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom β))
  have : IsAffineHom (F.obj G).X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom β))
  have : ConnectedSpace (F.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine β
  have : IsAffineHom H.X.hom := hh.isAffineHom
  have : Smooth (F.obj H).X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom β))
  have : ConnectedSpace (F.obj H).X.left := H.connectedSpace_baseChange_of_smooth_affine β
  have hhK : IsClosedSubgroup (F.map h) := hh.baseChange β
  have hnK : (SubgroupFunctor.range (F.map h)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact SubgroupFunctor.IsNormal.baseChange β hn
  obtain ⟨hsurj, -, -⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  refine ⟨fun P p hp => ?_, fun B b hb => ?_⟩
  · -- Clause (ii): `Q = H ∩ P` with its first projection.
    have : Smooth P.X.hom := hp.smooth
    have : Smooth (F.obj P).X.hom := inferInstanceAs (Smooth (pullback.snd P.X.hom β))
    obtain ⟨BK, jK, fK, hjK, hfK⟩ := hp.exists_isBorelSubgroup
    obtain ⟨hsm, hconn, C, c, e, hc, he⟩ :=
      exists_borel_parabolicIntersection_algClosed hI1 (F.map h) hhK hnK (F.map p)
        (hp.isClosedSubgroup.baseChange β) jK hjK fK hfK
    refine ⟨subgroupIntersection h p, subgroupIntersectionFst h p,
      ⟨isClosedSubgroup_subgroupIntersectionFst h hp.isClosedSubgroup,
        smooth_pullback_of_smooth_pullback_baseChange h p hsm,
        C, c, e ≫ (subgroupIntersectionBaseChangeIso β h p).inv, hc, ?_⟩,
      connectedSpace_of_baseChange β _ (connectedSpace_baseChange_pullback h p hconn),
      range_subgroupIntersectionHom h p⟩
    rw [← he, Category.assoc]
    congr 1
    exact PreservesPullback.iso_inv_fst F h p
  · -- Clause (iii): `C = H ∩ B` with its first projection.
    have hBK := isBorelSubgroup_borelIntersection_algClosed hI1 (F.map h) hhK hnK (F.map b) hb.2
    refine ⟨subgroupIntersection h b, subgroupIntersectionFst h b, ?_,
      range_subgroupIntersectionHom h b⟩
    apply isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure _
      (isClosedSubgroup_subgroupIntersectionFst h hb.1.isClosedSubgroup)
    have hfst : F.map (subgroupIntersectionFst h b) =
        (subgroupIntersectionBaseChangeIso β h b).hom ≫
          subgroupIntersectionFst (F.map h) (F.map b) :=
      (PreservesPullback.iso_hom_fst F h b).symm
    rw [hfst]
    exact hBK.iso_comp _

end Descent

/-- `NormalSubgroupIntersectionStatement` follows from the normalizer theorem
`BorelContainingSubgroupSelfNormalizerStatement` together with its first clause (maximal tori
of subgroups normalized by a maximal torus). -/
theorem normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer
    (hI1 : BorelContainingSubgroupSelfNormalizerStatement.{u})
    (htorus : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsMaximalTorus t →
        ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
          IsClosedSubgroup n → Smooth N.X.hom → ConnectedSpace N.X.left →
          (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range t) →
          ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ N),
            IsMaximalTorus c ∧
              SubgroupFunctor.range (c ≫ n) =
                SubgroupFunctor.range n ⊓ SubgroupFunctor.range t) :
    NormalSubgroupIntersectionStatement.{u} :=
  fun k _ G hGs hGa hGc => ⟨htorus k G hGs hGa hGc,
    normalSubgroupParabolicIntersection_of_borelSelfNormalizer hI1 G hGs hGa hGc⟩

end NormalSubgroupParabolicIntersection

end Langlands.GroupScheme
