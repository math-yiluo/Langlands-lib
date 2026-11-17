import Langlands.GroupScheme.Torus.NormalSubgroupMaximalStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.RelativeLargestSubtorusProof
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.BaseChangeReflection

/-! # Maximal tori of a normal subgroup variety (Milne, Corollary 17.85) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace NormalSubgroupMaximalTorus

variable {k : Type u} [Field k]

/-- The range of a composite lies in the range of its second factor. -/
theorem range_comp_le {S : Scheme.{u}} {A B C : GroupScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    SubgroupFunctor.range (f ≫ g) ≤ SubgroupFunctor.range g := by
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2 ⟨y ≫ f.hom.hom, ?_⟩
  rw [Grp.comp_hom_hom, Category.assoc]

/-- A closed subgroup of a torus over a field is of multiplicative type in the relative
(fppf-local) sense: it becomes diagonalizable over a finite Galois splitting field. -/
theorem isRelativeMultiplicativeType_of_isClosedSubgroup
    {T H : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) (i : H ⟶ T)
    (hi : IsClosedSubgroup i) : RelativeMultiplicativeType.IsMultiplicativeType H := by
  obtain ⟨K, hK, aK, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T hT
  let := hK
  let := aK
  let := hfin
  let := hgal
  let : Algebra.FinitePresentation k K :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : Etale b := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      ⟨Algebra.FormallyEtale.of_isSeparable k K, inferInstance⟩
  have hs : Surjective b := (fieldExtension_fpqc k K).1
  have : Etale b := hb
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
      (Spec (CommRingCat.of k)) :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => Spec (CommRingCat.of K)) (fun _ => b)
      (fun x => by
        obtain ⟨y, hy⟩ := hs.surj x
        exact ⟨PUnit.unit, y, hy⟩) (fun _ => ⟨inferInstance, inferInstance⟩)
  refine ⟨𝒰, fun a => ?_⟩
  change RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange b).obj H)
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := exists_diagonalizableIso_of_isClosedSubgroup_splitTorus hsplit
    ((GroupScheme.baseChange b).map i) (hi.baseChange b)
  exact ⟨Λ, hΛ, hfg, ⟨e ≪≫ (Diagonalizable.baseChangeIso (Gm.toSpecZ _) Λ).symm⟩⟩

/-- Part (2): every maximal torus of a closed subgroup lies in a maximal torus of `G`. -/
theorem exists_isMaximalTorus_range_le_of_subgroup
    (G N : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N) (hs : IsMaximalTorus s) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j := by
  obtain ⟨T, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G (s ≫ n) hs.1 (hs.2.1.comp hn)
  refine ⟨T, j, hj, ?_⟩
  rw [← hf]
  exact range_comp_le f j

/-- The inverse of the base-change comparison for subgroup intersections is compatible with
the second projections. -/
theorem subgroupIntersectionBaseChangeIso_inv_snd {S S' : Scheme.{u}} {P P' G : GroupScheme S}
    (b : S' ⟶ S) (j : P ⟶ G) (j' : P' ⟶ G) :
    (subgroupIntersectionBaseChangeIso b j j').inv ≫
        (GroupScheme.baseChange b).map (subgroupIntersectionSnd j j') =
      subgroupIntersectionSnd ((GroupScheme.baseChange b).map j)
        ((GroupScheme.baseChange b).map j') :=
  PreservesPullback.iso_inv_snd _ _ _

/-- A closed torus `s` of `N` through which a maximal torus `s₁` of `N` factors is itself a
maximal torus: maximality of `s₁` makes the factoring map an isomorphism. -/
theorem isMaximalTorus_of_comp_eq {N : GroupScheme (Spec (CommRingCat.of k))}
    {S S₁ : CommGroupScheme (Spec (CommRingCat.of k))} (s : S.toGrp ⟶ N) (s₁ : S₁.toGrp ⟶ N)
    (hS : IsTorus S.toGrp) (hs : IsClosedSubgroup s) (hs₁ : IsMaximalTorus s₁)
    (a : S₁.toGrp ⟶ S.toGrp) (ha : a ≫ s = s₁) : IsMaximalTorus s := by
  have : IsIso a := hs₁.2.2 S s a hS hs ha
  have hmax := IsMaximalTorus.iso_comp (asIso a).symm hs₁
  rwa [Iso.symm_hom, asIso_inv, ← ha, IsIso.inv_hom_id_assoc] at hmax

/-- Over an algebraically closed field, let `s₀ : S₀ → N` be a maximal torus of a closed
normal subgroup `N` of a smooth connected affine group `G`, lying in a maximal torus `T₀` of
`G`. For every maximal torus `T` of `G` there is another maximal torus `s₁ : S₀ → N` of `N`
(the conjugate of `s₀` by an element carrying `T₀` to `T`) that lies in `T`. -/
theorem exists_conjugate_maximalTorus_factor [IsAlgClosed k]
    (G N : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hnorm : (SubgroupFunctor.range n).IsNormal)
    {T T₀ S₀ : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j) (j₀ : T₀.toGrp ⟶ G) (hj₀ : IsMaximalTorus j₀)
    (s₀ : S₀.toGrp ⟶ N) (hs₀ : IsMaximalTorus s₀) (f₀ : S₀.toGrp ⟶ T₀.toGrp)
    (hf₀ : f₀ ≫ j₀ = s₀ ≫ n) :
    ∃ (s₁ : S₀.toGrp ⟶ N) (t : S₀.toGrp ⟶ T.toGrp), IsMaximalTorus s₁ ∧ t ≫ j = s₁ ≫ n := by
  obtain ⟨g, φ, hg⟩ := maximalTorusConjugacy k G T₀ T j₀ j hj₀ hj
  let c := hn.isRepresentedBy_range.conjugateIso hnorm g
  refine ⟨s₀ ≫ c.hom, f₀ ≫ CommGroupScheme.groupHom φ.hom, hs₀.comp_iso c, ?_⟩
  rw [Category.assoc, ← hg, ← Category.assoc, hf₀, Category.assoc, Category.assoc,
    SubgroupFunctor.IsRepresentedBy.conjugateIso_hom_comp]

/-- Part (1): a maximal torus `T` of `G` contains a maximal torus of the smooth closed normal
subgroup `N`, namely the universal subtorus `(T ∩ N)_t` of the scheme-theoretic
intersection `T ∩ N`. -/
theorem exists_isMaximalTorus_range_le_of_normal
    (G N : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : Smooth N.X.hom)
    (hnorm : (SubgroupFunctor.range n).IsNormal)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N),
      IsMaximalTorus s ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j := by
  have : Smooth N.X.hom := hN
  have : IsAffineHom N.X.hom := hn.isAffineHom
  -- The scheme-theoretic intersection `T ∩ N` and its two closed projections.
  let p := subgroupIntersectionFst j n
  let q := subgroupIntersectionSnd j n
  have hp : IsClosedSubgroup p := isClosedSubgroup_subgroupIntersectionFst j hn
  have hq : IsClosedSubgroup q := by
    have : IsClosedImmersion j.hom.hom.left := hj.2.1
    change IsClosedImmersion (subgroupIntersectionSnd j n).hom.hom.left
    exact MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme j n) this
  have hpq : p ≫ j = q ≫ n := subgroupIntersection_condition j n
  -- Its universal subtorus `(T ∩ N)_t`, regarded as a closed torus of `N`.
  obtain ⟨U, u, hu⟩ :=
    (isRelativeMultiplicativeType_of_isClosedSubgroup hj.1 p hp).exists_universalSubtorus
  let S := hu.2.1.commGroupScheme
  let s : S.toGrp ⟶ N := u ≫ q
  have hsn : s ≫ n = (u ≫ p) ≫ j := by
    change (u ≫ q) ≫ n = (u ≫ p) ≫ j
    rw [Category.assoc, Category.assoc, hpq]
  have hSt : IsTorus S.toGrp := hu.2.1.isTorus
  have hsc : IsClosedSubgroup s := hu.1.comp hq
  refine ⟨S, s, ?_, by rw [hsn]; exact range_comp_le (u ≫ p) j⟩
  -- Maximality is checked over an algebraic closure `K` of `k`.
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let F' := CommGroupScheme.baseChange b
  apply (maximalTorusBaseChange k K N S s hSt hsc).mpr
  have : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine b
  have hnormK : (SubgroupFunctor.range (F.map n)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hnorm.baseChange b
  -- A maximal torus `S₀` of `N`, inside a maximal torus `T₀` of `G`.
  obtain ⟨S₀, s₀, hs₀⟩ := maximalTorusExistence k N
  obtain ⟨T₀, j₀, hj₀, f₀, hf₀⟩ :=
    exists_maximalTorus_extension_of_finiteType G (s₀ ≫ n) hs₀.1 (hs₀.2.1.comp hn)
  have hjK : IsMaximalTorus (T := F'.obj T) (F.map j) :=
    (maximalTorusBaseChange k K G T j hj.1 hj.2.1).mp hj
  have hj₀K : IsMaximalTorus (T := F'.obj T₀) (F.map j₀) :=
    (maximalTorusBaseChange k K G T₀ j₀ hj₀.1 hj₀.2.1).mp hj₀
  have hs₀K : IsMaximalTorus (T := F'.obj S₀) (F.map s₀) :=
    (maximalTorusBaseChange k K N S₀ s₀ hs₀.1 hs₀.2.1).mp hs₀
  have hf₀K : F.map f₀ ≫ F.map j₀ = F.map s₀ ≫ F.map n := by
    rw [← F.map_comp, hf₀, F.map_comp]
  -- Over `K`, a conjugate `S₁` of `S₀` inside `N` lies in `T ∩ N`, hence in `(T ∩ N)_t`.
  obtain ⟨s₁, t, hs₁, ht⟩ := exists_conjugate_maximalTorus_factor (F.obj G) (F.obj N) (F.map n)
    (hn.baseChange b) hnormK (T := F'.obj T) (T₀ := F'.obj T₀) (S₀ := F'.obj S₀)
    (F.map j) hjK (F.map j₀) hj₀K (F.map s₀) hs₀K (F.map f₀) hf₀K
  let t' : (F'.obj S₀).toGrp ⟶ F.obj T.toGrp := t
  have ht' : t' ≫ F.map j = s₁ ≫ F.map n := ht
  let l : (F'.obj S₀).toGrp ⟶ subgroupIntersection (F.map j) (F.map n) :=
    pullback.lift t' s₁ ht'
  have hl : l ≫ subgroupIntersectionSnd (F.map j) (F.map n) = s₁ := pullback.lift_snd _ _ _
  let w := l ≫ (subgroupIntersectionBaseChangeIso b j n).inv
  have hw : w ≫ F.map q = s₁ := by
    change (l ≫ (subgroupIntersectionBaseChangeIso b j n).inv) ≫
      F.map (subgroupIntersectionSnd j n) = s₁
    rw [Category.assoc, subgroupIntersectionBaseChangeIso_inv_snd, hl]
  have hS₀t : RelativeTorus.IsTorus (F'.obj S₀).toGrp :=
    (hs₀.1.baseChange (K := K)).isRelativeTorus
  obtain ⟨a, ha⟩ := hu.2.2 _ b (F'.obj S₀).toGrp w hS₀t
  have has : a ≫ F.map s = s₁ := by
    change a ≫ F.map (u ≫ q) = s₁
    rw [F.map_comp, ← Category.assoc, ha, hw]
  exact isMaximalTorus_of_comp_eq (S := F'.obj S) (S₁ := F'.obj S₀) (F.map s) s₁
    (hSt.baseChange (K := K)) (hsc.baseChange b) hs₁ a has

end NormalSubgroupMaximalTorus

open NormalSubgroupMaximalTorus in
/-- **Milne, Corollary 17.85**, in the containment form of
`NormalSubgroupMaximalTorusStatement`: for a smooth closed normal subgroup `N` of a smooth
connected affine group `G` over a field, every maximal torus of `G` contains a maximal torus
of `N`, and every maximal torus of `N` lies in a maximal torus of `G`. -/
theorem normalSubgroupMaximalTorus : NormalSubgroupMaximalTorusStatement.{u} := by
  intro k _ G _ _ _ N n hn hN hnorm
  exact ⟨fun T j hj => exists_isMaximalTorus_range_le_of_normal G N n hn hN hnorm T j hj,
    fun S s hs => exists_isMaximalTorus_range_le_of_subgroup G N n hn S s hs⟩

end Langlands.GroupScheme
