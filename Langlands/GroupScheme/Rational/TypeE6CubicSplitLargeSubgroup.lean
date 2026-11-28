import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Rational.AnisotropicGaloisParabolicIntersectionLevi
import Langlands.GroupScheme.Rational.TypeE6ParabolicDimensions
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.StandardLeviDerivedPinning

/-! # The large reductive subgroup of anisotropic type E6 split by a cubic field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private def typeD5FaceEquiv : Fin 5 ≃ {a : Fin 6 // a ≠ 0} :=
  Equiv.ofBijective (fun i => ⟨![(5 : Fin 6), 4, 3, 1, 2] i, by
    fin_cases i <;> decide⟩) (by decide)

private theorem typeD5Face_cartan (a b : Fin 5) :
    CartanMatrix.E 6 (typeD5FaceEquiv a).val (typeD5FaceEquiv b).val =
      CartanMatrix.D 5 a b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Over the splitting field, the standard parabolic of type E6 with its
first long-arm endpoint omitted has codimension sixteen. Its Levi has
an actual simply connected split derived subgroup of type D5. -/
theorem SplitPinning.exists_typeD5_endpointParabolic
    {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : SplitPinning G)
    (e : p.base.support ≃ Fin 6) (hsc : IsSimplyConnected G)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    Lie.dimension G = 78 ∧
    ∃ ν : cocharacterLattice p.torus,
      let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
      let M := Dynamic.Affine.centralizerScheme χ
      haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
      haveI := (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).isAffineHom
      IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) ∧
      Lie.dimension (Dynamic.Affine.parabolicScheme χ) + 16 = 78 ∧
      ∃ (D : GroupScheme (Spec (CommRingCat.of K))) (i : D ⟶ M) (hi : IsDerivedSubgroup i),
        haveI := hi.1.isAffineHom
        IsSimplyConnected D ∧
        ∃ (q : SplitPinning D) (f : q.base.support ≃ Fin 5),
          ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (f a) (f b) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hdim, hparabolic⟩ := typeE6ParabolicDimensions K G p hsc e hE
  obtain ⟨ν, hν, hP, hPdim⟩ := hparabolic {0}
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let M := Dynamic.Affine.centralizerScheme χ
  let m := Dynamic.Affine.centralizerHom χ
  let hm := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let hc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  let : IsAffineHom M.X.hom := hc.isAffineHom
  let : LocallyOfFiniteType M.X.hom := hc.locallyOfFiniteType
  obtain ⟨D, i, _, _, hi⟩ := derivedSubgroupRepresentability K M
  have hνnonneg (a : p.base.support) : 0 ≤ p.rootDatum.root' a.val ν := by
    rw [hν]
    split <;> decide
  obtain ⟨⟨Q⟩, hscD⟩ := p.standardLeviDerivedPinning ν hνnonneg m hm i hi
  let E : Q.pinning.base.support ≃ {a : Fin 6 // a ≠ 0} :=
    Q.vertices.trans (e.subtypeEquiv (fun a => by
      rw [hν]
      by_cases ha : e a = 0 <;> simp [ha]))
  let f : Q.pinning.base.support ≃ Fin 5 := E.trans typeD5FaceEquiv.symm
  refine ⟨hdim, ν, hP, ?_, D, i, hi, hscD hsc, Q.pinning, f, fun a b => ?_⟩
  · exact Langlands.CartanE6Root.parabolicCodimensionCounts.1 ▸ hPdim
  · have hf (a : Q.pinning.base.support) : (typeD5FaceEquiv (f a)).val = e (Q.vertices a).val :=
      congrArg Subtype.val (typeD5FaceEquiv.apply_symm_apply (E a))
    rw [Q.cartan_eq, hE, ← hf a, ← hf b, typeD5Face_cartan]

section Cubic

variable {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local notation "B" => GroupScheme.baseChange (algebraBaseMap k K)
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- In a cubic splitting of anisotropic E6, the rational reductive
intersection subgroup has dimension at least thirty and its derived group
embeds over the cubic field into the split simply connected D5. -/
theorem IsAnisotropic.exists_typeE6_cubicSplit_largeSubgroup
    (hG : IsAnisotropic G) (hsc : IsSimplyConnected G) (hK : Module.finrank k K = 3)
    (p : SplitPinning G_K) (e : p.base.support ≃ Fin 6)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
      haveI := hj.isAffineHom
      IsConnectedReductive H ∧ 30 ≤ Lie.dimension H ∧
      ∃ (H' : GroupScheme (Spec (CommRingCat.of k))) (i : H' ⟶ H) (hi : IsDerivedSubgroup i)
        (D : GroupScheme (Spec (CommRingCat.of K))) (hDaff : IsAffineHom D.X.hom)
        (l : Functor.obj B H' ⟶ D),
        haveI := hi.1.isAffineHom
        haveI := hDaff
        IsClosedSubgroup l ∧ IsSemisimple H' ∧ IsSimplyConnected D ∧
          ∃ (q : SplitPinning D) (f : q.base.support ≃ Fin 5),
            ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (f a) (f b) := by
  let : LocallyOfFiniteType (G_K).X.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
  obtain ⟨hdim, ν, hP, hPdim, D, d, hd, hscD, q, f, hD⟩ :=
    p.exists_typeD5_endpointParabolic e (isSimplyConnectedFieldExtension k K G hsc) hE
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let : IsAffine (G_K).X.left := isAffine_of_isAffineHom (G_K).X.hom
  let : IsAffineHom (Dynamic.Affine.centralizerScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).isAffineHom
  have hcodim : haveI := hP.isClosedSubgroup.isAffineHom
      Lie.dimension G_K ≤ Lie.dimension (Dynamic.Affine.parabolicScheme χ) + 16 := by
    rw [hdim, hPdim]
  obtain ⟨H, j, hj, hH, hbound, l, _, hl⟩ := hG.exists_reductive_subgroup_of_parabolic_orbit
    k K G hsc.isSemisimple χ hP 16 hcodim
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : LocallyOfFiniteType H.X.hom := hj.locallyOfFiniteType
  obtain ⟨H', i, _, _, hi⟩ := derivedSubgroupRepresentability k H
  have hiK := hi.baseChange_of_eq (algebraBaseMap k K)
    (derivedSubgroup_baseChange_eq_of_field (algebraBaseMap k K) H)
  let l₀ := l ≫ Corepresented.limitGroupHom (Dynamic.Affine.cocharacter χ)
  let l' := hiK.map hd l₀
  have hl' : IsClosedSubgroup l' := IsClosedSubgroup.of_comp hd.1 (by
    rw [hiK.map_comp hd l₀]
    exact hiK.1.comp hl)
  rw [hdim, hK] at hbound
  refine ⟨H, j, hj, hH, by omega, H', i, hi, D, hd.1.isAffineHom, l', hl', ?_, hscD, q, f, hD⟩
  exact derivedSubgroupSemisimple k H H' i hH hi

end Cubic

/-- An anisotropic group split as type E6 by a cubic Galois extension has
a connected reductive subgroup of dimension at least thirty whose derived
group embeds into split D5 after extension. -/
def TypeE6CubicSplitLargeSubgroupStatement : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsGalois k K], Module.finrank k K = 3 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSimplyConnected G →
    let B := GroupScheme.baseChange (algebraBaseMap k K)
    ∀ (p : SplitPinning (B.obj G)) (e : p.base.support ≃ Fin 6),
      (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
        haveI := hj.isAffineHom
        IsConnectedReductive H ∧ 30 ≤ Lie.dimension H ∧
        ∃ (H' : GroupScheme (Spec (CommRingCat.of k))) (i : H' ⟶ H) (hi : IsDerivedSubgroup i)
          (D : GroupScheme (Spec (CommRingCat.of K))) (hDaff : IsAffineHom D.X.hom)
          (l : B.obj H' ⟶ D),
          haveI := hi.1.isAffineHom
          haveI := hDaff
          IsClosedSubgroup l ∧ IsSemisimple H' ∧ IsSimplyConnected D ∧
            ∃ (q : SplitPinning D) (f : q.base.support ≃ Fin 5),
              ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (f a) (f b)

theorem typeE6CubicSplitLargeSubgroup : TypeE6CubicSplitLargeSubgroupStatement.{u} := by
  intro k K _ _ _ _ _ _ hK G _ _ hG hsc B p e hE
  exact hG.exists_typeE6_cubicSplit_largeSubgroup hsc hK p e hE

end Langlands.GroupScheme
