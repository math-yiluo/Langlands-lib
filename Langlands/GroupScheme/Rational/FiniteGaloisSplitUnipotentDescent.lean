import Langlands.GroupScheme.Rational.PolynomialNormImage
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorStatement
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Lie.QuotientConnectedKernelDimension
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.DominantHomFlatProof

/-! # Finite-Galois descent of split unipotence from central vector subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable (hstable : SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

local notation "b" => algebraBaseMap k L
local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

include hstable

/-- A nontrivial smooth connected unipotent group split by a finite Galois
extension has a nontrivial central smooth connected split subgroup over the
base field, conditional on the stated stable-vector theorem. -/
theorem exists_central_split_subgroup_of_finiteGalois
    (hU : IsUnipotent G) (hsplit : IsSplitUnipotent G_L)
    (hne : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
      IsClosedSubgroup i ∧ Smooth N.X.hom ∧ IsAffineHom N.X.hom ∧
      ConnectedSpace N.X.left ∧ IsCentral i ∧ IsSplitUnipotent N ∧
      SubgroupFunctor.range i ≠ ⊥ := by
  have hfaith : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat b := hfaith.1
  let : Surjective b := hfaith.2
  let : QuasiCompact b := by dsimp [algebraBaseMap]; infer_instance
  let : Smooth (G_L).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom (G_L).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace (G_L).X.left := G.connectedSpace_baseChange_of_smooth_affine b
  have hneL : SubgroupFunctor.range (𝟙 G_L) ≠ ⊥ := by
    intro h
    apply hne
    apply SubgroupFunctor.eq_bot_of_baseChange_eq_bot b
    rw [← SubgroupFunctor.range_baseChangeHom, CategoryTheory.Functor.map_id]
    exact h
  obtain ⟨V, z, _aV, n, e, hz, _hVs, _hVa, _hVc, _hVu, _hVsplit,
      hcent, _hstable, _hnt, hn, _hdim, he, _heq⟩ :=
    hstable L G_L inferInstance inferInstance inferInstance hU.baseChange hsplit hneL
      G_L inferInstance inferInstance (AutomorphicAction.conjugation (𝟙 G_L))
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  let f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L :=
    (vectorGroupIso e he).inv ≫ z
  let : Mono f.hom.hom := by
    change Mono ((vectorGroupIso e he).inv.hom.hom ≫ z.hom.hom)
    infer_instance
  let d := PolynomialPoint.centralSplitImageOfCentralHom k L G f (hcent.comp _) hn
  exact ⟨d.groupScheme, d.inclusion, d.closed, d.smooth, d.affine, d.connected,
    d.central, d.split, d.range_ne_bot⟩

/-- Split unipotence descends from a finite Galois field extension for smooth
connected affine unipotent groups, using the explicit stable-vector premise. -/
theorem IsSplitUnipotent.of_finiteGalois_of_stableVector
    (hU : IsUnipotent G) (hsplit : IsSplitUnipotent G_L) : IsSplitUnipotent G := by
  classical
  apply smoothConnectedAffineGroup_lieDimension_induction
    (fun H => IsUnipotent H →
      IsSplitUnipotent ((GroupScheme.baseChange b).obj H) → IsSplitUnipotent H) ?_ G hU hsplit
  intro H _ _ _ ih hHu hHL
  by_cases htriv : SubgroupFunctor.range (𝟙 H) = ⊥
  · exact ⟨0, htriv⟩
  obtain ⟨N, i, hi, hNs, hNa, hNc, hcent, hNsplit, hne⟩ :=
    exists_central_split_subgroup_of_finiteGalois hstable L H hHu hHL htriv
  let : Smooth N.X.hom := hNs
  let : IsAffineHom N.X.hom := hNa
  let : ConnectedSpace N.X.left := hNc
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hnormal : (SubgroupFunctor.range i).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← (commute_of_mem_center (hcent T y) g).eq, mul_inv_cancel_right]
    exact hx
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k H N i hi hnormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : ConnectedSpace Q.X.left := hq.connectedSpace
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  have hlt : Lie.dimension Q < Lie.dimension H :=
    hq.lieDimension_lt_of_nontrivial_connected_kernel ⟨inferInstance, rfl⟩ hNs hne
  let : Smooth ((GroupScheme.baseChange b).obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom b)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  let : Smooth ((GroupScheme.baseChange b).obj Q).X.hom := by
    change Smooth (pullback.snd Q.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  let : Surjective q.hom.hom.left := hq.2.1
  let : Surjective ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.of_isPullback (DominantHomFlat.baseChange_isPullback b q).flip
      inferInstance
  have hQL : IsSplitUnipotent ((GroupScheme.baseChange b).obj Q) :=
    hHL.of_surjective_to_smooth_affine ((GroupScheme.baseChange b).map q)
  obtain ⟨n, hn⟩ := ih Q hlt (hq.isUnipotent hHu) hQL
  obtain ⟨m, hm⟩ := hNsplit
  exact ⟨m + n, hm.of_fppfQuotient_of_field i q hi inferInstance hq hn⟩

/-- An actual finite represented Ga-series obtained by the preceding descent
argument, retaining the one explicit stable-vector premise. -/
def finiteGaloisSplitSeriesOfStableVector
    (hU : IsUnipotent G) (hsplit : IsSplitUnipotent G_L) :
    {n : ℕ // HasSplitSeries n G} :=
  let h := IsSplitUnipotent.of_finiteGalois_of_stableVector hstable L G hU hsplit
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme.RelativeRoot
