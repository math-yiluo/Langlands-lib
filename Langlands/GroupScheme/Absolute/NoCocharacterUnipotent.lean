import Langlands.GroupScheme.Absolute.CharacterCocharacter
import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof
import Langlands.GroupScheme.Absolute.BorelProperQuotientReduction
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.Unipotent.ProperHomogeneousQuotient
import Langlands.GroupScheme.Torus.AlgClosedTrivialMaximalUnipotentStatement
import Langlands.GroupScheme.Torus.NoClosedTorus
import Langlands.GroupScheme.Torus.ImageProof

/-! # Connected groups without cocharacters over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AbsoluteNoCocharacter

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A smooth connected affine group over an algebraically closed field is
unipotent when every actual cocharacter is zero. -/
theorem isUnipotent
    (hG : ∀ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, z = 0) :
    IsUnipotent G := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨X, a, hXp, hXne, hsolv⟩ := generalLinearSolvableStabilizer k N
  have := hXp
  obtain ⟨O, j, b, x, hOred, hj, _, _, hjb, htrans⟩ :=
    closedOrbit k G X hXne (a.restrict ρ)
  have := hOred
  have := hj
  have hOp : IsProper O.hom := by
    rw [← Over.w j]
    infer_instance
  have := hOp
  obtain ⟨S, iS, hiS, hS⟩ := b.exists_isClosedSubgroup_stabilizer x
  obtain ⟨H, f, hHc, hHs, hHconn, hfopen, _⟩ :=
    ReducedSubgroup.exists_reducedIdentityComponent iS hiS
  have := hHs
  have := hHconn
  have : IsClosedImmersion (f ≫ iS).hom.hom.left := hHc
  have : IsAffineHom H.X.hom := by
    rw [← Over.w (f ≫ iS).hom.hom]
    infer_instance
  have hHsolv : IsSolvableGroupScheme H := by
    refine hsolv (x ≫ j) H (f ≫ iS ≫ ρ) ?_ ?_
    · have h₁ : IsClosedImmersion (f ≫ iS).hom.hom.left := hHc
      have h₂ : IsClosedImmersion ρ.hom.hom.left := hρ
      show IsClosedImmersion (f ≫ iS ≫ ρ).hom.hom.left
      simp only [Grp.comp_hom_hom, Over.comp_left] at h₁ h₂ ⊢
      rw [← Category.assoc]
      infer_instance
    · intro T c h
      have hc : c = toUnit T := toUnit_unique _ _
      subst hc
      have hmem : h ≫ (f ≫ iS).hom.hom ∈ (SubgroupFunctor.range iS).carrier T :=
        SubgroupFunctor.mem_range.mpr ⟨h ≫ f.hom.hom, by simp⟩
      rw [hS] at hmem
      calc (a.restrict (f ≫ iS ≫ ρ)).act h (toUnit T ≫ x ≫ j)
          = (a.restrict ρ).act (h ≫ (f ≫ iS).hom.hom) ((toUnit T ≫ x) ≫ j) := by
            simp only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
        _ = b.act (h ≫ (f ≫ iS).hom.hom) (toUnit T ≫ x) ≫ j := (hjb _ _ _).symm
        _ = toUnit T ≫ x ≫ j := by rw [hmem, Category.assoc]
  have hHu : IsUnipotent H := by
    apply isUnipotent_of_gm_hom_eq_zero hHsolv
    intro z
    have : Mono (f ≫ iS).hom.hom := Over.mono_of_mono_left _
    have : Mono (f ≫ iS) :=
      (Grp.forget _).mono_of_mono_map (f := f ≫ iS) ‹Mono (f ≫ iS).hom.hom›
    apply (cancel_mono (f ≫ iS)).mp
    rw [hG (z ≫ (f ≫ iS)), zero_comp]
  obtain ⟨Q, q, hQs, hQl, hQq, hqs, hqsurj, hqq, hq⟩ :=
    smoothSubgroupQuotientExistence k G H (f ≫ iS) hHc hHs
  obtain ⟨hπf, hπs, hπq⟩ := orbitMapFaithfullyFlat k G O b x htrans
  have hQp : IsProper Q.hom := by
    refine finiteIndexQuotientProperTransfer k G S iS hiS H (f ≫ iS) f hHc rfl hfopen
      O _ hOp hπf hπs hπq ?_ Q q hQs hQl hQq hqs hqsurj hqq hq
    intro T g h
    have hg : g ≫ toUnit G.X = toUnit T := toUnit_unique _ _
    have hh : h ≫ toUnit G.X = toUnit T := toUnit_unique _ _
    rw [b.naturality, b.naturality, Category.comp_id, Category.comp_id,
      ← Category.assoc, ← Category.assoc, hg, hh, hS]
    exact b.act_eq_act_iff g h _
  have := hQp
  have := hqs
  have := hqsurj
  have := hqq
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  have : IsIso (f ≫ iS) :=
    isIso_of_unipotent_of_proper_homogeneousQuotient (f ≫ iS) hHc hHu q
      (fun T g h he => (hq T g h).mp he)
  exact IsUnipotent.of_iso (asIso (f ≫ iS)).symm hHu

end AbsoluteNoCocharacter

/-- The algebraically closed no-cocharacter criterion without a solvability premise. -/
def AlgClosedNoCocharacterUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, z = 0) → IsUnipotent G

/-- A closed flag orbit supplies a solvable stabilizer and a proper quotient. -/
theorem algClosedNoCocharacterUnipotent : AlgClosedNoCocharacterUnipotentStatement.{u} := by
  intro k _ _ G _ _ _ hG
  exact AbsoluteNoCocharacter.isUnipotent hG

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A trivial maximal torus rules out every nontrivial closed torus. -/
theorem IsMaximalTorus.hasNoNontrivialClosedTorus_of_range_eq_bot
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hzero : SubgroupFunctor.range i = ⊥) :
    HasNoNontrivialClosedTorus G := by
  have hi0 : i = 0 := SubgroupFunctor.eq_zero_of_range_eq_bot hzero
  intro T' hT' j hj
  have : IsIso (0 : T.toGrp ⟶ T'.toGrp) := hi.2.2 T' j 0 hT' hj (by simp [hi0])
  have hj0 : j = 0 := by
    apply (cancel_epi (0 : T.toGrp ⟶ T'.toGrp)).mp
    simp
  rw [hj0, SubgroupFunctor.range_zero]

/-- A smooth connected affine group over an algebraically closed field is
unipotent if it contains no nontrivial closed torus. -/
theorem HasNoNontrivialClosedTorus.isUnipotent [IsAlgClosed k]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasNoNontrivialClosedTorus G) : IsUnipotent G := by
  apply AbsoluteNoCocharacter.isUnipotent
  intro z
  obtain ⟨T, j, p, hT, hj, hfac⟩ := torusImageClosedTorusStatement k G
    (Gm (Spec (CommRingCat.of k))).toGrp isSplitTorus_gm.isTorus z
  have hj0 : j = 0 := SubgroupFunctor.eq_zero_of_range_eq_bot (hG T hT j hj)
  rw [← hfac, hj0, comp_zero]

/-- The exact published trivial-maximal-torus proposition over algebraically closed fields. -/
theorem algClosedTrivialMaximalTorusUnipotent :
    AlgClosedTrivialMaximalTorusUnipotentStatement.{u} := by
  intro k _ _ G _ _ _ T i hi hzero
  exact (hi.hasNoNontrivialClosedTorus_of_range_eq_bot hzero).isUnipotent

end Langlands.GroupScheme
