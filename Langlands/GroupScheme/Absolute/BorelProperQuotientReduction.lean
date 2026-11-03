import Langlands.GroupScheme.ClosedOrbitStatement
import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerStatement
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.Absolute.BorelProperQuotientStatement
import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.SolvableProperFixedPointStatement
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Reduction of proper Borel quotients to orbit, stabilizer and flag prerequisites -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S}

/-- Two translates of a point agree exactly when the quotient of the acting points fixes it. -/
theorem act_eq_act_iff (a : SchemeAction G X) {T : Over S} (g h : T ⟶ G.X) (x : T ⟶ X) :
    a.act g x = a.act h x ↔ a.act (g⁻¹ * h) x = x := by
  constructor
  · intro e
    rw [a.act_mul, ← e, ← a.act_mul, inv_mul_cancel, a.act_one]
  · intro e
    rw [← mul_inv_cancel_left g h, a.act_mul, e]

end SchemeAction

/-- Some Borel subgroup has proper homogeneous quotients, assuming the closed-orbit, flag and
fixed-point propositions. -/
theorem someBorelQuotientProper_of_prerequisites
    (hFlag : GeneralLinearSolvableStabilizerStatement.{u})
    (hOrbit : ClosedOrbitStatement.{u})
    (hFix : SolvableProperFixedPointStatement.{u}) :
    SomeBorelQuotientProperStatement.{u} := by
  intro k _ _ G _ _ _
  obtain ⟨B, i, hB⟩ := BorelExistence.exists_isBorelSubgroup G
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨X, a, hXp, hXne, hsolv⟩ := hFlag k N
  have := hXp
  obtain ⟨O, j, b, x₀, hOred, hj, -, -, hjb, htrans⟩ := hOrbit k G X hXne (a.restrict ρ)
  have := hOred
  have := hj
  have hOp : IsProper O.hom := by
    rw [← Over.w j]
    infer_instance
  have := hOp
  -- The Borel subgroup fixes a rational point of the proper orbit.
  have : Smooth B.X.hom := hB.smooth
  have : IsClosedImmersion i.hom.hom.left := hB.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hOne : Nonempty O.left := ⟨x₀.left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))⟩
  obtain ⟨y, hy⟩ :=
    hFix k B hB.connectedSpace hB.isSolvableGroupScheme O hOp hOne (b.restrict i)
  obtain ⟨S, iS, hiS, hS⟩ := b.exists_isClosedSubgroup_stabilizer y
  have hBS : SubgroupFunctor.range i ≤ SubgroupFunctor.range iS := by
    rw [SubgroupFunctor.le_def]
    intro T g hg
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    rw [hS]
    have := hy T (toUnit T) h
    rwa [SchemeAction.restrict_act] at this
  obtain ⟨H, f, hHc, hHs, hHconn, hfopen, hmax⟩ :=
    ReducedSubgroup.exists_reducedIdentityComponent iS hiS
  obtain ⟨e, he⟩ := hmax B i hB.isClosedSubgroup hB.smooth hB.connectedSpace hBS
  -- The reduced identity component of the stabilizer is solvable.
  have hHsolv : IsSolvableGroupScheme H := by
    refine hsolv (y ≫ j) H (f ≫ iS ≫ ρ) ?_ ?_
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
      calc (a.restrict (f ≫ iS ≫ ρ)).act h (toUnit T ≫ y ≫ j)
          = (a.restrict ρ).act (h ≫ (f ≫ iS).hom.hom) ((toUnit T ≫ y) ≫ j) := by
            simp only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
        _ = b.act (h ≫ (f ≫ iS).hom.hom) (toUnit T ≫ y) ≫ j := (hjb _ _ _).symm
        _ = toUnit T ≫ y ≫ j := by rw [hmem, Category.assoc]
  have : IsIso e := hB.maximal H (f ≫ iS) e hHc hHs hHconn hHsolv he
  have hrange : SubgroupFunctor.range i = SubgroupFunctor.range (f ≫ iS) := by
    ext T g
    constructor
    · intro hg
      obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
      exact SubgroupFunctor.mem_range.mpr ⟨h ≫ e.hom.hom, by rw [← he]; simp⟩
    · intro hg
      obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
      refine SubgroupFunctor.mem_range.mpr ⟨h ≫ (inv e).hom.hom, ?_⟩
      rw [← he]
      simp only [Grp.comp_hom_hom, Category.assoc]
      rw [← Grp.comp_hom_hom_assoc, IsIso.inv_hom_id, Grp.id_hom_hom, Category.id_comp]
  -- The orbit map through the fixed point.
  have htrans' : ∀ z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, b.act g y = z := by
    intro z
    obtain ⟨g₀, hg₀⟩ := htrans y
    obtain ⟨g₁, hg₁⟩ := htrans z
    refine ⟨g₁ * g₀⁻¹, ?_⟩
    rw [← hg₀, ← hg₁, ← b.act_mul, inv_mul_cancel_right]
  obtain ⟨hπf, hπs, hπq⟩ := orbitMapFaithfullyFlat k G O b y htrans'
  refine ⟨B, i, hB, fun Q q hQs hQl hQq hqs hqsurj hqq hq => ?_⟩
  refine finiteIndexQuotientProperTransfer k G S iS hiS H (f ≫ iS) f hHc rfl hfopen O _ hOp hπf hπs hπq ?_
    Q q hQs hQl hQq hqs hqsurj hqq ?_
  · intro T g h
    have hg : g ≫ toUnit G.X = toUnit T := toUnit_unique _ _
    have hh : h ≫ toUnit G.X = toUnit T := toUnit_unique _ _
    rw [b.naturality, b.naturality, Category.comp_id, Category.comp_id,
      ← Category.assoc, ← Category.assoc, hg, hh, hS]
    exact b.act_eq_act_iff g h _
  · intro T g h
    rw [hq, hrange]

end Langlands.GroupScheme
