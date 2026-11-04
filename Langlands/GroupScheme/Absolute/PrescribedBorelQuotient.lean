import Langlands.GroupScheme.Absolute.BorelProperQuotientReduction
import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.HomogeneousQuotientProof

/-! # Proper homogeneous quotients for a prescribed Borel -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- The orbit-stabilizer proof of properness applies to the prescribed Borel,
without replacing it by a conjugate or another Borel. -/
theorem IsBorelSubgroup.quotient_isProper_of_prerequisites
    (hFlag : GeneralLinearSolvableStabilizerStatement.{u})
    (hOrbit : ClosedOrbitStatement.{u})
    (hFix : SolvableProperFixedPointStatement.{u})
    (hB : IsBorelSubgroup i)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
    (hQs : IsSeparated Q.hom) (hQl : LocallyOfFiniteType Q.hom)
    (hQq : QuasiCompact Q.hom) (hqs : Smooth q.left)
    (hqsurj : Surjective q.left) (hqq : QuasiCompact q.left)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsProper Q.hom := by
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

/-- With the proved flag-stabilizer and closed-orbit theorems, only the
solvable proper fixed-point statement remains as a structural input. -/
theorem IsBorelSubgroup.quotient_isProper_of_solvableProperFixedPoint
    (hFix : SolvableProperFixedPointStatement.{u}) (hB : IsBorelSubgroup i)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
    (hQs : IsSeparated Q.hom) (hQl : LocallyOfFiniteType Q.hom)
    (hQq : QuasiCompact Q.hom) (hqs : Smooth q.left)
    (hqsurj : Surjective q.left) (hqq : QuasiCompact q.left)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsProper Q.hom :=
  IsBorelSubgroup.quotient_isProper_of_prerequisites
    generalLinearSolvableStabilizer closedOrbit hFix hB Q q
    hQs hQl hQq hqs hqsurj hqq hq

/-- The actual smooth homogeneous quotient of a prescribed Borel is proper,
conditional only on the solvable proper fixed-point statement. -/
theorem IsBorelSubgroup.exists_properQuotient_of_solvableProperFixedPoint
    (hFix : SolvableProperFixedPointStatement.{u}) (hB : IsBorelSubgroup i) :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsProper Q.hom ∧ Smooth q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  obtain ⟨Q, q, hQs, hQl, hQq, hqs, hqsurj, hqq, hq⟩ :=
    smoothSubgroupQuotientExistence k G B i hB.isClosedSubgroup hB.smooth
  exact ⟨Q, q, IsBorelSubgroup.quotient_isProper_of_solvableProperFixedPoint
    hFix hB Q q hQs hQl hQq hqs hqsurj hqq hq, hqs, hqsurj, hqq, hq⟩

/-- An actual proper quotient for the specified subgroup embedding, retaining
the projection and its exact coset fibers on every relative scheme test. -/
structure IsBorelSubgroup.ProperQuotientData (i : B ⟶ G) where
  quotient : Over (Spec (CommRingCat.of k))
  projection : G.X ⟶ quotient
  proper : IsProper quotient.hom
  smooth : Smooth projection.left
  surjective : Surjective projection.left
  quasiCompact : QuasiCompact projection.left
  fibers : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    g ≫ projection = h ≫ projection ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

/-- Choose an actual proper quotient for this Borel embedding using the
solvable proper fixed-point statement and the proved quotient construction. -/
noncomputable def IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint
    (hFix : SolvableProperFixedPointStatement.{u}) (hB : IsBorelSubgroup i) :
    IsBorelSubgroup.ProperQuotientData i :=
  Classical.choice <| by
    obtain ⟨Q, q, hQ, hqs, hqsurj, hqq, hq⟩ :=
      hB.exists_properQuotient_of_solvableProperFixedPoint hFix
    exact ⟨{
      quotient := Q
      projection := q
      proper := hQ
      smooth := hqs
      surjective := hqsurj
      quasiCompact := hqq
      fibers := hq
    }⟩

end Langlands.GroupScheme
