import Langlands.GroupScheme.Rational.CyclicWeightSubgroups
import Langlands.GroupScheme.Rational.TorusWeightQuotient
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.TorusActionPoints
import Langlands.GroupScheme.Rational.TorusWeightLie

/-! # The quotient of a cyclic weight subgroup by the next one -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open Corepresented

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (ψ : groupScheme F e ≅ G)
  {I : Type u} [Fintype I] [DecidableEq I]
  (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (b : AutomorphicAction S.toGrp G)

/-- The quotient statement for one representative of a cyclic weight subgroup, given the
identification of the filtration with the weight subgroup functors and the coordinate form of the
action on all test schemes. -/
theorem exists_quotient_of_weightFiltration_eq [IsAffineHom G.X.hom]
    [Algebra.FormallySmooth k B] [Algebra.FiniteType k B] (hS : IsSplitTorus S.toGrp)
    {a : characterLattice S} (ha : characterExponents φ a ≠ 0) {r : ℕ} (hr : 0 < r)
    (hWr : weightFiltration b a r =
      weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) r))
    (hWr1 : weightFiltration b a (r + 1) =
      weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) (r + 1)))
    (hsharp : ∀ (T : Over (Spec (CommRingCat.of k)))
      (s : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (x : T ⟶ (groupScheme F e).X),
      pointsEquiv F e T ((b.transport φ.inv ψ).act s x) =
        (modelAction e ψ φ b).act (splitTorus.pointsEquiv I T s) (pointsEquiv F e T x))
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
    (hj : (weightFiltration b a r).IsRepresentedBy j) :
    ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ V)
      (c : AutomorphicAction S.toGrp V) (d : AutomorphicAction S.toGrp H),
      IsFppfQuotient ((weightFiltration b a (r + 1)).comap j) q ∧
      HasUniqueWeightVectorStructure c (r • a) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        c.act s (h ≫ q.hom.hom) = d.act s h ≫ q.hom.hom) := by
  set a' := characterExponents φ a with ha'
  set σ := modelAction e ψ φ b
  set P := Corepresented.cyclicTail a' r
  set hJ := isCutOutBy_weightIdeal e σ P
  have hrepU : (weightFiltration b a r).IsRepresentedBy (cutHom hJ ≫ ψ.hom) := by
    rw [hWr]
    exact (isRepresentedBy_cutHom hJ).comp_iso ψ
  let θ := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj hrepU
  have hθ : θ.hom ≫ (cutHom hJ ≫ ψ.hom) = j :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hj hrepU
  obtain ⟨N, y, hy, hyh, hq⟩ := exists_isFppfQuotient_cyclicTail e σ ha hr
  -- The next cyclic weight subgroup, inside the cut group.
  let M : SubgroupFunctor (cutGroupScheme hJ) :=
    (weightFiltration b a (r + 1)).comap (cutHom hJ ≫ ψ.hom)
  have hcut : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (cutGroupScheme hJ).X),
      pointsEquiv F e T (x ≫ (cutHom hJ).hom.hom) =
        (pointsEquiv (cutFunctor hJ) (weightCorep e σ P) T x).1 := by
    intro T x
    rw [cutHom, groupSchemeMap_points]
    rfl
  have hM : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (cutGroupScheme hJ).X),
      x ∈ M.carrier T ↔ (pointsEquiv (cutFunctor hJ) (weightCorep e σ P) T x).1 ∈
        weightSubgroup e σ (Corepresented.cyclicTail a' (r + 1)) _ := by
    intro T x
    rw [SubgroupFunctor.mem_comap, hWr1, mem_weightSubgroupFunctor, ← hcut]
    have h : (x ≫ (cutHom hJ ≫ ψ.hom).hom.hom) ≫ ψ.inv.hom.hom = x ≫ (cutHom hJ).hom.hom := by
      rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, iso_hom_inv_hom, Category.comp_id]
    rw [h]
  have hfq := hq M hM
  have hstab : b.IsStable (weightFiltration b a r) := by
    rw [hWr]
    exact isStable_weightSubgroupFunctor e ψ φ b _
  have hra : r • a ≠ 0 := by
    intro h
    apply nsmul_ne_zero_of_pos ha hr
    rw [ha', ← map_nsmul, h, map_zero]
  refine ⟨VectorGroup.groupScheme (CommRingCat.of k) N, θ.hom ≫ VectorGroup.quotientMap hy,
    VectorGroup.weightAction (r • a), AutomorphicAction.onRepresentedSubgroup b j hj hstab,
    ?_, VectorGroup.hasUniqueWeightVectorStructure_weightAction (r • a) hS hra,
    fun T s h => AutomorphicAction.onRepresentedSubgroup_act_comp b j hj hstab s h, ?_⟩
  · have h := hfq.comapIso θ.symm
    rwa [Iso.symm_inv, ← SubgroupFunctor.comap_comp, hθ] at h
  · intro T s h
    apply VectorGroup.points_ext
    intro i
    set d := AutomorphicAction.onRepresentedSubgroup b j hj hstab
    have hcomp : ∀ w : T ⟶ H.X, w ≫ (θ.hom ≫ VectorGroup.quotientMap hy).hom.hom =
        (w ≫ θ.hom.hom.hom) ≫ (VectorGroup.quotientMap hy).hom.hom := by
      intro w
      rw [Grp.comp_hom_hom, Category.assoc]
    rw [VectorGroup.coordinates_weightAction_act, Pi.smul_apply, smul_eq_mul, hcomp, hcomp,
      VectorGroup.coordinates_quotientMap, VectorGroup.coordinates_quotientMap]
    -- The point of the model below `d.act s h`.
    have hmodel : (d.act s h ≫ θ.hom.hom.hom) ≫ (cutHom hJ).hom.hom =
        (b.transport φ.inv ψ).act (s ≫ φ.hom.hom.hom)
          ((h ≫ θ.hom.hom.hom) ≫ (cutHom hJ).hom.hom) := by
      have hiso : Mono ψ.hom.hom.hom := by
        have : IsIso ψ.hom.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso ψ).hom)
        infer_instance
      apply (cancel_mono ψ.hom.hom.hom).1
      have hj' : j.hom.hom = θ.hom.hom.hom ≫ (cutHom hJ).hom.hom ≫ ψ.hom.hom.hom := by
        rw [← hθ, Grp.comp_hom_hom, Grp.comp_hom_hom]
      rw [AutomorphicAction.transport_act]
      simp only [Category.assoc, iso_inv_hom_hom, iso_hom_inv_hom, Category.comp_id]
      rw [← hj']
      exact AutomorphicAction.onRepresentedSubgroup_act_comp b j hj hstab s h
    obtain ⟨f, hf⟩ := exists_eq_mk_comp e σ P (hyh i)
    rw [← hf, coord_cut_mk, coord_cut_mk, ← hcut, ← hcut, hmodel, hsharp]
    have hact := coord_act_of_isHomogeneous e σ (A := ((algΓ (CommRingCat.of k)).obj T).unop)
      (splitTorus.pointsEquiv I T (s ≫ φ.hom.hom.hom))
      (pointsEquiv F e T ((h ≫ θ.hom.hom.hom) ≫ (cutHom hJ).hom.hom))
      (isHomogeneous_comp e σ (r • a') f)
    rw [hact]
    have hcv : VectorGroup.charValue (r • a) T s =
        ((splitTorus.exponentValue I (splitTorus.pointsEquiv I T (s ≫ φ.hom.hom.hom))
          (Multiplicative.ofAdd (r • a')) : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) := by
      rw [VectorGroup.charValue, pointsEquiv_characterExponents φ (r • a), map_nsmul]
      rfl
    rw [hcv]
    exact mul_comm _ _

omit [Fintype I] [DecidableEq I] in
theorem cyclicTail_subset_of_le {a : I → ℤ} {r r' : ℕ} (h : r' ≤ r) :
    (Corepresented.cyclicTail a r : Set (I → ℤ)) ⊆ Corepresented.cyclicTail a r' := by
  rintro _ ⟨n, hn, hn0, rfl⟩
  exact ⟨n, h.trans hn, hn0, rfl⟩

omit [Fintype I] [DecidableEq I] in
theorem cyclicTail_add_mem {a : I → ℤ} {r r' : ℕ} :
    ∀ m ∈ Corepresented.cyclicTail a r', ∀ p ∈ Corepresented.cyclicTail a r,
      m + p ∈ Corepresented.cyclicTail a r := by
  rintro _ ⟨n, -, hn0, rfl⟩ _ ⟨n', hn', -, rfl⟩
  exact ⟨n + n', by omega, by omega, add_nsmul a n n'⟩

include ψ φ in
/-- The cyclic filtration statement for one group with a corepresented model of finite type and
formally smooth over `k`. -/
theorem cyclicWeightFiltration_of_model [IsAffineHom G.X.hom]
    [IsAffineHom (groupScheme F e).X.hom] [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0) (r : ℕ) (hr : 0 < r) :
    (weightFiltration b a r).IsNormalizedBy (weightFiltration b a 1) ∧
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        (weightFiltration b a r).IsRepresentedBy j →
        ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ V)
          (c : AutomorphicAction S.toGrp V) (d : AutomorphicAction S.toGrp H),
          IsFppfQuotient ((weightFiltration b a (r + 1)).comap j) q ∧
          HasUniqueWeightVectorStructure c (r • a) ∧
          (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
            d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) ∧
          (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
            c.act s (h ≫ q.hom.hom) = d.act s h ≫ q.hom.hom) := by
  have ha' : characterExponents φ a ≠ 0 := by
    intro h
    exact ha ((characterExponents φ).injective (h.trans (map_zero _).symm))
  have hW : ∀ n : ℕ, weightFiltration b a n =
      weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) n) := by
    intro n
    refine weightFiltration_eq_weightSubgroupFunctor e ψ φ b ha' n ?_ ?_
    · intro χ hχ
      exact (mem_cyclicTail_characterExponents φ a n χ).1
        (actionWeightSupport_comap_weightSubgroup_subset e ψ φ b _ hχ)
    · intro F' hF' J hJ hH
      refine tangentRigid_of_actionWeightSupport_subset e ψ φ b _ (fun χ hχ => ?_) hJ hH
      exact (mem_cyclicTail_characterExponents φ a n χ).2 (hF'.2.2 hχ)
  refine ⟨?_, fun H j hj =>
    exists_quotient_of_weightFiltration_eq e ψ φ b hS ha' hr (hW r) (hW (r + 1))
      (fun T s x => pointsEquiv_act e (b.transport φ.inv ψ) T s x) H j hj⟩
  rw [hW r, hW 1]
  exact weightSubgroupFunctor_isNormalizedBy e ψ φ b (cyclicTail_subset_of_le hr)
    cyclicTail_add_mem

end Langlands.GroupScheme.RelativeRoot
