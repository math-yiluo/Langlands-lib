import Langlands.GroupScheme.Rational.SemigroupProductRestriction
import Langlands.GroupScheme.Rational.CentralProductKernel
import Langlands.GroupScheme.Rational.SemigroupComparisonStatement
import Langlands.GroupScheme.Rational.SmoothTangentWeights
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction

/-! # Exact semigroup products in central extensions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {k : Type u} [Field k]
    {G Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Z.X.hom] [IsAffineHom Q.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The canonical family of factor kernels in a represented central subgroup. -/
def centralSemigroupKernelFamily
    (z : Z ⟶ G) (q : G ⟶ Q)
    (hz : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy z)
    {n : ℕ} {H R : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G) (lQ : ∀ r, R r ⟶ Q) (p : ∀ r, H r ⟶ R r)
    (hp : ∀ r, j r ≫ q = p r ≫ lQ r) :
    ∀ r, kernel (p r) ⟶ Z :=
  fun r => factorKernelHom q z hz (j r) (lQ r) (p r) (hp r)

/-- The exact product property passes from an actual central subgroup and its
smooth fppf quotient to the ambient action, under the stated semigroup inputs. -/
theorem hasOrderedSemigroupProducts_of_centralExtension
    (hReal : SemigroupRealizationStatement.{u})
    (hSmoothQuotient : SemigroupSmoothQuotientStatement.{u})
    (hIntersection : SemigroupIntersectionStatement.{u})
    (hG : Smooth G.X.hom) (hZ : Smooth Z.X.hom) (hQ : Smooth Q.X.hom)
    (hZconn : ConnectedSpace Z.X.left)
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (bZ : AutomorphicAction S.toGrp Z)
    (bQ : AutomorphicAction S.toGrp Q) (z : Z ⟶ G) (q : G ⟶ Q)
    (hzClosed : IsClosedSubgroup z) (hzCentral : IsCentral z)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) q)
    (hqSmooth : Smooth q.hom.hom.left)
    (hzEq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ Z.X),
      bZ.act s v ≫ z.hom.hom = b.act s (v ≫ z.hom.hom))
    (hqEq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
      b.act s g ≫ q.hom.hom = bQ.act s (g ≫ q.hom.hom))
    (hZprod : HasOrderedSemigroupProducts bZ) (hQprod : HasOrderedSemigroupProducts bQ) :
    HasOrderedSemigroupProducts b := by
  classical
  let _ := hG
  let _ := hQ
  have hzMono : Mono z.hom.hom := by
    let _ := hzClosed.mono
    exact Over.mono_of_mono_left _
  have hzrep : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨hzMono, rfl⟩
  have hzker : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy z := by
    rw [hq.2.2.2]
    exact hzrep
  have hZsupport : actionWeightSupport bZ ⊤ ⊆ actionWeightSupport b ⊤ := by
    rw [← actionWeightSupport_map z hzMono bZ b hzEq ⊤]
    exact actionWeightSupport_subset_top b _
  have hQsupport : actionWeightSupport bQ ⊤ ⊆ actionWeightSupport b ⊤ := by
    intro χ hχ
    by_contra hn
    have hbot := actionWeightSpace_eq_bot_of_smooth b bQ hS q hqEq hqSmooth χ
      (actionWeightSpace_eq_bot_of_not_mem_support b hn)
    exact (mem_actionWeightSupport_top_iff bQ χ).mp hχ hbot
  have hnormal : (SubgroupFunctor.range z).IsNormal := hzCentral.range_isNormal
  intro n Ψ hcover hdis hcross
  let A : Fin n → AddSubsemigroup (characterLattice S) :=
    fun r => AddSubsemigroup.closure (Ψ r)
  obtain ⟨R, lQ, hR, hRprod⟩ := hQprod.for_larger_support
    (actionWeightSupport b ⊤) hQsupport n Ψ hcover hdis hcross
  obtain ⟨V, lZ, hV, hVprod⟩ := hZprod.for_larger_support
    (actionWeightSupport b ⊤) hZsupport n Ψ hcover hdis hcross
  have hchoose : ∀ r : Fin n,
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        (semigroupSubgroup b (A r)).IsRepresentedBy j ∧
          IsClosedSubgroup j ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left :=
    fun r => (hReal k G hG inferInstance S hS b (A r)).1
  choose H j hj hjClosed hH hHconn using hchoose
  have hquot : ∀ r : Fin n, ∃ p : H r ⟶ R r,
      j r ≫ q = p ≫ lQ r ∧ Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left := by
    intro r
    exact hSmoothQuotient k G Q hG hQ inferInstance inferInstance S hS b bQ q
      hqSmooth hq.2.1 hqEq (A r) (H r) (R r) (j r) (lQ r) (hj r) (hR r).1
  choose p hp hpSmooth hpSurj using hquot
  let l : ∀ r, kernel (p r) ⟶ Z :=
    centralSemigroupKernelFamily z q hzker j lQ p hp
  have hlrep : ∀ r, (semigroupSubgroup bZ (A r)).IsRepresentedBy (l r) := by
    intro r
    let _ : Mono (lQ r).hom.hom := (hR r).1.1
    have hinter := hIntersection k G Z hG hZ inferInstance inferInstance hZconn
      S hS b bZ z hzClosed hzEq (A r) (Or.inr (Or.inr hnormal))
    rw [← hinter]
    exact factorKernelHom_isRepresentedBy q z hzker (j r) (lQ r) (p r) (hp r) (hj r)
  have hlprod : IsIso (orderedMultiplication l) :=
    isIso_orderedMultiplication_of_same_representatives
      (fun r => semigroupSubgroup bZ (A r)) lZ l (fun r => (hV r).1) hlrep hVprod
  let e : Z ≅ kernel q := hq.kernelIso hzrep
  let lK : ∀ r, kernel (p r) ⟶ kernel q := fun r => l r ≫ e.hom
  have hlK : ∀ r, lK r ≫ kernelι q = kernelι (p r) ≫ j r := by
    intro r
    dsimp only [lK]
    rw [Category.assoc, IsFppfQuotient.kernelIso_hom_comp]
    exact factorKernelHom_comp q z hzker (j r) (lQ r) (p r) (hp r)
  have hlKprod : IsIso (orderedMultiplication lK) := by
    change IsIso (orderedMultiplication (fun r => l r ≫ e.hom))
    rw [← orderedMultiplication_comp]
    let _ := hlprod
    let _ : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
    infer_instance
  have hcentral : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ≫ q.hom.hom = 1 → ∀ g : T ⟶ G.X, Commute x g := by
    intro T x hx g
    have hxN : x ∈ (SubgroupFunctor.range z).carrier T := by
      rw [← hq.2.2.2]
      exact (mem_range_kernelι_iff q x).mpr hx
    obtain ⟨v, hv⟩ := hxN
    change v ≫ z.hom.hom = x at hv
    rw [← hv]
    exact commute_of_mem_center (hzCentral T v) g
  let _ := hRprod
  let _ := hlKprod
  refine ⟨H, j, fun r => ⟨hj r, hjClosed r, hH r, hHconn r⟩, ?_⟩
  exact isIso_orderedMultiplication_of_centralExtension j lQ q p hp lK hlK
    (fun r => by let _ := hpSmooth r; infer_instance) hpSurj
    (fun r => by let _ := hpSmooth r; infer_instance) hcentral

end Langlands.GroupScheme.RelativeRoot
