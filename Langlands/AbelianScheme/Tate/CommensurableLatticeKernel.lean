import Langlands.AbelianScheme.Tate.CommensurableLatticeScaling
import Langlands.AbelianScheme.Tate.TorsionSubgroupQuotient

/-! # Actual torsion-kernel subgroup attached to a commensurable lattice -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The normalized torsion subgroup on actual points of the multiplication kernel. -/
def normalizedKernelSubgroup (n : Index (fun _ => True))
    (L : AddSubgroup (RationalFull G T)) :
    AddSubgroup (Additive (T ⟶ (kernel (multiplication G ((n.val * n.val : ℕ) : ℤ))).X)) :=
  (normalizedLevelSubgroup G T n L).comap
    (kernelLevelEquiv G T (n.val * n.val)).toAddMonoidHom

@[simp]
theorem mem_normalizedKernelSubgroup (n : Index (fun _ => True))
    (L : AddSubgroup (RationalFull G T))
    (x : Additive (T ⟶ (kernel (multiplication G ((n.val * n.val : ℕ) : ℤ))).X)) :
    x ∈ normalizedKernelSubgroup G T n L ↔
      kernelLevelEquiv G T (n.val * n.val) x ∈ normalizedLevelSubgroup G T n L :=
  Iff.rfl

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale GroupScheme.Tate

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- Invariance on the rational lattice gives invariance on actual torsion-kernel points. -/
theorem normalizedKernelSubgroup_monodromy
    (n : Index (fun _ => True)) (L : AddSubgroup (RationalFull A (Over.mk s)))
    (hL : ∀ (g : FundamentalGroup s hs) (w : RationalFull A (Over.mk s)),
      rationalMonodromy s hs htor A (fun _ => True) hu g w ∈ L ↔ w ∈ L) :
    letI := torsionKernel_isFinite htor A (n.val * n.val)
      (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n))
    letI := torsionKernel_etale htor A (n.val * n.val)
      (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n))
    ∀ (g : FundamentalGroup s hs)
      (x : Additive (Over.mk s ⟶ (GroupScheme.kernel
        (GroupScheme.multiplication A.toGrp ((n.val * n.val : ℕ) : ℤ))).X)),
      groupMonodromy s hs (GroupScheme.kernel
        (GroupScheme.multiplication A.toGrp ((n.val * n.val : ℕ) : ℤ))) g x ∈
          normalizedKernelSubgroup A.toGrp (Over.mk s) n L ↔
        x ∈ normalizedKernelSubgroup A.toGrp (Over.mk s) n L := by
  dsimp only
  intro g x
  change kernelLevelEquiv A (Over.mk s) (n.val * n.val)
    (Additive.ofMul (g.hom.app (torsionCover htor A (n.val * n.val)
      (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n))) x.toMul)) ∈
        normalizedLevelSubgroup A.toGrp (Over.mk s) n L ↔ _
  rw [← levelMonodromy_kernel]
  exact normalizedLevelSubgroup_monodromy s hs htor A hu n L hL g _

/-- A supplied realization of the normalized torsion-kernel subgroup gives an
actual abelian scheme with exactly the prescribed rational full integral image. -/
theorem exists_realization_of_normalizedKernelSubgroup
    [IsLocallyNoetherian S]
    (hfib : ∀ (F : Finset A.X.left) (t : S), (∀ x ∈ F, A.X.hom x = t) →
      ∃ W : A.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W)
    (n : Index (fun _ => True)) (L : AddSubgroup (RationalFull A (Over.mk s)))
    (hlower : ∀ x : Full A (Over.mk s),
      n.val • GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x ∈ L)
    (hupper : ∀ w ∈ L, ∃ x : Full A (Over.mk s),
      GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x = n.val • w)
    (H : CommGroupScheme S) [IsFinite H.X.hom] [Etale H.X.hom]
    (i : H.toGrp ⟶ GroupScheme.kernel
      (GroupScheme.multiplication A.toGrp ((n.val * n.val : ℕ) : ℤ)))
    [IsClosedImmersion i.hom.hom.left]
    (hM : ∀ x : Additive (Over.mk s ⟶ (GroupScheme.kernel
        (GroupScheme.multiplication A.toGrp ((n.val * n.val : ℕ) : ℤ))).X),
      x ∈ normalizedKernelSubgroup A.toGrp (Over.mk s) n L ↔
        ∃ y : Additive (Over.mk s ⟶ H.X), Additive.ofMul (y.toMul ≫ i.hom.hom) = x) :
    ∃ (B : AbelianScheme S) (e : Rationalization.of B ≅ Rationalization.of A),
      ∀ w : RationalFull A (Over.mk s),
        w ∈ L ↔ ∃ x : Full B (Over.mk s),
          rationalHomMap (Over.mk s) (fun _ => True) e.hom
            (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) = w := by
  let K := FiniteEtaleSubgroup.ofTorsionSubgroup A (n.val * n.val) H i
  have hK : K.inclusion ≫ commHom ((n.val * n.val) • 𝟙 A) = 0 :=
    FiniteEtaleSubgroup.ofTorsionSubgroup_annihilated A (n.val * n.val) H i
  obtain ⟨D⟩ :=
    FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre A hfib K
  let r := D.inverseMultiple (n.val * n.val) hK
  have hqr : D.q ≫ r = (n.val * n.val) • 𝟙 A := D.q_inverseMultiple _ hK
  have hrq : r ≫ D.q = (n.val * n.val) • 𝟙 D.B := D.inverseMultiple_q _ hK
  have himage (x : Full A (Over.mk s)) :
      (∃ y : Full D.B (Over.mk s), map (Over.mk s) (fun _ => True) r y = x) ↔
        x ∈ normalizedIntegralSubgroup A.toGrp (Over.mk s) n.val L := by
    refine (D.exists_map_inverseMultiple_iff_exists_inclusion
      (Over.mk s) (fullSquareIndex n) hK x).trans ?_
    let e := GroupScheme.Tate.kernelLevelEquiv A.toGrp (Over.mk s) (n.val * n.val)
    let v := GroupScheme.Tate.evaluation A.toGrp (Over.mk s) (fun _ => True) (fullSquareIndex n) x
    have heq :
        (∃ y : Additive (Over.mk s ⟶ K.G.X),
          Additive.ofMul (y.toMul ≫ (CommGroupScheme.groupHom K.inclusion).hom.hom) =
            Additive.ofMul v.toMul.val) ↔
        ∃ y : Additive (Over.mk s ⟶ H.X),
          Additive.ofMul (y.toMul ≫ i.hom.hom) = e.symm v := by
      apply exists_congr
      intro y
      constructor
      · intro hy
        apply e.injective
        apply toSection_injective A.toGrp (Over.mk s) (n.val * n.val)
        rw [e.apply_symm_apply]
        change Additive.ofMul ((y.toMul ≫ i.hom.hom) ≫
          (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp
            ((n.val * n.val : ℕ) : ℤ))).hom.hom) = Additive.ofMul v.toMul.val
        change Additive.ofMul (y.toMul ≫ (i.hom.hom ≫
          (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp
            ((n.val * n.val : ℕ) : ℤ))).hom.hom)) = Additive.ofMul v.toMul.val at hy
        simpa only [Category.assoc] using hy
      · intro hy
        have hz := congrArg (fun z => toSection A.toGrp (Over.mk s)
          (n.val * n.val) (e z)) hy
        rw [e.apply_symm_apply] at hz
        change Additive.ofMul ((y.toMul ≫ i.hom.hom) ≫
          (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp
            ((n.val * n.val : ℕ) : ℤ))).hom.hom) = Additive.ofMul v.toMul.val at hz
        change Additive.ofMul (y.toMul ≫ (i.hom.hom ≫
          (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp
            ((n.val * n.val : ℕ) : ℤ))).hom.hom)) = Additive.ofMul v.toMul.val
        simpa only [Category.assoc] using hz
    rw [heq, ← hM]
    change e (e.symm v) ∈ normalizedLevelSubgroup A.toGrp (Over.mk s) n L ↔ _
    rw [e.apply_symm_apply]
    exact evaluation_mem_normalizedLevelSubgroup_iff A.toGrp (Over.mk s) n L hlower x
  refine ⟨D.B, squareReverseIso n.val n.property.1 D.q r hqr hrq, ?_⟩
  exact squareReverseIso_image_iff (Over.mk s) n.val n.property.1 D.q r hqr hrq L hupper himage

end Langlands.AbelianScheme.Tate
