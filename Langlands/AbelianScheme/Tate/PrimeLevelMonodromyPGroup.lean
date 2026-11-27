import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.GroupTheory.PGroup

/-! # Prime-power monodromy when prime torsion is fixed -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- Divisibility gives the ordinary inclusion of the smaller torsion level. -/
def levelInclusionOfDvd (T : Over S) {m n : ℕ} (h : m ∣ n) : Level G T m →+ Level G T n :=
  MonoidHom.toAdditive (Subgroup.inclusion (by
    intro x hx
    rw [mem_levelGroup] at hx ⊢
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, hx, one_pow]))

/-- The map of actual torsion kernel schemes inducing this inclusion. -/
def kernelInclusion {m n : ℕ} (h : m ∣ n) :
    (kernel (multiplication G m)).X ⟶ (kernel (multiplication G n)).X :=
  kernelLift G _ n (levelInclusionOfDvd G _ h (kernelSection G m))

theorem kernelLevelEquiv_inclusion (T : Over S) {m n : ℕ} (h : m ∣ n)
    (x : Additive (T ⟶ (kernel (multiplication G m)).X)) :
    kernelLevelEquiv G T n (.ofMul (x.toMul ≫ kernelInclusion G h)) =
      levelInclusionOfDvd G T h (kernelLevelEquiv G T m x) := by
  apply toSection_injective G T n
  change Additive.ofMul ((x.toMul ≫ kernelInclusion G h) ≫
      (kernelι (multiplication G n)).hom.hom) =
    Additive.ofMul (x.toMul ≫ (kernelι (multiplication G m)).hom.hom)
  rw [Category.assoc, kernelInclusion, kernelLift_ι]
  change Additive.ofMul (x.toMul ≫ (kernelSection G m).toMul.val) = _
  rw [kernelSection_val]

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (levelInclusionOfDvd kernelInclusion kernelLevelEquiv_inclusion)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (A : AbelianScheme S)
  {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
  (hu_m : IsUnit (m : Γ(S, ⊤))) (hu_n : IsUnit (n : Γ(S, ⊤)))

/-- The residue-linear automorphisms of the finite torsion level form a group representation. -/
def levelMonodromyHom : FundamentalGroup s hs →*
    (Level A (Over.mk s) n ≃ₗ[ZMod n] Level A (Over.mk s) n) where
  toFun g :=
    { levelMonodromy s hs torsionFiniteEtale A n hn hu_n g with
      map_smul' := levelMonodromy_zmod_smul s hs torsionFiniteEtale A n hn hu_n g }
  map_one' := LinearEquiv.ext (levelMonodromy_one s hs torsionFiniteEtale A n hn hu_n)
  map_mul' g k := LinearEquiv.ext (levelMonodromy_mul s hs torsionFiniteEtale A n hn hu_n g k)

set_option backward.isDefEq.respectTransparency false in
/-- The finite-level homomorphism is continuous for the discrete topology on
its residue-linear automorphism group. -/
theorem continuous_levelMonodromyHom :
    let : TopologicalSpace (Level A (Over.mk s) n ≃ₗ[ZMod n] Level A (Over.mk s) n) := ⊥
    Continuous (levelMonodromyHom s hs A hn hu_n : FundamentalGroup s hs →
      (Level A (Over.mk s) n ≃ₗ[ZMod n] Level A (Over.mk s) n)) := by
  classical
  intro inst
  let M := Level A (Over.mk s) n
  have : Finite M := level_finite s hs torsionFiniteEtale A n hn hu_n
  let toFunction : (M ≃ₗ[ZMod n] M) → (M → M) := fun e => e
  have hinj : Function.Injective toFunction := fun _ _ h => LinearEquiv.ext (congrFun h)
  have hcont : Continuous (fun g : FundamentalGroup s hs =>
      toFunction (levelMonodromyHom s hs A hn hu_n g)) := by
    apply continuous_pi
    intro x
    change Continuous (fun g : FundamentalGroup s hs =>
      levelMonodromy s hs torsionFiniteEtale A n hn hu_n g x)
    have hx : Continuous (fun g : FundamentalGroup s hs => (g, x)) :=
      continuous_id.prodMk continuous_const
    exact Continuous.comp (f := fun g : FundamentalGroup s hs => (g, x))
      (continuous_levelMonodromy s hs torsionFiniteEtale A n hn hu_n) hx
  have hdecode : Continuous (Function.invFun toFunction) := continuous_of_discreteTopology
  have h := hdecode.comp hcont
  have hleft (e : M ≃ₗ[ZMod n] M) : Function.invFun toFunction (toFunction e) = e :=
    Function.leftInverse_invFun hinj e
  simpa only [Function.comp_def, hleft] using h

/-- The torsion action has a finite image. -/
theorem finite_levelMonodromyImage : Finite (levelMonodromyHom s hs A hn hu_n).range := by
  let M := Level A (Over.mk s) n
  have : Finite M := level_finite s hs torsionFiniteEtale A n hn hu_n
  exact Finite.of_injective (fun e : (levelMonodromyHom s hs A hn hu_n).range => (e.val : M → M))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- Continuity holds with the discrete topology on the actual image as well. -/
theorem continuous_levelMonodromyToImage :
    let : TopologicalSpace (Level A (Over.mk s) n ≃ₗ[ZMod n] Level A (Over.mk s) n) := ⊥
    Continuous ((levelMonodromyHom s hs A hn hu_n).rangeRestrict :
      FundamentalGroup s hs → (levelMonodromyHom s hs A hn hu_n).range) := by
  intro inst
  exact (continuous_levelMonodromyHom s hs A hn hu_n).subtype_mk _

/-- Inclusions between actual finite torsion levels are monodromy-equivariant. -/
theorem levelMonodromy_inclusion (h : m ∣ n) (g : FundamentalGroup s hs)
    (x : Level A (Over.mk s) m) :
    levelMonodromy s hs torsionFiniteEtale A n hn hu_n g (levelInclusionOfDvd A.toGrp _ h x) =
      levelInclusionOfDvd A.toGrp _ h (levelMonodromy s hs torsionFiniteEtale A m hm hu_m g x) := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv A (Over.mk s) m).surjective x
  rw [← kernelLevelEquiv_inclusion, levelMonodromy_kernel, levelMonodromy_kernel,
    ← kernelLevelEquiv_inclusion]
  have := torsionKernel_isFinite torsionFiniteEtale A m hm hu_m
  have := torsionKernel_etale torsionFiniteEtale A m hm hu_m
  have := torsionKernel_isFinite torsionFiniteEtale A n hn hu_n
  have := torsionKernel_etale torsionFiniteEtale A n hn hu_n
  exact congrArg (fun z => kernelLevelEquiv A (Over.mk s) n (.ofMul z))
    (act_naturality s hs (kernelInclusion A.toGrp h) g y.toMul)

private theorem pow_apply_eq_of_fixed_prime_torsion {R M : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] (p : ℕ) (e : M ≃ₗ[R] M) (hfix : ∀ x : M, p • x = 0 → e x = x)
    (n : ℕ) (x : M) (hx : p ^ n • x = 0) : (e ^ (p ^ n)) x = x := by
  have hpowers (x : M) (hx : p • x = 0) (k : ℕ) : (e ^ k) x = x := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hfix x hx]
  induction n generalizing x with
  | zero =>
      have hx' : x = 0 := by simpa only [pow_zero, one_nsmul] using hx
      simp [hx']
  | succ n ih =>
      let f := e ^ (p ^ n)
      have hpx : (p ^ n) • (p • x) = 0 := by rwa [smul_smul, ← pow_succ]
      have hfx : f (p • x) = p • x := ih _ hpx
      let d := f x - x
      have hd : p • d = 0 := by
        rw [show d = f x - x from rfl, nsmul_sub, ← map_nsmul, hfx, sub_self]
      have hfd : f d = d := hpowers d hd _
      have hiter (k : ℕ) : (f ^ k) x = x + k • d := by
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ', LinearEquiv.mul_apply, ih, _root_.map_add, map_nsmul, hfd, succ_nsmul]
            dsimp [d]
            abel
      rw [pow_succ, pow_mul]
      change (f ^ p) x = x
      rw [hiter, hd, add_zero]

/-- With trivial action at the prime level, each prime-power image is a finite
group of prime-power order. -/
def PrimeLevelMonodromyPGroupStatement : Prop :=
  ∀ (S : Scheme.{u}) (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (A : AbelianScheme S) (p : ℕ) [Fact p.Prime]
    (h₁ : IsUnit (p : Γ(S, ⊤))),
    levelMonodromyHom s hs A (Fact.out : p.Prime).pos h₁ = 1 →
      ∀ (n : ℕ) (hu : IsUnit ((p ^ n : ℕ) : Γ(S, ⊤))),
        IsPGroup p (levelMonodromyHom s hs A (pow_pos (Fact.out : p.Prime).pos n) hu).range

/-- Each finite torsion action has prime-power order by the filtration by
annihilators of powers of the prime. -/
theorem primeLevelMonodromyPGroup : PrimeLevelMonodromyPGroupStatement.{u} := by
  intro S Ω _ s hs A p _ h₁ htriv n hu
  let hn := pow_pos (Fact.out : p.Prime).pos n
  let ρ := levelMonodromyHom s hs A hn hu
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨e, g, hg⟩
  subst e
  refine ⟨n, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
  change ((ρ g) ^ (p ^ n)) x = x
  refine pow_apply_eq_of_fixed_prime_torsion p (ρ g) ?_ n x
    (GroupScheme.Tate.level_nsmul_eq_zero A.toGrp (Over.mk s) (p ^ n) x)
  intro y hy
  cases n with
  | zero =>
      have hy' := GroupScheme.Tate.level_nsmul_eq_zero A.toGrp (Over.mk s) (p ^ 0) y
      change (1 : ℕ) • y = 0 at hy'
      rw [one_nsmul] at hy'
      rw [hy', map_zero]
  | succ n =>
      let z : Level A (Over.mk s) p := Additive.ofMul ⟨y.toMul.val, by
        rw [GroupScheme.Tate.mem_levelGroup]
        exact congrArg (fun z : Level A (Over.mk s) (p ^ (n + 1)) => z.toMul.val) hy⟩
      let hdiv : p ∣ p ^ (n + 1) := dvd_pow_self _ (Nat.succ_ne_zero _)
      have hzy : levelInclusionOfDvd A.toGrp (Over.mk s) hdiv z = y := by
        apply GroupScheme.Tate.toSection_injective A.toGrp (Over.mk s)
        rfl
      have hz : levelMonodromy s hs torsionFiniteEtale A p (Fact.out : p.Prime).pos h₁ g z = z :=
        congrArg (fun f => (f g) z) htriv
      change levelMonodromy s hs torsionFiniteEtale A (p ^ (n + 1)) hn hu g y = y
      rw [← hzy, levelMonodromy_inclusion s hs A (Fact.out : p.Prime).pos hn h₁ hu, hz]

end Langlands.AbelianScheme.Tate
