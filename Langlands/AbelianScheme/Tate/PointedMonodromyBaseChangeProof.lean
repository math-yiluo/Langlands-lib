import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeStatement

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

universe u
namespace Langlands.GroupScheme
open Langlands.AlgebraicGeometry.FiniteEtale
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {Ω : Type u} [Field Ω]
  (t : Spec (.of Ω) ⟶ S')
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

private instance pullback_isFinite (G : Grp (Over S)) [IsFinite G.X.hom] :
    IsFinite ((Over.pullback b).mapGrp.obj G).X.hom := by
  change IsFinite (pullback.snd G.X.hom b)
  infer_instance

private instance pullback_etale (G : Grp (Over S)) [Etale G.X.hom] :
    Etale ((Over.pullback b).mapGrp.obj G).X.hom := by
  change Etale (pullback.snd G.X.hom b)
  infer_instance

/-- Pullback adjunction on finite étale group points intertwines geometric monodromy. -/
theorem baseChangePointsEquiv_act (G : Grp (Over S))
    [IsFinite G.X.hom] [Etale G.X.hom]
    (g : FundamentalGroup t ht)
    (x : Over.mk t ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    baseChangePointsEquiv b G (Over.mk t)
      (act t ht ((Over.pullback b).mapGrp.obj G).X g x) =
    act (t ≫ b) hs G.X (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (baseChangePointsEquiv b G (Over.mk t) x) := by
  apply Over.OverMorphism.ext
  exact (fundamentalGroupMap_smul_left_of_comp b t (t ≫ b) rfl ht hs g
    (Y := ofOver G.X) (baseChangePointsEquiv b G (Over.mk t) x)
    (Y' := ofOver ((Over.pullback b).mapGrp.obj G).X) x
    (pullback.fst G.X.hom b) pullback.condition rfl).symm

namespace Tate
variable (G : Grp (Over S)) [IsCommMonObj G.X]

/-- Compatibility of the existing level comparison with the actual kernel pullback. -/
theorem levelBaseChange_kernel (T : Over S') (n : ℕ)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X) :
    levelBaseChange b G T n
      (kernelLevelEquiv _ T n (Additive.ofMul
        (x ≫ (torsionBaseChangeIso b G (n : ℤ)).hom.hom.hom))) =
    kernelLevelEquiv G ((Over.map b).obj T) n
      (Additive.ofMul (baseChangePointsEquiv b (torsion G (n : ℤ)) T x)) :=
  torsionBaseChangeIso_points b G (n : ℤ) T x

/-- The actual finite torsion comparison intertwines the restricted action. -/
theorem levelBaseChange_finiteLevelMonodromy (n : ℕ)
    [IsFinite (kernel (multiplication G n)).X.hom]
    [Etale (kernel (multiplication G n)).X.hom]
    [IsFinite (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom]
    [Etale (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom]
    (g : FundamentalGroup t ht)
    (z : Level ((Over.pullback b).mapGrp.obj G) (Over.mk t) n) :
    levelBaseChange b G (Over.mk t) n
      (finiteLevelMonodromy _ t ht n g z) =
    finiteLevelMonodromy G (t ≫ b) hs n
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (levelBaseChange b G (Over.mk t) n z) := by
  let : IsFinite (torsion G (n : ℤ)).X.hom :=
    inferInstanceAs (IsFinite (kernel (multiplication G n)).X.hom)
  let : Etale (torsion G (n : ℤ)).X.hom :=
    inferInstanceAs (Etale (kernel (multiplication G n)).X.hom)
  let : IsFinite (torsion ((Over.pullback b).mapGrp.obj G) (n : ℤ)).X.hom :=
    inferInstanceAs (IsFinite (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom)
  let : Etale (torsion ((Over.pullback b).mapGrp.obj G) (n : ℤ)).X.hom :=
    inferInstanceAs (Etale (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom)
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv ((Over.pullback b).mapGrp.obj G)
    (Over.mk t) n).surjective z
  let e := torsionBaseChangeIso b G (n : ℤ)
  let x := y.toMul ≫ e.inv.hom.hom
  have hy : y = Additive.ofMul (x ≫ e.hom.hom.hom) := by
    change y.toMul = (y.toMul ≫ e.inv.hom.hom) ≫ e.hom.hom.hom
    rw [Category.assoc]
    have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) e.inv_hom_id
    rw [he]
    exact (Category.comp_id y.toMul).symm
  have hx₁ := levelBaseChange_kernel b G (Over.mk t) n x
  have hx₂ := levelBaseChange_kernel b G (Over.mk t) n
    (act t ht ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X g x)
  have hnat := act_naturality t ht e.hom.hom.hom g x
  have hact := baseChangePointsEquiv_act b t ht hs (torsion G (n : ℤ)) g x
  rw [hy, finiteLevelMonodromy_kernel]
  calc
    _ = levelBaseChange b G (Over.mk t) n
        (kernelLevelEquiv _ (Over.mk t) n (Additive.ofMul
          (act t ht ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X g x
            ≫ e.hom.hom.hom))) :=
      congrArg (fun v => levelBaseChange b G (Over.mk t) n
        (kernelLevelEquiv _ (Over.mk t) n (Additive.ofMul v))) hnat
    _ = kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk t)
          (act t ht ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X g x))) := hx₂
    _ = kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul (act (t ≫ b) hs (torsion G (n : ℤ)).X
          (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
          (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk t) x))) :=
      congrArg (fun v => kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul v)) hact
    _ = finiteLevelMonodromy G (t ≫ b) hs n
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
        (kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
          (Additive.ofMul (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk t) x))) :=
      (finiteLevelMonodromy_kernel G (t ≫ b) hs n _ _).symm
    _ = _ := congrArg
      (finiteLevelMonodromy G (t ≫ b) hs n
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)) hx₁.symm

end Tate
end Langlands.GroupScheme

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {Ω : Type u} [Field Ω]
  (t : Spec (.of Ω) ⟶ S')
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- Pointed base change on a positive invertible abelian torsion level is equivariant. -/
theorem levelBaseChange_monodromy (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) (hu' : IsUnit (n : Γ(S', ⊤)))
    (g : FundamentalGroup t ht)
    (x : Level ((AbelianScheme.baseChange b).obj A) (Over.mk t) n) :
    GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) n
      (levelMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) n hn hu' g x) =
    levelMonodromy (t ≫ b) hs htor A n hn hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) n x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have : IsFinite (GroupScheme.kernel (GroupScheme.multiplication
      ((Over.pullback b).mapGrp.obj A.toGrp) n)).X.hom :=
    torsionKernel_isFinite htor ((AbelianScheme.baseChange b).obj A) n hn hu'
  have : Etale (GroupScheme.kernel (GroupScheme.multiplication
      ((Over.pullback b).mapGrp.obj A.toGrp) n)).X.hom :=
    torsionKernel_etale htor ((AbelianScheme.baseChange b).obj A) n hn hu'
  exact GroupScheme.Tate.levelBaseChange_finiteLevelMonodromy b t ht hs A.toGrp n g x

variable (P : ℕ → Prop)
  (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index P, IsUnit (n.val : Γ(S', ⊤)))

/-- Equivariance of the actual selected inverse limit follows coordinatewise. -/
theorem integralBaseChange_monodromy (g : FundamentalGroup t ht)
    (x : Integral ((AbelianScheme.baseChange b).obj A) (Over.mk t) P) :
    integralBaseChange b A (Over.mk t) P
      (integralMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) P hu' g x) =
    integralMonodromy (t ≫ b) hs htor A P hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (integralBaseChange b A (Over.mk t) P x) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_monodromy b t ht hs htor A n.val n.property.1 (hu n) (hu' n) g
    (x.val n)

/-- Equivariance after rationalizing the selected integral Tate module. -/
theorem rationalBaseChange_monodromy (g : FundamentalGroup t ht)
    (x : Rational ((AbelianScheme.baseChange b).obj A) (Over.mk t) P) :
    rationalBaseChange b A (Over.mk t) P
      (rationalMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) P hu' g x) =
    rationalMonodromy (t ≫ b) hs htor A P hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (rationalBaseChange b A (Over.mk t) P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralBaseChange b A (Over.mk t) P
      (integralMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) P hu' g x) =
      q ⊗ₜ[ℤ] integralMonodromy (t ≫ b) hs htor A P hu
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
        (integralBaseChange b A (Over.mk t) P x)
    rw [integralBaseChange_monodromy]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- The finite, integral, and rational compatibility statements together. -/
theorem pointedMonodromyBaseChange : PointedMonodromyBaseChange.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro S S' b Ω inst t ht hs htor A n hn hu hu' g x
    exact levelBaseChange_monodromy b t ht hs htor A n hn hu hu' g x
  · intro S S' b Ω inst t ht hs htor A P hu hu' g x
    exact integralBaseChange_monodromy b t ht hs htor A P hu hu' g x
  · intro S S' b Ω inst t ht hs htor A P hu hu' g x
    exact rationalBaseChange_monodromy b t ht hs htor A P hu hu' g x

end Langlands.AbelianScheme.Tate
