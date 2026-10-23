import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.Tate.MultiplicativePrime

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Gm.TateComparison
variable {S : Scheme.{u}} {R : CommRingCat.{u}} (s : Spec R ⟶ S)

/-- The actual affine torsion comparison, expressed through the kernel points. -/
def affineLevelEquiv (n : ℕ) :
    Tate.Level (Gm S).toGrp (Over.mk s) n ≃+ TateTwist.Level R n :=
  (Tate.kernelLevelEquiv (Gm S).toGrp (Over.mk s) n).symm.trans (mu.levelEquiv n s)

@[simp] theorem affineLevelEquiv_kernel (n : ℕ)
    (x : Additive (Over.mk s ⟶ (mu S n).X)) :
    affineLevelEquiv s n (Tate.kernelLevelEquiv (Gm S).toGrp (Over.mk s) n x) =
      mu.levelEquiv n s x := by
  simp only [affineLevelEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

/-- This is the existing torsion-to-roots comparison followed by the canonical affine map. -/
theorem affineLevelEquiv_eq (n : ℕ) (x : Tate.Level (Gm S).toGrp (Over.mk s) n) :
    affineLevelEquiv s n x =
      TateTwist.levelMap (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toRingHom n
        (levelEquiv (Over.mk s) n x) := by
  obtain ⟨y, rfl⟩ := (Tate.kernelLevelEquiv (Gm S).toGrp (Over.mk s) n).surjective x
  rw [affineLevelEquiv_kernel]
  rfl

theorem affineLevelEquiv_transition {n m : ℕ} (h : n ∣ m)
    (x : Tate.Level (Gm S).toGrp (Over.mk s) m) :
    affineLevelEquiv s n (Tate.transition (Gm S).toGrp (Over.mk s) h x) =
      TateTwist.transition R h (affineLevelEquiv s m x) := by
  rw [affineLevelEquiv_eq, levelEquiv_transition, affineLevelEquiv_eq]
  exact TateTwist.levelMap_transition _ h _

end Langlands.GroupScheme.Gm.TateComparison

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme
open Langlands.GroupScheme.Gm.TateComparison

private theorem kernel_isFinite (S : Scheme.{u}) (n : ℕ) [IsFinite (mu S n).X.hom] :
    IsFinite (kernel (multiplication (Gm S).toGrp n)).X.hom :=
  inferInstanceAs (IsFinite (mu S n).X.hom)

private theorem kernel_etale (S : Scheme.{u}) (n : ℕ) [Etale (mu S n).X.hom] :
    Etale (kernel (multiplication (Gm S).toGrp n)).X.hom :=
  inferInstanceAs (Etale (mu S n).X.hom)

attribute [local instance] kernel_isFinite kernel_etale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (n : ℕ) [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]

/-- Actual geometric evaluation on roots of unity, without a choice of roots. -/
def levelMonodromy (g : FundamentalGroup s hfin) : AddAut (Level Ω n) :=
  ((affineLevelEquiv s n).symm.trans
    (Tate.finiteLevelMonodromy (Gm S).toGrp s hfin n g)).trans (affineLevelEquiv s n)

/-- The affine comparison intertwines the existing actual Gm action and the root action. -/
@[simp] theorem affineLevelEquiv_monodromy (g : FundamentalGroup s hfin)
    (x : Tate.Level (Gm S).toGrp (Over.mk s) n) :
    levelMonodromy s hfin n g (affineLevelEquiv s n x) =
      affineLevelEquiv s n (Tate.finiteLevelMonodromy (Gm S).toGrp s hfin n g x) := by
  simp [levelMonodromy]

/-- On actual kernel points this action is precisely evaluation of the natural automorphism. -/
theorem levelMonodromy_kernel (g : FundamentalGroup s hfin)
    (x : Additive (Over.mk s ⟶ (mu S n).X)) :
    levelMonodromy s hfin n g (mu.levelEquiv n s x) =
      mu.levelEquiv n s (Additive.ofMul (act s hfin (mu S n).X g x.toMul)) := by
  rw [← affineLevelEquiv_kernel, affineLevelEquiv_monodromy,
    Tate.finiteLevelMonodromy_kernel, affineLevelEquiv_kernel]
  rfl

@[simp] theorem levelMonodromy_one (x : Level Ω n) :
    levelMonodromy s hfin n 1 x = x := by
  simp [levelMonodromy, Tate.finiteLevelMonodromy_one]

theorem levelMonodromy_mul (g h : FundamentalGroup s hfin) (x : Level Ω n) :
    levelMonodromy s hfin n (g * h) x =
      levelMonodromy s hfin n g (levelMonodromy s hfin n h x) := by
  simp only [levelMonodromy, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rw [Tate.finiteLevelMonodromy_mul]

/-- Residue linearity uses the existing root module, not an additional scalar action. -/
def levelMonodromyLinear (g : FundamentalGroup s hfin) : Level Ω n ≃ₗ[ZMod n] Level Ω n :=
  { levelMonodromy s hfin n g with
    map_smul' := fun a x => ZMod.map_smul (levelMonodromy s hfin n g).toAddMonoidHom a x }

/-- The actual finite-level geometric representation. -/
def levelRepresentation : FundamentalGroup s hfin →* (Level Ω n ≃ₗ[ZMod n] Level Ω n) where
  toFun := levelMonodromyLinear s hfin n
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact levelMonodromy_one s hfin n x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact levelMonodromy_mul s hfin n g h x

/-- Install the same additive action locally when an action instance is useful. -/
@[instance_reducible] def levelAction : DistribMulAction (FundamentalGroup s hfin) (Level Ω n) where
  smul := fun g x => levelMonodromy s hfin n g x
  one_smul := levelMonodromy_one s hfin n
  mul_smul := levelMonodromy_mul s hfin n
  smul_zero g := map_zero (levelMonodromy s hfin n g)
  smul_add g := map_add (levelMonodromy s hfin n g)

theorem continuous_levelMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Level Ω n =>
      levelMonodromy s hfin n z.1 z.2) := by
  have he : Continuous (affineLevelEquiv s n) := continuous_of_discreteTopology
  have hi : Continuous (affineLevelEquiv s n).symm := continuous_of_discreteTopology
  change Continuous ((affineLevelEquiv s n) ∘
    (fun z : FundamentalGroup s hfin × Tate.Level (Gm S).toGrp (Over.mk s) n =>
      Tate.finiteLevelMonodromy (Gm S).toGrp s hfin n z.1 z.2) ∘
    (fun z : FundamentalGroup s hfin × Level Ω n =>
      (z.1, (affineLevelEquiv s n).symm z.2)))
  apply he.comp
  apply (Tate.continuous_finiteLevelMonodromy (Gm S).toGrp s hfin n).comp
  exact continuous_fst.prodMk (hi.comp continuous_snd)

theorem levelAction_continuousSMul :
    let := levelAction s hfin n
    ContinuousSMul (FundamentalGroup s hfin) (Level Ω n) :=
  by
    let := levelAction s hfin n
    exact ⟨continuous_levelMonodromy s hfin n⟩

include hfin in
theorem level_finite : Finite (Level Ω n) := by
  let := Tate.finiteLevel_finite (Gm S).toGrp s hfin n
  exact Finite.of_injective (affineLevelEquiv s n).symm (affineLevelEquiv s n).symm.injective

variable {n}

/-- Geometric monodromy commutes with the actual quotient-power transition. -/
theorem levelMonodromy_transition {m : ℕ}
    [IsFinite (mu S m).X.hom] [Etale (mu S m).X.hom]
    (h : n ∣ m) (g : FundamentalGroup s hfin) (x : Level Ω m) :
    levelMonodromy s hfin n g (transition Ω h x) =
      transition Ω h (levelMonodromy s hfin m g x) := by
  obtain ⟨y, rfl⟩ := (affineLevelEquiv s m).surjective x
  rw [← affineLevelEquiv_transition s h y, affineLevelEquiv_monodromy,
    Tate.finiteLevelMonodromy_transition, affineLevelEquiv_transition,
    affineLevelEquiv_monodromy]

end Langlands.TateTwist.Geometry
