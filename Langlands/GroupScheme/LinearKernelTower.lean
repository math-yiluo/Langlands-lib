import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite equivariant fppf quotient towers with character-linear additive kernels -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearKernelTower

variable {k : Type u} [Field k] (D : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Over a field `k`, let `q : E ⟶ D` be a homomorphism to the fixed commutative group `D` and
`p : E ⟶ Q` a homomorphism with full actual kernel `K := kernel p`. The kernel is
character-linear when there are a closed-subgroup homomorphism `a : K ⟶ 𝔾ₐ`, a character `χ`
of `D` and an action `b` of `D` on `K` such that, on every test `T`, conjugation by a point `g`
of `E` acts on `K` as `b` at `g ≫ q`, and `a` intertwines `b` with the linear action of `D` on
`𝔾ₐ` through `χ`. The subgroup may be finite or nonreduced and `χ` may be zero. -/
def IsCharacterLinearKernel {E Q : GroupScheme (Spec (CommRingCat.of k))}
    (q : E ⟶ D.toGrp) (p : E ⟶ Q) : Prop :=
  ∃ (a : kernel p ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) (χ : characterLattice D)
    (b : AutomorphicAction D.toGrp (kernel p)),
    IsClosedSubgroup a ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel p).X),
        b.act (g ≫ q.hom.hom) x ≫ (kernelι p).hom.hom =
          g * (x ≫ (kernelι p).hom.hom) * g⁻¹) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ D.X) (x : T ⟶ (kernel p).X),
        b.act d x ≫ a.hom.hom =
          (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)

/-- A tower of length `n` over the fixed commutative group `D`, starting at `q : E ⟶ D`. Every
stage is an affine group scheme locally of finite type over `k`. At length zero the structural
map `q` is an actual isomorphism of group schemes. At length `n + 1` the map `q` factors as
`p ≫ r`, where `p : E ⟶ Q` is an fppf quotient by its full actual kernel, this kernel is
character-linear for `q`, and `r : Q ⟶ D` has a tower of length `n`. -/
def HasTower : ℕ → {E : GroupScheme (Spec (CommRingCat.of k))} → (E ⟶ D.toGrp) → Prop
  | 0, E, q => LocallyOfFiniteType E.X.hom ∧ IsAffineHom E.X.hom ∧ IsIso q
  | n + 1, E, q => LocallyOfFiniteType E.X.hom ∧ IsAffineHom E.X.hom ∧
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (p : E ⟶ Q) (r : Q ⟶ D.toGrp),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p ∧
          p ≫ r = q ∧ IsCharacterLinearKernel D q p ∧ HasTower n r

/-- The homomorphism `q : E ⟶ D` admits a tower of some finite length. -/
def AdmitsTower {E : GroupScheme (Spec (CommRingCat.of k))} (q : E ⟶ D.toGrp) : Prop :=
  ∃ n : ℕ, HasTower D n q

variable {D} {E : GroupScheme (Spec (CommRingCat.of k))}

@[simp]
theorem hasTower_zero_iff (q : E ⟶ D.toGrp) :
    HasTower D 0 q ↔ LocallyOfFiniteType E.X.hom ∧ IsAffineHom E.X.hom ∧ IsIso q :=
  Iff.rfl

@[simp]
theorem hasTower_succ_iff (n : ℕ) (q : E ⟶ D.toGrp) :
    HasTower D (n + 1) q ↔ LocallyOfFiniteType E.X.hom ∧ IsAffineHom E.X.hom ∧
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (p : E ⟶ Q) (r : Q ⟶ D.toGrp),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p ∧
          p ≫ r = q ∧ IsCharacterLinearKernel D q p ∧ HasTower D n r :=
  Iff.rfl

theorem admitsTower_iff (q : E ⟶ D.toGrp) : AdmitsTower D q ↔ ∃ n : ℕ, HasTower D n q :=
  Iff.rfl

/-- Construct a length-zero tower from an actual isomorphism onto `D`. -/
theorem HasTower.zero {q : E ⟶ D.toGrp} (hft : LocallyOfFiniteType E.X.hom)
    (haff : IsAffineHom E.X.hom) (hq : IsIso q) : HasTower D 0 q :=
  ⟨hft, haff, hq⟩

/-- Construct a successor tower from one quotient step and a tower for the remaining map. -/
theorem HasTower.succ {n : ℕ} {q : E ⟶ D.toGrp} {Q : GroupScheme (Spec (CommRingCat.of k))}
    (p : E ⟶ Q) (r : Q ⟶ D.toGrp) (hft : LocallyOfFiniteType E.X.hom)
    (haff : IsAffineHom E.X.hom)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p)
    (hpr : p ≫ r = q) (hK : IsCharacterLinearKernel D q p) (hr : HasTower D n r) :
    HasTower D (n + 1) q :=
  ⟨hft, haff, Q, p, r, hp, hpr, hK, hr⟩

/-- The source of a tower of any length is locally of finite type over `k`. -/
theorem HasTower.locallyOfFiniteType {n : ℕ} {q : E ⟶ D.toGrp} (h : HasTower D n q) :
    LocallyOfFiniteType E.X.hom := by
  cases n with
  | zero => exact h.1
  | succ n => exact h.1

/-- The source of a tower of any length is affine over `k`. -/
theorem HasTower.isAffineHom {n : ℕ} {q : E ⟶ D.toGrp} (h : HasTower D n q) :
    IsAffineHom E.X.hom := by
  cases n with
  | zero => exact h.2.1
  | succ n => exact h.2.1

/-- A tower of a specified length witnesses that a tower exists. -/
theorem AdmitsTower.of_hasTower {n : ℕ} {q : E ⟶ D.toGrp} (h : HasTower D n q) :
    AdmitsTower D q :=
  ⟨n, h⟩

end Langlands.GroupScheme.LinearKernelTower
