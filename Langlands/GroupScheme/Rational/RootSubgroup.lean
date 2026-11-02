import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.Dynamic.Action
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # All-test relative root subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}

/-- The actual scheme-theoretic kernel of a character. It need not be smooth. -/
abbrev characterKernel (a : characterLattice S) : GroupScheme B :=
  kernel (CommGroupScheme.groupHom a)

/-- The inclusion of the actual character kernel into the torus. -/
abbrev characterKernelι (a : characterLattice S) : characterKernel a ⟶ S.toGrp :=
  kernelι (CommGroupScheme.groupHom a)

/-- The all-test centralizer of the character kernel, including all refinements. -/
def kernelCentralizer (i : S.toGrp ⟶ G) (a : characterLattice S) : SubgroupFunctor G :=
  ((AutomorphicAction.conjugation i).restrict (characterKernelι a)).fixedSubgroup

/-- Membership is actual commutation with every kernel point on every refinement. -/
theorem mem_kernelCentralizer (i : S.toGrp ⟶ G) (a : characterLattice S)
    {T : Over B} {g : T ⟶ G.X} :
    g ∈ (kernelCentralizer i a).carrier T ↔
      ∀ (V : Over B) (b : V ⟶ T) (c : V ⟶ (characterKernel a).X),
        Commute (b ≫ g) (c ≫ (characterKernelι a ≫ i).hom.hom) := by
  change (∀ (V : Over B) (b : V ⟶ T) (c : V ⟶ (characterKernel a).X),
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a)).act c (b ≫ g) =
      b ≫ g) ↔ _
  simp only [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act,
    Grp.comp_hom_hom, Category.assoc]
  constructor
  · intro h V b c
    exact ((mul_inv_eq_iff_eq_mul).mp (h V b c)).symm
  · intro h V b c
    rw [(h V b c).symm.eq, mul_inv_cancel_right]

/-- The torus-conjugation orbit on the product with the entire torus. -/
def orbit (i : S.toGrp ⟶ G) {T : Over B} (g : T ⟶ G.X) : T ⊗ S.X ⟶ G.X :=
  (AutomorphicAction.conjugation i).act (snd T S.X) (fst T S.X ≫ g)

/-- An extension through the actual character `a : S → Gm`. The affine-line
parameter is `a(s)`, with no choice of a primitive lift or a cocharacter. -/
def IsOrbitExtension (i : S.toGrp ⟶ G) (a : characterLattice S)
    {T : Over B} (g : T ⟶ G.X) (e : T ⊗ AffineLine.scheme B ⟶ G.X) : Prop :=
  T ◁ ((CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) ≫ e =
    orbit i g

variable (i : S.toGrp ⟶ G) (a : characterLattice S)

theorem orbit_one {T : Over B} : orbit i (1 : T ⟶ G.X) = 1 := by
  simp only [orbit, MonObj.comp_one, AutomorphicAction.act_one]

theorem orbit_mul {T : Over B} (g h : T ⟶ G.X) :
    orbit i (g * h) = orbit i g * orbit i h := by
  simp only [orbit, MonObj.comp_mul, AutomorphicAction.act_mul_right]

theorem orbit_inv {T : Over B} (g : T ⟶ G.X) : orbit i g⁻¹ = (orbit i g)⁻¹ := by
  simp only [orbit, GrpObj.comp_inv, AutomorphicAction.act_inv]

theorem whiskerRight_orbit {T V : Over B} (b : V ⟶ T) (g : T ⟶ G.X) :
    b ▷ S.X ≫ orbit i g = orbit i (b ≫ g) := by
  simp only [orbit, AutomorphicAction.naturality, whiskerRight_snd,
    whiskerRight_fst_assoc]

theorem IsOrbitExtension.one {T : Over B} :
    IsOrbitExtension i a (1 : T ⟶ G.X) 1 := by
  rw [IsOrbitExtension, MonObj.comp_one, orbit_one]

theorem IsOrbitExtension.mul {T : Over B} {g h : T ⟶ G.X}
    {e e' : T ⊗ AffineLine.scheme B ⟶ G.X}
    (he : IsOrbitExtension i a g e) (he' : IsOrbitExtension i a h e') :
    IsOrbitExtension i a (g * h) (e * e') := by
  rw [IsOrbitExtension, MonObj.comp_mul, he, he', orbit_mul]

theorem IsOrbitExtension.inv {T : Over B} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme B ⟶ G.X} (he : IsOrbitExtension i a g e) :
    IsOrbitExtension i a g⁻¹ e⁻¹ := by
  rw [IsOrbitExtension, GrpObj.comp_inv, he, orbit_inv]

theorem IsOrbitExtension.whiskerRight {T V : Over B} (b : V ⟶ T)
    {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme B ⟶ G.X}
    (he : IsOrbitExtension i a g e) :
    IsOrbitExtension i a (b ≫ g) (b ▷ AffineLine.scheme B ≫ e) := by
  rw [IsOrbitExtension, whisker_exchange_assoc, he, whiskerRight_orbit]

/-- The actual relative root subgroup functor on every test scheme: an orbit
extension through `a` with identity value at zero. No realization is an input. -/
def subgroup : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∃ e, IsOrbitExtension i a g e ∧ Dynamic.evalZero e = 1}
      one_mem' := ⟨1, IsOrbitExtension.one i a, Dynamic.evalZero_one⟩
      mul_mem' := fun ⟨e, he, he0⟩ ⟨e', he', he0'⟩ =>
        ⟨e * e', he.mul i a he', by rw [Dynamic.evalZero_mul, he0, he0', mul_one]⟩
      inv_mem' := fun ⟨e, he, he0⟩ =>
        ⟨e⁻¹, he.inv i a, by rw [Dynamic.evalZero_inv, he0, inv_one]⟩ }
  comp_mem b _ := fun ⟨e, he, he0⟩ =>
    ⟨b ▷ AffineLine.scheme B ≫ e, he.whiskerRight i a b, by
      rw [Dynamic.evalZero_whiskerRight, he0, MonObj.comp_one]⟩

theorem mem_subgroup {T : Over B} {g : T ⟶ G.X} :
    g ∈ (subgroup i a).carrier T ↔
      ∃ e, IsOrbitExtension i a g e ∧ Dynamic.evalZero e = 1 := Iff.rfl

section RepresentedCentralizer

variable {C : GroupScheme B} (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)

/-- The full torus action on a represented kernel centralizer, constructed from
its inclusion by the public represented-action machinery. -/
def centralizerAction : AutomorphicAction S.toGrp C :=
  AutomorphicAction.onRepresentedFixedSubgroup (AutomorphicAction.conjugation i)
    (characterKernelι a) j hj

/-- The actual kernel acts trivially; its smoothness is not required. -/
theorem centralizerAction_kernelActsTrivially :
    (centralizerAction i a j hj).KernelActsTrivially (CommGroupScheme.groupHom a) :=
  fun _ c g => AutomorphicAction.onRepresentedFixedSubgroup_restrict_act
    (AutomorphicAction.conjugation i) (characterKernelι a) j hj c g

variable [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- Descent through the actual character identifies the quotient torus with Gm.
Only the fpqc character map and a represented centralizer are needed. -/
def quotientAction : AutomorphicAction (Gm B).toGrp C :=
  AutomorphicAction.quotientAction (centralizerAction i a j hj)
    (CommGroupScheme.groupHom a) (centralizerAction_kernelActsTrivially i a j hj)

/-- Pullback along the character recovers the full torus action. -/
theorem quotientAction_restrict :
    (quotientAction i a j hj).restrict (CommGroupScheme.groupHom a) =
      centralizerAction i a j hj :=
  AutomorphicAction.quotientAction_restrict _ _ _

end RepresentedCentralizer

end RelativeRoot

end Langlands.GroupScheme
