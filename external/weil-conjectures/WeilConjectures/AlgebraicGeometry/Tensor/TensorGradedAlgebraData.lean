/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPowerAlgebraCoproduct
import WeilConjectures.AlgebraicGeometry.Curve.AlgebraTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Graded algebra and quotient of tensor powers

Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- The underlying module map, with its source and target stated explicitly.
Source: Stacks Project, Tag 09MS, the quotient in the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraMap {X : Scheme.{u}} {B C : X.CommAlgebraSheaf} (p : B ⟶ C) :
    commAlgebraSheafModule X.sheaf B ⟶ commAlgebraSheafModule X.sheaf C :=
  (commAlgebraSheafModuleFunctor X.sheaf).map p

/-- Read a section of the underlying module as a section of the algebra sheaf.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraSection {X : Scheme.{u}} (B : X.CommAlgebraSheaf) (U : X.Opens)
    (z : Γ(commAlgebraSheafModule X.sheaf B, U)) : B.right.obj.obj (op U) := z

attribute [local irreducible] tensorGradedAlgebraMap commAlgebraSheafModule

/-- The chosen tensor-pullback unit, with a compact explicit module-map type.
Source: Stacks Project, Tag 0096, the tensor-pullback adjunction.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedUnit {X Z : Scheme.{u}} (j : Z ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward j).obj ((tensorPullback j).obj M) :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M

attribute [local irreducible] tensorGradedUnit tensorPullback

/-- The two graded algebra sheaves, with their underlying module coproducts.
No exactness, kernel, or degree projection data are included.
Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data). -/
structure TensorGradedAlgebraData {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  b_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)
  c_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf C) c)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  b_multiply : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
    (t : Γ(L.tensorPow d, U)),
    tensorGradedAlgebraSection B U ((b a).app U s) *
      tensorGradedAlgebraSection B U ((b d).app U t) =
      tensorGradedAlgebraSection B U
        ((b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))

private theorem restrictionCofanIsColimit {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] {M : X.Modules} {D : ℕ → X.Modules}
    (b : ∀ d, D d ⟶ M) (hb : IsColimit (Cofan.mk M b)) :
    Nonempty (IsColimit (Cofan.mk ((pushforward j).obj ((tensorPullback j).obj M))
      (fun d ↦ (pushforward j).map ((tensorPullback j).map (b d))))) := by
  classical
  let F := tensorPullback j ⋙ pushforward j
  let a : tensorPullback j ⊣ pushforward j :=
    Classical.choice (nonempty_tensorPullbackAdjunction j)
  let μ : ∀ N : X.Modules, j.ker.toModules ⊗ N ⟶ N := fun N ↦
    j.ker.toModulesι ▷ N ≫ (λ_ N).hom
  obtain ⟨q, hq, _⟩ := closedImmersion_unit_quotient j
  change ∀ N, _ at hq
  have hq' (N : X.Modules) :
      Epi (a.unit.app N) ∧
        cokernel.π (image.ι (μ N)) ≫ q N = a.unit.app N ∧ IsIso (q N) :=
    ⟨(hq N).1, (hq N).2.2.1, (hq N).2.2.2⟩
  have hμ {N P : X.Modules} (f : N ⟶ P) :
      (tensorLeft j.ker.toModules).map f ≫ μ P = μ N ≫ f := by
    change (j.ker.toModules ◁ f) ≫
      (j.ker.toModulesι ▷ P ≫ (λ_ P).hom) =
      (j.ker.toModulesι ▷ N ≫ (λ_ N).hom) ≫ f
    rw [← Category.assoc, whisker_exchange, Category.assoc, Category.assoc]
    exact congrArg (fun t ↦ j.ker.toModulesι ▷ N ≫ t) (leftUnitor_naturality f)
  have hμzero (N : X.Modules) : μ N ≫ a.unit.app N = 0 := by
    rw [← image.fac (μ N), Category.assoc]
    obtain ⟨w, _⟩ := (hq N).2.1
    rw [w, comp_zero]
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft j.ker.toModules) :=
    (SheafOfModules.tensorHomAdjunction X.sheaf j.ker.toModules).leftAdjoint_preservesColimits
  have ht : IsColimit (Cofan.mk (j.ker.toModules ⊗ M)
      (fun d ↦ (tensorLeft j.ker.toModules).map (b d))) :=
    (Cofan.isColimitMapCoconeEquiv (tensorLeft j.ker.toModules) D
      (Cofan.mk M b)) (isColimitOfPreserves (tensorLeft j.ker.toModules) hb)
  have desc (s : Cofan (fun d ↦ F.obj (D d))) :
      ∃ f : F.obj M ⟶ s.pt,
        a.unit.app M ≫ f =
          Cofan.IsColimit.desc hb (fun d ↦ a.unit.app (D d) ≫ s.inj d) := by
    let g := Cofan.IsColimit.desc hb (fun d ↦ a.unit.app (D d) ≫ s.inj d)
    have hzero : μ M ≫ g = 0 := by
      apply Cofan.IsColimit.hom_ext ht
      intro d
      change (tensorLeft j.ker.toModules).map (b d) ≫ (μ M ≫ g) = _
      rw [← Category.assoc, hμ, Category.assoc]
      have hbg : b d ≫ g = a.unit.app (D d) ≫ s.inj d :=
        Cofan.IsColimit.fac hb _ d
      rw [hbg]
      rw [← Category.assoc, hμzero, zero_comp, comp_zero]
    have hzero' : image.ι (μ M) ≫ g = 0 := by
      apply (cancel_epi (factorThruImage (μ M))).1
      simpa only [← Category.assoc, image.fac, comp_zero] using hzero
    have : IsIso (q M) := (hq' M).2.2
    refine ⟨inv (q M) ≫ cokernel.desc (image.ι (μ M)) g hzero', ?_⟩
    rw [← (hq' M).2.1]
    simp [g]
  choose f hf using desc
  refine ⟨Cofan.IsColimit.mk _ f ?_ ?_⟩
  · intro s d
    have : Epi (a.unit.app (D d)) := (hq' (D d)).1
    apply (cancel_epi (a.unit.app (D d))).1
    change a.unit.app (D d) ≫ (F.map (b d) ≫ f s) = _
    rw [← Category.assoc, ← a.unit.naturality, Category.assoc, hf]
    exact Cofan.IsColimit.fac hb _ d
  · intro s m hm
    have : Epi (a.unit.app M) := (hq' M).1
    apply (cancel_epi (a.unit.app M)).1
    rw [hf]
    apply Cofan.IsColimit.hom_ext hb
    intro d
    rw [Cofan.IsColimit.fac]
    change b d ≫ (a.unit.app M ≫ m) = _
    rw [← Category.assoc]
    have hn := a.unit.naturality (b d)
    change b d ≫ a.unit.app M = a.unit.app (D d) ≫ F.map (b d) at hn
    rw [hn, Category.assoc]
    exact congrArg (fun t ↦ a.unit.app (D d) ≫ t) (hm d)

/-- The tensor powers and their restrictions form a graded algebra quotient.
Source: Stacks Project, Tag 09MS, the direct-sum sequence after coherent-equation-ses.
Proof: on a frame open for L, form the polynomial algebra O_X[T], and on its inverse
image form O_Z[T]. A change of frame by a unit u acts on degree d by u^d. These
algebra automorphisms satisfy the cocycle identities, so the polynomial algebra
sheaves and their coefficient quotient maps glue to B, C, and p. Their underlying
modules are the sheafifications of the direct sums of the tensor powers and of
j_*j^*L^d. The canonical homogeneous inclusions give b and c; the coproduct
universal properties hold locally on frames and therefore globally. Compare the
chosen tensor-pullback adjunction with the usual adjunction by uniqueness of left
adjoints. Its units differ by an invertible natural transformation on j_*j^*.
Precompose each target inclusion c_d by the inverse of this transformation. This
preserves the coproduct universal property and gives the quotient square for the
chosen tensorGradedUnit, without requiring c to preserve multiplication. On a frame,
the multiplication equation is (s T^a)(t T^d) = st T^(a+d); the transition maps preserve
it, and separation of the sheaf gives the equation on every open. This construction
uses neither square-zero of the ideal nor any kernel or projection data.
(blueprint: lem-sc-tensor-graded-algebra-data). -/
theorem tensorGradedAlgebraData_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] :
    Nonempty (TensorGradedAlgebraData j L) := by
  classical
  obtain ⟨B, b, ⟨hb⟩, hmul⟩ := exists_tensorPowerAlgebraCoproduct L
  let a : tensorPullback j ⊣ pushforward j :=
    Classical.choose (exists_tensorPullbackAdjunction j)
  let F := tensorPullback j ⋙ pushforward j
  obtain ⟨C, p, e, hp⟩ := exists_algebraTensorPullbackComparison j a B
  let c := fun d ↦ F.map (b d) ≫ e.hom
  have hc : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf C) c) := by
    let hF := Classical.choice (restrictionCofanIsColimit j b hb)
    apply IsColimit.ofIsoColimit hF
    exact Cofan.ext e (fun d ↦ rfl)
  refine ⟨{ B := B
            C := C
            p := p
            b := b
            c := c
            b_colimit := hb
            c_colimit := hc
            b_quotient := ?_
            b_multiply := hmul }⟩
  intro d
  unfold tensorGradedAlgebraMap tensorGradedUnit
  rw [hp, ← Category.assoc]
  have hn := a.unit.naturality (b d)
  change b d ≫ a.unit.app (commAlgebraSheafModule X.sheaf B) =
    a.unit.app (L.tensorPow d) ≫ F.map (b d) at hn
  rw [hn, Category.assoc]

end
end AlgebraicGeometry.Scheme.Modules
