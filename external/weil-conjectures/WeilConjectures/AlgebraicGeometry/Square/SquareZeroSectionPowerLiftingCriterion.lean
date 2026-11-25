/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorPowerBoundary

/-! # The obstruction-and-lifting conjunct

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS.
(blueprint: lem-sc-square-zero-section-power-obstruction-core).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u

private theorem nsmul_addHom_zero {A B : Type*} [AddZeroClass A] [AddMonoid B]
    (b : A →+ B) (k : ℕ) : k • b 0 = 0 := by
  rw [b.map_zero, nsmul_zero]

/-- Core obstruction and lifting criterion, omitting quasi-coherence.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS.
(blueprint: lem-sc-square-zero-section-power-obstruction-core).
Proof: Tensor the ideal sequence by L^d, which is invertible, to obtain an exact
sequence with kernel I tensor L^d and quotient j_*j^*(L^d). The kernel is killed
by I, since I^2=0. Identify it with the pushforward of its pullback using the
annihilated-module theorem. The affine-morphism edge isomorphism identifies its
H^1 with H^1 on Z. Take F=j^*(I tensor L^n), and take xi
to be the boundary of s under this identification. Form the direct sum of the
sequences over d. Local frames of L identify the resulting graded algebra with
a polynomial algebra, so it is commutative and its kernel is square zero.
The boundary derivation theorem and induction give boundary(s^(e+1)) =
(e+1) s^e xi. Inclusion and projection of graded summands identify this with
the degree n*(e+1) boundary. Naturality of the edge isomorphism identifies the
s^e action with the displayed H^1 map. Its vanishing therefore makes the
boundary zero. Exactness supplies a global lift t. Iterated tensor-pullback
comparisons (including the unit comparison when n=0) give a, and identify
restriction of t followed by a with the pure tensor power of s. -/
theorem square_zero_section_power_obstruction_core
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) :
    let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    ∃ (xi : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj F),
      ∀ e : ℕ, (RingedSpace.moduleCohomology Z.toRingedSpace 1).map
        ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection
          (((tensorPullback j).obj L).tensorPow n) s) e) xi = 0 →
      ∃ t : (L.tensorPow (n * (e + 1))).val.presheaf.obj (Opposite.op ⊤),
        ∃ a : (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1),
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t) ≫ a.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) (e + 1) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))
  have hη (d : ℕ) : Epi ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (L.tensorPow d)) := by
    obtain ⟨_, h, _⟩ := closedImmersion_unit_quotient j
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
    have : Epi (adj.unit.app (L.tensorPow d)) := (h (L.tensorPow d)).1
    let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
    change Epi (adj'.unit.app (L.tensorPow d))
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' (L.tensorPow d)]
    infer_instance
  have hshort (d : ℕ) :
      (CategoryTheory.ShortComplex.kernelSequence
        ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow d))).ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mk'
      (CategoryTheory.ShortComplex.kernelSequence_exact _) inferInstance (hη d)
  obtain ⟨xi, hxi⟩ := square_zero_tensor_power_boundary j L hI n s hshort
  refine ⟨xi, ?_⟩
  intro e he
  obtain ⟨a, b, hb⟩ := hxi e
  have hz := congrArg (fun x ↦ (e + 1) • b x) he
  have hz' := nsmul_addHom_zero b (e + 1)
  have hb0 := hb.trans (hz.trans hz')
  obtain ⟨t, ht⟩ := (RingedSpace.moduleSectionBoundary_eq_zero_iff X.toRingedSpace
    (CategoryTheory.ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow (n * (e + 1)))))
    (hshort (n * (e + 1))) _).mp hb0
  refine ⟨t, a, ?_⟩
  let q := tensorPowSection (homOfGlobalSection
    (((tensorPullback j).obj L).tensorPow n) s) (e + 1) ≫ a.inv
  have hq : homOfGlobalSection _ (q.app ⊤ (1 : Γ(Z, ⊤))) = q := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext U
    change (homOfGlobalSection _ _).app U.unop (1 : Γ(Z, U.unop)) =
      q.app U.unop (1 : Γ(Z, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (q.app U.unop)
      (map_one (Z.presheaf.map (homOfLE
        (le_top : U.unop ≤ ⊤)).op).hom :)
  change ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
    (L.tensorPow (n * (e + 1)))).val.app (Opposite.op ⊤) t =
      q.app ⊤ (1 : Γ(Z, ⊤)) at ht
  rw [ht, hq]
  simp only [q, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
