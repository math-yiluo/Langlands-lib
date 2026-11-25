/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The homogeneous action on graded cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 0897
(blueprint: lem-weil-pbc-graded-cohomology-module-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry


/-- The homogeneous action induces the uniquely specified action on graded cohomology.

Source: Stacks Project, Cohomology of Schemes, Lemma 0897(1), the graded action in
its statement; this algebraic part does not require properness or finite generation.
(blueprint: lem-weil-pbc-graded-cohomology-module-structure).

Proof:
Write H_m = H^p(X, G_m). Applying the additive cohomology functor to mu gives
additive maps H_m -> H_(m+k), additive in b by hmu_add. Functoriality and hmu_mul
give the composition law, after transporting along the equalities of degrees.
For a = 1, hmu_scalar says sectionwise that mu m 0 (1) is the identity (with the
transport m+0=m). Thus its cohomology map is the identity.

Every b in B has a unique finite homogeneous decomposition, by hgrading. Define
b acting on a finite family (x_m) by summing the images H^p(mu m k b_k)(x_m)
in degree m+k. The sum is finite. Additivity in both arguments follows from
additivity of the homogeneous decomposition and the maps above. The unit law
uses hunit and the identity map just established. For the product law expand the
two finite sums; hmul places b_k c_l in degree k+l and hmu_mul identifies its
map with the composite. This constructs a Module B structure, with the asserted
formula on homogeneous generators. That formula also determines the action
uniquely: every scalar and every vector is a finite sum of such generators.
No geometric finiteness assertion is used in this construction.
-/
theorem gradedCohomologyModuleStructure
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (p : ℕ) :
    ∃ mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u))),
      ∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x) := by
  classical
  let F := RingedSpace.moduleCohomology X.toRingedSpace p
  let H : ℕ → Type u := fun m ↦ F.obj (G m)
  let V := DirectSum ℕ H
  have : F.Additive := by
    dsimp [F, RingedSpace.moduleCohomology]
    infer_instance
  -- Extend each homogeneous operator to the direct sum by its universal property.
  let muAdd (m k : ℕ) : graded k →+ (G m ⟶ G (m + k)) :=
    { toFun := mu m k
      map_add' := hmu_add m k
      map_zero' := by
        apply add_left_cancel (a := mu m k 0)
        simpa only [add_zero] using (hmu_add m k 0 0).symm }
  let T (k : ℕ) : graded k →+ AddMonoid.End V :=
    { toFun := fun b ↦ DirectSum.toAddMonoid fun m ↦
        (DirectSum.of H (m + k)).comp (F.map (mu m k b)).hom.toAddMonoidHom
      map_zero' := by
        apply DirectSum.addHom_ext
        intro m x
        change (DirectSum.toAddMonoid (γ := V) _) (DirectSum.of H m x) = 0
        rw [DirectSum.toAddMonoid_of]
        change DirectSum.of H (m + k) (F.map (mu m k 0) x) = 0
        rw [show mu m k 0 = 0 from (muAdd m k).map_zero, F.map_zero]
        simp
      map_add' := by
        intro b c
        apply DirectSum.addHom_ext
        intro m x
        change (DirectSum.toAddMonoid (γ := V) _) (DirectSum.of H m x) =
          (DirectSum.toAddMonoid (γ := V) _) (DirectSum.of H m x) +
            (DirectSum.toAddMonoid (γ := V) _) (DirectSum.of H m x)
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
          DirectSum.toAddMonoid_of]
        change DirectSum.of H (m + k) (F.map (mu m k (b + c)) x) =
          DirectSum.of H (m + k) (F.map (mu m k b) x) +
            DirectSum.of H (m + k) (F.map (mu m k c) x)
        rw [hmu_add, F.map_add]
        exact map_add (DirectSum.of H (m + k)) _ _ }
  have hT (k m : ℕ) (b : graded k) (x : H m) :
      T k b (DirectSum.of H m x) = DirectSum.of H (m + k) (F.map (mu m k b) x) := by
    change (DirectSum.toAddMonoid (γ := V) _) (DirectSum.of H m x) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  -- The heterogeneous equalities of sheaf maps give ordinary equalities in the sum.
  have transport {m n n' : ℕ} (hn : n = n')
      {q : G m ⟶ G n} {q' : G m ⟶ G n'} (hq : HEq q q') (x : H m) :
      DirectSum.of H n (F.map q x) = DirectSum.of H n' (F.map q' x) := by
    subst n'
    cases hq
    rfl
  have sectionwise_id (m n : ℕ) (hn : n = m) (q : G m ⟶ G n)
      (hq : ∀ (U : X.Opens) (t : (G m).val.obj (op U)),
        HEq (q.val.app (op U) t) t) : HEq q (𝟙 (G m)) := by
    subst n
    apply heq_of_eq
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact eq_of_heq (hq U.unop t)
  have hTunit : T 0 ⟨1, hunit⟩ = 1 := by
    apply DirectSum.addHom_ext
    intro m x
    rw [hT]
    have hmu_one : HEq (mu m 0 ⟨1, hunit⟩) (𝟙 (G m)) := by
      apply sectionwise_id m (m + 0) (Nat.add_zero m)
      intro U t
      simpa only [map_one, one_smul] using hmu_scalar m 1 U t
    change DirectSum.of H (m + 0) (F.map (mu m 0 ⟨1, hunit⟩) x) =
      DirectSum.of H m x
    simpa only [F.map_id, ModuleCat.id_apply] using transport (Nat.add_zero m) hmu_one x
  have hTmul (k l : ℕ) (b : graded k) (c : graded l) :
      T (k + l) ⟨b.val * c.val, hmul k l b.property c.property⟩ = T k b * T l c := by
    apply DirectSum.addHom_ext
    intro m x
    change _ = T k b (T l c (DirectSum.of H m x))
    rw [hT, hT, hT]
    have hh := transport (by omega : m + l + k = m + (k + l))
      (hmu_mul m k l b c) x
    simpa only [F.map_comp, ModuleCat.comp_apply] using hh.symm
  -- The internal grading gives a canonical inverse to the sum of the inclusions.
  let e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap graded) hgrading).toAddEquiv
  let act : B →+ AddMonoid.End V := (DirectSum.toAddMonoid T).comp e.symm.toAddMonoidHom
  have he (k : ℕ) (b : graded k) : e (DirectSum.of (fun k ↦ graded k) k b) = b.val := by
    exact DirectSum.coeLinearMap_of graded k b
  have hact (k : ℕ) (b : graded k) : act b.val = T k b := by
    rw [← he k b]
    simp [act]
  -- Distributivity reduces arbitrary scalar products to homogeneous products.
  have hactmul (b c : B) : act (b * c) = act b * act c := by
    obtain ⟨b, rfl⟩ := e.surjective b
    obtain ⟨c, rfl⟩ := e.surjective c
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, add_mul, hb, hb']
    | of k b =>
      induction c using DirectSum.induction_on with
      | zero => simp
      | add c c' hc hc' => simp only [map_add, mul_add, hc, hc']
      | of l c =>
        rw [he, he]
        exact (hact (k + l) ⟨b.val * c.val, hmul k l b.property c.property⟩).trans
          ((hTmul k l b c).trans (by rw [hact, hact]))
  let ρ : B →+* AddMonoid.End V :=
    { act with
      map_one' := (hact 0 ⟨1, hunit⟩).trans hTunit
      map_mul' := hactmul }
  refine ⟨Module.compHom V ρ, ?_⟩
  intro k m b x
  change act b.val (DirectSum.of H m x) = _
  rw [hact]
  exact hT k m b x

end AlgebraicGeometry
