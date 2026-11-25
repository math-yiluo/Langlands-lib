/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
/-! # Local homogeneous generators of the algebra-module direct image

Source: Stacks Project, Tag 0897, finite-type paragraph, with Tags 03DA and 01B4.
(blueprint: lem-weil-pbc-graded-realization-local-generators-epi).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- Equality of morphisms over an open can be checked locally on each section. -/
private theorem over_hom_ext_of_locally_eq {X : Scheme.{u}}
    {R : X.toTopCat.Sheaf RingCat.{u}} {U : X.Opens}
    {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} (R.over U)}
    (p q : M.over U ⟶ N)
    (h : ∀ (V : Over U) (t : M.val.obj (op V.left)) (y : X), y ∈ V.left →
      ∃ (W : X.Opens) (hWV : W ≤ V.left), y ∈ W ∧
        let W' : Over U := Over.mk (homOfLE (hWV.trans V.hom.le))
        p.val.app (op W') (M.val.map (homOfLE hWV).op t) =
          q.val.app (op W') (M.val.map (homOfLE hWV).op t)) : p = q := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext t
  let S : Sieve V.unop := Presheaf.equalizerSieve (F := N.val.presheaf)
    (p.val.app V t) (q.val.app V t)
  have hcover : S ∈ (Opens.grothendieckTopology X).over U V.unop := by
    rw [GrothendieckTopology.mem_over_iff]
    intro y hy
    obtain ⟨W, hWV, hyW, ht⟩ := h V.unop t y hy
    let W' : Over U := Over.mk (homOfLE (hWV.trans V.unop.hom.le))
    let v : W' ⟶ V.unop := Over.homMk (homOfLE hWV)
    refine ⟨W, homOfLE hWV, ?_, hyW⟩
    rw [Sieve.overEquiv_iff]
    change N.val.presheaf.map v.op _ = N.val.presheaf.map v.op _
    erw [← PresheafOfModules.naturality_apply p.val,
      ← PresheafOfModules.naturality_apply q.val]
    exact ht
  exact N.isSheaf.isSeparated V.unop S hcover _ _ (fun W v hv ↦ hv)

/-- The specified finite homogeneous sections generate the algebra-module direct image
on a fixed open. This is purely a local generation statement: the morphism need not be
 affine and the module need not be quasi-coherent.

Source: Stacks Project, Tag 0897, finite-type paragraph; Modules on Sites, Tag 03DA;
Modules, Tag 01B4.
(blueprint: lem-weil-pbc-graded-realization-local-generators-epi).

Proof: Test epimorphy by comparing two algebra-linear maps p and q that agree after
composition with the specified free map. Evaluating their free-Hom equivalence shows
that they agree on every restricted basis section. Restriction to U is a left adjoint,
so preserves the given coproduct. Its universal property reduces equality to equality
on each restricted G_m, after restricting scalars from the direct-image algebra to O_X.
For a section t of G_m on V contained in U and a point y of V, hgen gives W containing y
where t restricts to the span of the homogeneous generators. Induct on this span.
For a generator, d_i + (m - d_i) = m resolves the HEq; compatibility identifies its
image with a scalar multiple of the image of s_i. The maps p and q are algebra-linear
and agree on the image of s_i, so agree on this multiple. Linearity handles zero,
addition and O_X-scalar multiplication. The equalizer sieve of the two images of t is
therefore covering. Separatedness of the target sheaf gives equality on V. Coproduct
uniqueness then gives equality of the restricted O_X-linear maps, hence of p and q.
This proves epi. Empty generating families and empty opens are included: span induction
and the covering condition require no nonemptiness assumption. -/
theorem gradedRealization_local_generators_epi
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    {X Y : Scheme.{u}} (pi : Y ⟶ X) (fB : Y ⟶ Spec (.of B))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (U : X.Opens) (r : ℕ) (d : Fin r → ℕ)
    (s : ∀ i : Fin r, (G (d i)).val.obj (op U))
    (hgen : ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
      (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
        (G m).val.map (homOfLE hWV).op t ∈
          Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
            {z | ∃ (i : Fin r), d i ≤ m ∧
              ∃ b : graded (m - d i),
                HEq z ((mu (d i) (m - d i) b).val.app (op W)
                  ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    (F : Y.Modules)
    (iota : ∀ m : ℕ, G m ⟶ (Scheme.Modules.pushforward pi).obj F)
    (hcoprod : Nonempty (IsColimit
      (Cofan.mk ((Scheme.Modules.pushforward pi).obj F) iota)))
    (hcompat : ∀ (k m : ℕ) (b : graded k),
      mu m k b ≫ iota (m + k) = iota m ≫
        (Scheme.Modules.pushforward pi).map
          (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val))) :
    let AR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf)
    let M := (SheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map pi.base)
      (S := AR) (R := Y.ringCatSheaf) (𝟙 AR)).obj F
    let a : ULift.{u} (Fin r) → (M.over U).sections := fun i ↦
      PresheafOfModules.sectionsMk
        (fun V ↦ M.val.presheaf.map V.unop.hom.op ((iota (d i.down)).val.app (op U) (s i.down)))
        (fun V W v ↦ by
          change M.val.presheaf.map v.unop.left.op _ = _
          rw [← Functor.map_comp_apply]
          rfl)
    Epi ((M.over U).freeHomEquiv.symm a) := by
  classical
  dsimp only
  let AR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf)
  let M := (SheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map pi.base)
    (S := AR) (R := Y.ringCatSheaf) (𝟙 AR)).obj F
  let a : ULift.{u} (Fin r) → (M.over U).sections := fun i ↦
    PresheafOfModules.sectionsMk
      (fun V ↦ M.val.presheaf.map V.unop.hom.op
        ((iota (d i.down)).val.app (op U) (s i.down)))
      (fun V W v ↦ by
        change M.val.presheaf.map v.unop.left.op _ = _
        rw [← Functor.map_comp_apply]
        rfl)
  change Epi ((M.over U).freeHomEquiv.symm a)
  let rho : X.ringCatSheaf ⟶ AR :=
    (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map ⟨pi.c⟩
  let O := SheafOfModules.overFunctor X.ringCatSheaf U
  let T := SheafOfModules.restrictScalars
    (((Over.forget U).sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X)).map rho)
  refine ⟨?_⟩
  intro N p q hpq
  have hbasis (i : Fin r) (V : (Over U)ᵒᵖ) :
      p.val.app V ((a ⟨i⟩).1 V) = q.val.app V ((a ⟨i⟩).1 V) := by
    have h := congrArg (fun z ↦ N.freeHomEquiv z (ULift.up i)) hpq
    simpa only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply,
      SheafOfModules.sectionsMap,
      PresheafOfModules.sectionsMap, PresheafOfModules.sectionsMk]
      using congrArg (fun z ↦ z.1 V) h
  have : O.IsLeftAdjoint := by
    dsimp [O, SheafOfModules.overFunctor]
    infer_instance
  have hcol := isColimitOfPreserves O hcoprod.some
  have heq : T.map p = T.map q := by
    apply hcol.hom_ext
    rintro ⟨m⟩
    apply over_hom_ext_of_locally_eq
    intro V t y hy
    obtain ⟨W, hWV, hyW, ht⟩ := hgen m V.left V.hom.le t y hy
    refine ⟨W, hWV, hyW, ?_⟩
    let W' : Over U := Over.mk (homOfLE (hWV.trans V.hom.le))
    let Lp := ((O.map (iota m)) ≫ T.map p).val.app (op W')
    let Lq := ((O.map (iota m)) ≫ T.map q).val.app (op W')
    change Lp ((G m).val.map (homOfLE hWV).op t) =
      Lq ((G m).val.map (homOfLE hWV).op t)
    refine LinearMap.eqOn_span (f := Lp.hom) (g := Lq.hom) ?_ ht
    intro z hz
    obtain ⟨i, hdi, b, hz⟩ := hz
    generalize hk : m - d i = k at b hz
    have hd : d i + k = m := by simpa only [hk] using Nat.add_sub_of_le hdi
    subst m
    have hz' := eq_of_heq hz
    subst z
    let si := (G (d i)).val.map
      (homOfLE (hWV.trans V.hom.le)).op (s i)
    have hc := congrArg (fun e ↦ e.val.app (op W) si) (hcompat k (d i) b)
    let c := (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val)
    change (iota (d i + k)).val.app (op W) ((mu (d i) k b).val.app (op W) si) =
      (F.smulHom c).app (pi ⁻¹ᵁ W) ((iota (d i)).val.app (op W) si) at hc
    rw [Scheme.Modules.smulHom_app_apply] at hc
    change p.val.app (op W') ((iota (d i + k)).val.app (op W) _) =
      q.val.app (op W') ((iota (d i + k)).val.app (op W) _)
    erw [hc]
    rw [(p.val.app (op W')).hom.map_smul, (q.val.app (op W')).hom.map_smul]
    congr 1
    have hi := PresheafOfModules.naturality_apply (iota (d i)).val
      (homOfLE (hWV.trans V.hom.le)).op (s i)
    exact (congrArg (p.val.app (op W')) hi).trans
      ((hbasis i (op W')).trans (congrArg (q.val.app (op W')) hi).symm)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext t
  exact congrArg (fun a ↦ (a.val.app V) t) heq

end AlgebraicGeometry
