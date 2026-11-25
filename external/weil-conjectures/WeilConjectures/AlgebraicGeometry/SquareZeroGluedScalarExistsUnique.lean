/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The quotient action on a square-zero ideal

Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by local lifts gives a uniquely determined section of the kernel.
Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of its proof.
(blueprint: lem-sc-square-zero-glued-scalar-exists-unique)

Proof: Choose a cover of U and lifts b_a of f using local surjectivity of p.
The products b_a*i(x|V_a) agree on intersections: the difference of two lifts
is killed by p, as is i(x), so their product is zero by square-zero. Glue the
products in B to a section z. Naturality and separatedness in C show p(z)=0.
Evaluation preserves exactness at B for this short exact sequence, since i
is mono and evaluation preserves kernels. Thus z has a preimage y in I(U).
For any other lift b on V, restrict to the cover V intersect V_a and repeat
the difference-of-lifts calculation; separatedness in B proves the required
formula on V. Two candidate sections have the same image in B on the lifting
cover, hence globally by separatedness; sectionwise injectivity of i gives
uniqueness. The gluing and separatedness APIs include empty covers, so the
empty open and the zero sheaf require no exceptions. This constructs only
one scalar-action section; linearity, ring laws and restriction compatibility
of an operator family are not asserted here. -/
theorem square_zero_glued_scalar_exists_unique (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∀ (U : X.Opens) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
      ∃! y : I.val.obj (op U),
        ∀ (V : X.Opens) (j : V ⟶ U) (b : B.right.obj.obj (op V)),
          p.right.hom.app (op V) b = C.right.obj.map j.op f →
            @id (B.right.obj.obj (op V))
              (i.val.app (op V) (I.val.map j.op y)) =
                b * @id (B.right.obj.obj (op V))
                  (i.val.app (op V) (I.val.map j.op x)) := by
  classical
  let q := (commAlgebraSheafModuleFunctor X.sheaf).map p
  have : Mono i := hS.mono_f
  have : Epi q := hS.epi_g
  have inj (V : X.Opens) : Function.Injective (i.val.app (op V)) := by
    let E := SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op V)
    exact (ModuleCat.mono_iff_injective (E.map i)).mp inferInstance
  have pn {V W : X.Opens} (j : V ⟶ W) (b : B.right.obj.obj (op W)) :
      p.right.hom.app (op V) (B.right.obj.map j.op b) =
        C.right.obj.map j.op (p.right.hom.app (op W) b) := by
    exact congrArg (fun m ↦ m b) (p.right.hom.naturality j.op)
  have inat {V W : X.Opens} (j : V ⟶ W) (x : I.val.obj (op W)) :
      i.val.app (op V) (I.val.map j.op x) =
        B.right.obj.map j.op (i.val.app (op W) x) := by
    exact congrArg (fun m ↦ m x) (i.val.naturality j.op)
  have iz (V : X.Opens) (x : I.val.obj (op V)) :
      p.right.hom.app (op V) (i.val.app (op V) x) = 0 := by
    exact congrArg (fun m : I ⟶ commAlgebraSheafModule X.sheaf C ↦
      m.val.app (op V) x) hw
  have independent (V : X.Opens) (b c t : B.right.obj.obj (op V))
      (hbc : p.right.hom.app (op V) b = p.right.hom.app (op V) c)
      (ht : p.right.hom.app (op V) t = 0) : b * t = c * t := by
    have hz := hsq V (b - c) t (by simp only [map_sub, hbc, sub_self]) ht
    exact sub_eq_zero.mp (by simpa only [sub_mul] using hz)
  intro U f x
  obtain ⟨A, V, hV, b, hcover, hb⟩ :=
    ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1
      (commAlgebraSheafModule X.sheaf B)
      (commAlgebraSheafModule X.sheaf C) q).2.mpr inferInstance U f
  change (a : A) → B.right.obj.obj (op (V a)) at b
  change ∀ a, p.right.hom.app (op (V a)) (b a) =
    C.right.obj.map (homOfLE (hV a)).op f at hb
  let t : ∀ a, B.right.obj.obj (op (V a)) := fun a ↦
    b a * @id (B.right.obj.obj (op (V a)))
      (i.val.app (op (V a)) (I.val.map (homOfLE (hV a)).op x))
  have ht : TopCat.Presheaf.IsCompatible B.right.obj V t := by
    intro a c
    dsimp [t]
    rw [map_mul, map_mul, inat, inat]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    apply independent
    · rw [pn, pn, hb, hb]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    · change p.right.hom.app (op (V a ⊓ V c))
        (B.right.obj.map (homOfLE (inf_le_left.trans (hV a))).op
          (i.val.app (op U) x)) = 0
      rw [pn, iz, map_zero]
  obtain ⟨z, hz, _⟩ := TopCat.Sheaf.existsUnique_gluing' B.right V U
    (fun a ↦ homOfLE (hV a)) (by rw [hcover]) t ht
  have pz : p.right.hom.app (op U) z = 0 := by
    apply TopCat.Sheaf.eq_of_locally_eq' C.right V U
      (fun a ↦ homOfLE (hV a)) (by rw [hcover])
    intro a
    rw [← pn, hz]
    dsimp [t]
    rw [map_mul, iz, mul_zero, map_zero]
  let E := SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op U)
  have : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  have he := hS.exact.map_of_mono_of_preservesKernel E inferInstance inferInstance
  obtain ⟨y, hy⟩ := ((ShortComplex.mk i q hw).map E).moduleCat_exact_iff.mp he z pz
  change i.val.app (op U) y = z at hy
  have prop : ∀ (W : X.Opens) (j : W ⟶ U) (c : B.right.obj.obj (op W)),
      p.right.hom.app (op W) c = C.right.obj.map j.op f →
      i.val.app (op W) (I.val.map j.op y) =
        c * @id (B.right.obj.obj (op W)) (i.val.app (op W) (I.val.map j.op x)) := by
    intro W j c hc
    rw [inat, hy]
    let T : A → X.Opens := fun a ↦ W ⊓ V a
    have hT : W ≤ ⨆ a, T a := by
      intro w hw
      have hwU := j.le hw
      rw [← hcover] at hwU
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hwU
      exact Opens.mem_iSup.mpr ⟨a, hw, ha⟩
    apply TopCat.Sheaf.eq_of_locally_eq' B.right T W
      (fun a ↦ homOfLE inf_le_left) hT
    intro a
    rw [map_mul, inat]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hz' : B.right.obj.map (homOfLE (inf_le_right : T a ≤ V a)).op
        (B.right.obj.map (homOfLE (hV a)).op z) =
        B.right.obj.map (homOfLE (inf_le_right : T a ≤ V a)).op (t a) :=
      congrArg (B.right.obj.map (homOfLE inf_le_right).op) (hz a)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hz'
    rw [show (homOfLE (hV a)).op ≫
        (homOfLE (inf_le_right : T a ≤ V a)).op =
        j.op ≫ (homOfLE (inf_le_left : T a ≤ W)).op from Subsingleton.elim _ _] at hz'
    rw [hz']
    dsimp [t]
    rw [map_mul, inat]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    apply independent
    · rw [pn, pn, hb, hc]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    · change p.right.hom.app (op (T a))
        (B.right.obj.map (homOfLE (inf_le_right.trans (hV a))).op
          (i.val.app (op U) x)) = 0
      rw [pn, iz, map_zero]
  refine ⟨y, prop, ?_⟩
  intro y' hy'
  apply inj U
  apply TopCat.Sheaf.eq_of_locally_eq' B.right V U
    (fun a ↦ homOfLE (hV a)) (by rw [hcover])
  intro a
  rw [← inat, ← inat]
  exact (hy' _ _ (b a) (hb a)).trans (prop _ _ (b a) (hb a)).symm

end AlgebraicGeometry
