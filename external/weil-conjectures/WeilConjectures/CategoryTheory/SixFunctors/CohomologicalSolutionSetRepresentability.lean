/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # The solution-set criterion for cohomological representability

Source: Krause, *Localization theory for triangulated categories*, Theorem 5.1.1,
and the cofiber/kernel-killing argument in Stacks Project, Tag 0A8F.
(blueprint: lem-sfb-cohomological-solution-set-representability)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C]

private theorem coproduct_element
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {I : Type v} (A : I → C) (a : ∀ i, H.obj (op (A i))) :
    ∃ x : H.obj (op (∐ A)), ∀ i, H.map (Sigma.ι A i).op x = a i := by
  have := hH I
  let F := H ⋙ forget AddCommGrpCat
  let c := (Cofan.mk (∐ A) (Sigma.ι A)).op
  have hc : IsLimit (F.mapCone c) :=
    isLimitOfPreserves F (Cofan.IsColimit.op (coproductIsCoproduct A))
  let s : ∀ i : Discrete I, (Discrete.functor (fun i ↦ op (A i)) ⋙ F).obj i :=
    fun i ↦ a i.as
  have hs : s ∈ (Discrete.functor (fun i ↦ op (A i)) ⋙ F).sections := by
    intro i j f
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain rfl := Discrete.eq_of_hom f
    simp
  obtain ⟨x, hx, _⟩ := (Types.isLimit_iff _).1 ⟨hc⟩ s hs
  exact ⟨x, fun i ↦ hx ⟨i⟩⟩

private theorem coproduct_element_zero
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {I : Type v} (A : I → C) (x : H.obj (op (∐ A)))
    (hx : ∀ i, H.map (Sigma.ι A i).op x = 0) : x = 0 := by
  have := hH I
  let F := H ⋙ forget AddCommGrpCat
  let c := (Cofan.mk (∐ A) (Sigma.ι A)).op
  have hc : IsLimit (F.mapCone c) :=
    isLimitOfPreserves F (Cofan.IsColimit.op (coproductIsCoproduct A))
  apply (Types.isLimitEquivSections hc).injective
  apply Subtype.ext
  funext i
  change H.map (Sigma.ι A i.as).op x = H.map (Sigma.ι A i.as).op 0
  rw [hx, map_zero]

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsIdempotentComplete C]

/-- A cohomological functor with a small solution set is representable.

Source: Krause, *Localization theory for triangulated categories*, Theorem 5.1.1,
final solution-set argument; Stacks Project, Tag 0A8F, kernel-killing argument.
(blueprint: lem-sfb-cohomological-solution-set-representability)

Proof: Take the coproduct of the solution objects and lift their distinguished
values using preservation of products. Its value x is weakly universal. Form the
coproduct of all endomorphisms f of this object G for which H(f)(x)=0, and take the
cofiber p:G→Y of the evaluation map. Exactness lifts x to y in H(Y). Weak universality
gives s:Y→G with H(s)(x)=y. Every kernel endomorphism is killed by p; applying this
to ps-id gives psp=p. For an arbitrary f:Z→G in the kernel, lift x to its cofiber
and map that pair to (G,x). The resulting endomorphism q has H(q)(x)=x and fq=0.
Since (q-id)p=0, fp=fqp=0. Hence e=ps is idempotent and kills all kernels, while
H(e)(x)=x. Split e as i:E→G and r:G→E. The element H(i)(x) gives bijections
Hom(Z,E)→H(Z): a lift f:Z→G maps to fr, and injectivity follows by applying the
kernel-annihilation assertion to the difference of the two maps composed with i.
These bijections are natural because they are induced by a single element.
-/
theorem cohomological_isRepresentable_of_solutionSet
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    (hsol : ∃ (I : Type v) (A : I → C) (a : ∀ i, H.obj (op (A i))),
      ∀ (Z : C) (z : H.obj (op Z)), ∃ (i : I) (f : Z ⟶ A i), H.map f.op (a i) = z) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  classical
  obtain ⟨I, A, a, ha⟩ := hsol
  obtain ⟨x, hx⟩ := coproduct_element H hH A a
  let G := ∐ A
  have hsurj (Z : C) (z : H.obj (op Z)) : ∃ f : Z ⟶ G, H.map f.op x = z := by
    obtain ⟨i, f, hf⟩ := ha Z z
    refine ⟨f ≫ Sigma.ι A i, ?_⟩
    rw [op_comp, H.map_comp, AddCommGrpCat.comp_apply, hx]
    exact hf
  let K := {f : G ⟶ G // H.map f.op x = 0}
  let B : K → C := fun _ ↦ G
  let κ : (∐ B) ⟶ G := Sigma.desc fun f ↦ f.val
  have hκ : H.map κ.op x = 0 := by
    apply coproduct_element_zero H hH B
    intro f
    rw [← AddCommGrpCat.comp_apply, ← H.map_comp, ← op_comp]
    simpa only [κ, Sigma.ι_comp_desc] using f.property
  obtain ⟨Y, p, δ, hT⟩ := distinguished_cocone_triangle κ
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    (H.map_distinguished_op_exact (Triangle.mk κ p δ) hT) x hκ
  change H.map p.op y = x at hy
  have hkill (f : G ⟶ G) (hf : H.map f.op x = 0) : f ≫ p = 0 := by
    have h := comp_distTriang_mor_zero₁₂ (Triangle.mk κ p δ) hT
    have hi := congrArg (fun z ↦ Sigma.ι B ⟨f, hf⟩ ≫ z) h
    simpa [κ] using hi
  obtain ⟨s, hs⟩ := hsurj Y y
  have hps : H.map (p ≫ s).op x = x := by
    simpa only [op_comp, H.map_comp, AddCommGrpCat.comp_apply, hs] using hy
  have hpsp : p ≫ s ≫ p = p := by
    have h : H.map (p ≫ s - 𝟙 G).op x = 0 := by
      rw [op_sub, H.map_sub]
      change H.map (p ≫ s).op x - H.map (𝟙 G).op x = 0
      rw [hps]
      simp
    have h := hkill _ h
    simpa only [Preadditive.sub_comp, Category.id_comp, sub_eq_zero, Category.assoc] using h
  have hkernel {Z : C} (f : Z ⟶ G) (hf : H.map f.op x = 0) : f ≫ p = 0 := by
    obtain ⟨W, q, ε, hU⟩ := distinguished_cocone_triangle f
    obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).1
      (H.map_distinguished_op_exact (Triangle.mk f q ε) hU) x hf
    change H.map q.op w = x at hw
    obtain ⟨t, ht⟩ := hsurj W w
    have hqt : H.map (q ≫ t - 𝟙 G).op x = 0 := by
      rw [op_sub, H.map_sub]
      change H.map (q ≫ t).op x - H.map (𝟙 G).op x = 0
      simp only [op_comp, H.map_comp, AddCommGrpCat.comp_apply, ht, hw]
      simp
    have hqp : (q ≫ t) ≫ p = p := by
      simpa only [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] using hkill _ hqt
    have hfq : f ≫ q = 0 := comp_distTriang_mor_zero₁₂ (Triangle.mk f q ε) hU
    rw [← hqp, ← Category.assoc, ← Category.assoc, hfq, zero_comp, zero_comp]
  have he : (p ≫ s) ≫ (p ≫ s) = p ≫ s := by
    rw [Category.assoc, ← Category.assoc s, ← Category.assoc p, hpsp]
  obtain ⟨E, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split G (p ≫ s) he
  let e : H.obj (op E) := H.map i.op x
  have hbij (Z : C) : Function.Bijective (fun f : Z ⟶ E ↦ H.map f.op e) := by
    constructor
    · intro f g hfg
      have hk : H.map ((f - g) ≫ i).op x = 0 := by
        rw [op_comp, H.map_comp]
        change H.map (f - g).op e = 0
        rw [op_sub, H.map_sub]
        exact sub_eq_zero.mpr hfg
      have hk' : (f - g) ≫ i ≫ (p ≫ s) = 0 := by
        simpa only [Category.assoc, zero_comp] using
          congrArg (fun z ↦ z ≫ s) (hkernel _ hk)
      have hie : i ≫ (p ≫ s) = i := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
      simp only [hie] at hk'
      have h' := congrArg (fun z ↦ z ≫ r) hk'
      simpa only [Category.assoc, hir, Category.comp_id, zero_comp, sub_eq_zero] using h'
    · intro z
      obtain ⟨f, hf⟩ := hsurj Z z
      refine ⟨f ≫ r, ?_⟩
      calc
        H.map (f ≫ r).op e = H.map f.op (H.map (r ≫ i).op x) := by simp [e]
        _ = z := by rw [hri, hps, hf]
  exact (Functor.RepresentableBy.isRepresentable
    { homEquiv := fun {Z} ↦ Equiv.ofBijective _ (hbij Z)
      homEquiv_comp := fun f g ↦ by
        change H.map (f ≫ g).op e = H.map f.op (H.map g.op e)
        simp })

end CategoryTheory
