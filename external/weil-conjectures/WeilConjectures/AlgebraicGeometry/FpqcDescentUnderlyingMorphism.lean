/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDescentDataCategory
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-! Auxiliary steps for Stacks Project, Descent, Lemma 0241. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

private theorem transport_left_of_eq {S X : Scheme.{u}} {a : X ⟶ S}
    {V : Over X} (D : Over.DescentDatum a V) {T : Scheme.{u}}
    {f g : T ⟶ X} (hfg : f = g) (h : f ≫ a = g ≫ a) (z : Over.mk f ⟶ V) :
    (D.transport f g h z).left = z.left := by
  subst g
  rw [D.transport_self]

/-- Underlying morphisms of pulled-back descent data descend uniquely over X.
Source: Stacks Project, Descent, Lemma 0241, overlap argument and Lemma 02W0.
(blueprint: lem-galois-fpqc-descent-underlying-morphism).

Proof: Pull the fpqc singleton back along A.V.hom using its chosen cartesian square.
Fpqc subcanonicality makes q A an effective epimorphism. For two test-scheme maps
with equal composites through q A, base-change compatibility, transport along equal
base points, and the cartesian-square universal property identify their transport.
Compatibility of β with transport then gives the descent equation for β.hom.left ≫ q B.
EffectiveEpi.desc supplies the underlying map and its reconstruction equation.
Cancel q A to show the map is over X and to prove uniqueness. -/
theorem fpqc_descent_underlying_morphism
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X)
    (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
    (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left)
    (hq : ∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
      IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
      Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum)
    (A B : Over.DescentDataCategory a) (β : F.obj A ⟶ F.obj B) :
    ∃! α : A.V ⟶ B.V, q A ≫ α.left = β.hom.left ≫ q B := by
  obtain ⟨hqA, hPA, bcA⟩ := hq A
  obtain ⟨hqB, _, bcB⟩ := hq B
  have hcover : Presieve.singleton (q A) ∈ Scheme.fpqcPrecoverage A.V.left := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hr ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ r) hr A.V.hom
      (fun _ ↦ q A) (fun _ ↦ (F.obj A).V.hom) (fun _ ↦ hPA)
  let : EffectiveEpi (q A) := by
    rw [← Sieve.effectiveEpimorphic_singleton,
      Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro Z
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hcover)
  have he : ∀ {T : Scheme.{u}} (g₁ g₂ : T ⟶ (F.obj A).V.left),
      g₁ ≫ q A = g₂ ≫ q A →
      g₁ ≫ (β.hom.left ≫ q B) = g₂ ≫ (β.hom.left ≫ q B) := by
    intro T g₁ g₂ hg
    let f₁ := g₁ ≫ (F.obj A).V.hom
    let f₂ := g₂ ≫ (F.obj A).V.hom
    have hfr : f₁ ≫ r = f₂ ≫ r := by
      dsimp [f₁, f₂]
      simp only [Category.assoc, ← hqA]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ A.V.hom) hg
    have hf : f₁ ≫ (r ≫ a) = f₂ ≫ (r ≫ a) := by
      simpa only [← Category.assoc] using congrArg (fun k ↦ k ≫ a) hfr
    let z : Over.mk f₁ ⟶ (F.obj A).V := Over.homMk g₁ rfl
    have hz : ((F.obj A).datum.transport f₁ f₂ hf z).left = g₂ := by
      apply hPA.hom_ext
      · have hh := bcA f₁ f₂ hf z
        rw [transport_left_of_eq A.datum hfr] at hh
        simpa [z] using hh.symm.trans hg
      · exact Over.w _
    have hh := bcB f₁ f₂ hf (z ≫ β.hom)
    have hc := congrArg (fun k ↦ k.left ≫ q B) (β.commutes f₁ f₂ hf z)
    change _ = (((F.obj A).datum.transport f₁ f₂ hf z).left ≫ β.hom.left) ≫ q B at hc
    rw [hz] at hc
    have hi : (B.datum.transport (f₁ ≫ r) (f₂ ≫ r)
        (by simpa only [Category.assoc] using hf)
        (Over.homMk ((z ≫ β.hom).left ≫ q B) (by simp [hqB]))).left =
        (z ≫ β.hom).left ≫ q B := by
      exact transport_left_of_eq B.datum hfr _ _
    rw [hi] at hh
    exact (by simpa [z] using hh.trans hc)
  let α := EffectiveEpi.desc (q A) (β.hom.left ≫ q B) he
  have hα : q A ≫ α = β.hom.left ≫ q B := EffectiveEpi.fac _ _ he
  have hαX : α ≫ B.V.hom = A.V.hom := by
    apply (cancel_epi (q A)).mp
    rw [← Category.assoc, hα, Category.assoc, hqB]
    simpa only [← Category.assoc, Over.w β.hom] using hqA.symm
  refine ⟨Over.homMk α hαX, hα, ?_⟩
  intro γ hγ
  apply Over.OverMorphism.ext
  exact (cancel_epi (q A)).mp (hγ.trans hα.symm)

end CategoryTheory
