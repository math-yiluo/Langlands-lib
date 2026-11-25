/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DirectedPerfectHomIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PerfectHomContinuity

/-! # Transport of perfect Hom continuity through pinned Hom equivalences

Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-perfect-hom-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
  [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (Z : Scheme.{u}) (U : Z.Opens),
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
  (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
  (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
  (O : Bool → D) (G : ∀ k, C k ⥤ D)
  (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)

/-- A geometric presentation of the stage Hom sets and their actual limit images.
The equations pin the Hom equivalences to the given functors and comparisons.
This structure asserts no lifting, eventual equality, or stage transport.
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-perfect-hom-presentation). -/
structure PerfectHomPresentation where
  Y : Scheme.{u}
  s : Y ⟶ Spec (R.obj i)
  lfp : LocallyOfFinitePresentation s
  qc : QuasiCompact s
  qs : QuasiSeparated s
  P : Bool → schemeDerivedCategory Y
  perfect : ∀ b, Y.IsPerfect (P b)
  stage : ∀ (k : Set.Ici i) (a b : Bool), (F k a ⟶ F k b) ≃
    ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
        (P a) ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
        (P b))
  apex : ∀ a b, (O a ⟶ O b) ≃
    ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (P a) ⟶
      (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (P b))
  stage_id : ∀ k a, stage k a a (𝟙 (F k a)) = 𝟙 _
  stage_comp : ∀ k a b d (f : F k a ⟶ F k b) (g : F k b ⟶ F k d),
    stage k a d (f ≫ g) = stage k a b f ≫ stage k b d g
  pin : ∀ k a b (f : F k a ⟶ F k b),
    apex a b ((ψ k a).inv ≫ (G k).map f ≫ (ψ k b).hom) =
      perfectLimitMap R c s k.property (stage k a b f)

variable {R c i C F D O G ψ}

/-- A pinned presentation transfers the existing perfect Hom continuity theorem.
Source: Stacks Project, Tag 09RE, Hom-colimit isomorphism, and Tag 0D5S.
(blueprint: lem-pc-perfect-hom-presentation).

Proof: transport a stage morphism into the presented geometric Hom set, apply
canonical derived-pullback transport, and transport back. Preservation of identity
and composition follows from the stage equivalences and the pullback functor laws.
The pinning equation and the composition comparison show that the limit image is
unchanged. Apply perfect Hom continuity to each ordered pair of the two perfect
objects. Its surjectivity gives a lift, which is transported back through the stage
and apex equivalences. Its eventual equality clause gives equality of the two
transported morphisms at every later stage; injectivity of the stage equivalence
then gives the required equality in the original categories. -/
theorem PerfectHomPresentation.toSystem
    (p : PerfectHomPresentation R c i C F D O G ψ) (hc : IsColimit c) :
    Nonempty (DirectedPerfectHomSystem (Set.Ici i) C F D O G ψ) := by
  classical
  have : LocallyOfFinitePresentation p.s := p.lfp
  have : QuasiCompact p.s := p.qc
  have : QuasiSeparated p.s := p.qs
  let tr : ∀ {k l : Set.Ici i}, k ≤ l → ∀ {a b : Bool},
      (F k a ⟶ F k b) → (F l a ⟶ F l b) :=
    fun {k l} hkl {a b} f ↦
      (p.stage l a b).symm (perfectStageMap R p.s k.property hkl (p.stage k a b f))
  refine ⟨?_⟩
  refine
    { transport := tr
      transport_id := ?_
      transport_comp := ?_
      limit_transport := ?_
      lift := ?_
      equal := ?_ }
  · intro k l hkl a
    apply (p.stage l a a).injective
    simp only [tr, Equiv.apply_symm_apply, p.stage_id, perfectStageMap_id]
    rfl
  · intro k l hkl a b d f g
    apply (p.stage l a d).injective
    simp only [tr, Equiv.apply_symm_apply, p.stage_comp]
    exact perfectHomMap_comp _ _ _ _
  · intro k l hkl a b f
    apply (p.apex a b).injective
    rw [p.pin, p.pin]
    simp only [tr, Equiv.apply_symm_apply]
    exact perfectLimitMap_stage R c p.s k.property hkl (p.stage k a b f)
  · intro a b f
    obtain ⟨k, hik, fk, hk⟩ :=
      (perfect_hom_continuity R c hc i p.Y p.s (p.P a) (p.P b)
        (p.perfect a) (p.perfect b)).1 i le_rfl (p.apex a b f)
    refine ⟨⟨k, hik⟩, (p.stage ⟨k, hik⟩ a b).symm fk, (p.apex a b).injective ?_⟩
    simpa only [p.pin, Equiv.apply_symm_apply] using hk
  · intro k a b f g hfg
    have he : perfectLimitMap R c p.s k.property (p.stage k a b f) =
        perfectLimitMap R c p.s k.property (p.stage k a b g) := by
      rw [← p.pin, ← p.pin, hfg]
    obtain ⟨l, hkl, hl⟩ :=
      (perfect_hom_continuity R c hc i p.Y p.s (p.P a) (p.P b)
        (p.perfect a) (p.perfect b)).2 k.val k.property
          (p.stage k a b f) (p.stage k a b g) he
    refine ⟨⟨l, k.property.trans hkl⟩, hkl, ?_⟩
    intro m hlm
    apply (p.stage m a b).injective
    simpa only [tr, Equiv.apply_symm_apply] using hl m.val hlm

end AlgebraicGeometry
