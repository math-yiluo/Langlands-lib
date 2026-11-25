/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteSupportCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenCounitSectionLifting
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Lifting finite support through a smaller open

## References

* Stacks Project, Tags 00WK and 09AE
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale
open Scheme

/-- Finite local support descends to one compact open in the base. Restrict the
ambient sheaf along the weakly etale localization, refine the covering to finitely
many affine representatives, and enclose their nonzero images in a compact open.
Pull back the covering to the localized site. The open counit is monic and locally
surjective on these representatives, so their lifts glue uniquely. -/
theorem finiteSupport_lifting (R : Type (u + 1)) [Ring R]
    {X Y T : Scheme.{u}} (r : Y ⟶ X) [WeaklyEtale r] (p : Y ⟶ T)
    (Q : Y.ProEt) [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
    (U : T.Opens) (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))
    (s : N.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale r)).obj Q)))
    (S : Sieve ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale r)).obj Q))
    (hS : S ∈ ProEt.topology X _)
    (h : ∀ (Z : X.ProEt) (f : Z ⟶ _), S f →
      Set.range (f.left ≫ Q.hom ≫ p) ⊆ U ∨ N.obj.map f.op s = 0) :
    ∃ (O : T.Opens), IsCompact (O : Set T) ∧ O ≤ U ∧
      ∃ t : ((openImmersionLowerShriek (ModuleCat.{u + 1} R)
        (pullback.fst p O.ι)).obj
          ((openImmersionRestriction (ModuleCat.{u + 1} R)
            (pullback.fst p O.ι)).obj
              ((localizationRestriction (ModuleCat.{u + 1} R) r inferInstance).obj N))).obj.obj
                (op Q),
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R)
          (pullback.fst p O.ι)).counit.app
            ((localizationRestriction (ModuleCat.{u + 1} R) r inferInstance).obj N)).hom.app
              (op Q) t = s := by
  classical
  let L := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale r)
  have : CompactSpace (L.obj Q).left := inferInstanceAs (CompactSpace Q.left)
  have : QuasiSeparatedSpace (L.obj Q).left :=
    inferInstanceAs (QuasiSeparatedSpace Q.left)
  obtain ⟨O, hOc, hOU, I, hI, Z, f, hf, hfi⟩ :=
    ProEt.finiteSupportCover R (L.obj Q) (Q.hom ≫ p) U N s S hS h
  refine ⟨O, hOc, hOU, ?_⟩
  let G := (localizationRestriction (ModuleCat.{u + 1} R) r inferInstance).obj N
  have hcov : (Sieve.ofArrows Z f).functorPullback L ∈ ProEt.topology Y Q :=
    L.cover_lift (ProEt.topology Y) (ProEt.topology X) hf
  apply openCounit_section_lift R (pullback.fst p O.ι) G Q s _ hcov
  intro Z' g hg
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff Z f (L.map g)).mp hg
  rcases hfi i with hi | hi
  · left
    have hZ : Set.range (Z'.hom ≫ p) ⊆ O := by
      intro x hx
      obtain ⟨z, rfl⟩ := hx
      have he : g.left ≫ Q.hom = Z'.hom := MorphismProperty.Over.w g
      have ha' : a.left ≫ (f i).left = g.left :=
        congrArg (fun t ↦ t.left) ha.symm
      have hw : a.left ≫ (f i).left ≫ Q.hom ≫ p = Z'.hom ≫ p := by
        rw [← Category.assoc a.left, ha', ← Category.assoc, he]
      rw [← hw]
      exact hi ⟨a.left z, rfl⟩
    let l : Z'.left ⟶ O.toScheme := IsOpenImmersion.lift O.ι (Z'.hom ≫ p)
      (fun x hx ↦ ⟨⟨x, hZ hx⟩, rfl⟩)
    refine ⟨pullback.lift Z'.hom l
      (IsOpenImmersion.lift_fac O.ι (Z'.hom ≫ p) _).symm, ?_⟩
    exact pullback.lift_fst _ _ _
  · right
    change N.obj.map (L.map g).op s = 0
    rw [ha, op_comp, Functor.map_comp]
    change N.obj.map a.op (N.obj.map (f i).op s) = 0
    rw [hi]
    exact map_zero (N.obj.map a.op).hom

end AlgebraicGeometry.ProEtale
