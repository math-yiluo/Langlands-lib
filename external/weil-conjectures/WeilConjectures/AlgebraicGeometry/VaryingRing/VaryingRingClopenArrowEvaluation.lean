/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowFactors
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOpenBaseChangeEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenSectionEvaluation

/-!
# Coefficient realization of the clopen inverse-image arrow

Source: Stacks Project, Tag 0F7B, open case; Zheng, Construction 4.1 and Lemma 4.10.
The comparison is made for the exact inverse-image/open-extension arrow, before taking
proper-adjunction mates (blueprint: lem-sp-varying-ring-clopen-arrow-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The two factors of the clopen arrow have a common coefficient realization.
Source: Stacks 0F7B, open case
(blueprint: lem-sp-varying-ring-clopen-arrow-evaluation).
Proof: compose the coefficient realization of cartesian open base change with
that of the clopen section factor. Functoriality of evaluation and associativity
identify their composite with alpha, using exact localization of composition. -/
theorem clopenArrowEvaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (n : ℕ) :
    ∃ a : (StrictTower.moduleJ (R n) i).mapDerivedCategory ⋙
          (StrictTower.modulePullback (R n) p).mapDerivedCategory ⟶
        (StrictTower.modulePullback (R n) r).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) k).mapDerivedCategory,
      (∀ N : Derived R φ S,
        (ev R φ W n).map ((alpha R φ k r p i h).app N) ≫
            (evalJ R φ k n).hom.app ((G R φ r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((evalG R φ r n).hom.app N) =
          (evalG R φ p n).hom.app ((J R φ i).obj N) ≫
            (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
              ((evalJ R φ i n).hom.app N) ≫ a.app ((ev R φ S n).obj N)) ∧
      (∀ N : StrictTower.Derived (R n) S,
        (StrictTower.ev (R n) W 0).map ((StrictTower.alpha (R n) k r p i h).app N) ≫
            (StrictTower.evalJ (R n) k 0).hom.app ((StrictTower.G (R n) r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((StrictTower.evalG (R n) r 0).hom.app N) =
          (StrictTower.evalG (R n) p 0).hom.app ((StrictTower.J (R n) i).obj N) ≫
            (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
              ((StrictTower.evalJ (R n) i 0).hom.app N) ≫
            a.app ((StrictTower.ev (R n) S 0).obj N)) := by
  obtain ⟨b, hb, hbs⟩ := openBaseChangeEvaluation R φ
    (pullback.fst p i) (pullback.snd p i) p i
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip n
  obtain ⟨c, hc, hcs⟩ := clopenSectionEvaluation R φ k r p i h n
  refine ⟨b ≫ c, ?_, ?_⟩
  · intro N
    rw [alpha_factorization]
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [(hc N), reassoc_of% (hb N)]
  · intro N
    rw [strictAlpha_factorization]
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [(hcs N), reassoc_of% (hbs N)]

end AlgebraicGeometry.ProEtale.VaryingRing
