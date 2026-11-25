/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationCycles
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Evaluation for finite-free complexes with zero differentials

Source: Stacks Project, Tag 0BQY, the finite-free Hom calculation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem finiteFree_hom_preservesHomology
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u}) (r : ℕ)
    (M : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hM : M ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    [((SheafOfModules.homFunctor R).obj (op M)).PreservesZeroMorphisms] :
    ((SheafOfModules.homFunctor R).obj (op M)).PreservesHomology := by
  let H := (SheafOfModules.homFunctor R).obj (op M)
  let : H.Additive := ⟨by
    intro A B f g
    apply SheafOfModules.hom_ext
    ext U φ
    rfl⟩
  exact (Functor.exact_tfae H).out 1 3 |>.mp (by
    intro T hT
    obtain ⟨hz, hs, _⟩ := SheafOfModules.finiteFreeInternalHomExact (R := R) r M hM T hT
    exact hs)

/-- Evaluation for a bounded finite-free zero-differential complex is an isomorphism,
with its action on cycles expressed by two factorization identities.

Source: Stacks Project, Tag 0BQY, proof of Lemma 48.15.4, finite-free Hom calculation;
Tag 0A8X, the product-component definition of the Hom complex.
(blueprint: new-v4-finite-free-zero-homology-evaluation).

Proof: Put P = Hom(E,K), with the fixed product projections. Since E has zero
differentials, P is the product over p of factor complexes
with term Hom(E.X p,K.X(p+n)) in degree n and differential induced by d_K. Terms outside
the finite support of E contribute zero factors, so this is a finite product of
complexes. A chosen free basis of E.X p identifies its internal Hom functor with
the finite product of r copies of the identity functor. This functor is exact;
finite products are exact in an abelian category. Thus H^n(P) is the product of
Hom(E.X p,H^(p+n)(K)). Concentration of K removes every factor except p=-n.
The zero differential identifies E.cycles(-n), E.homology(-n), and E.X(-n).
The surviving product projection therefore induces f, an isomorphism.
The projection of a P-cycle evaluated on an E-cycle is a K-cycle: this follows
from the Hom differential formula and the zero differential of E. The kernel
property of K.iCycles gives c and the first identity. Passing to the homology
quotient of K gives the second identity, by the construction of f.
These identities determine f uniquely: homology class maps are locally surjective,
and equality of internal-Hom sections is checked on locally lifted cycle sections.
If -n is outside the support, the surviving factor is zero and both sides vanish.
Rank zero, the zero ring, and empty site objects obey the same calculation. -/
theorem finiteFreeZero_homologyEvaluation
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hK : ∀ k : ℤ, k ≠ 0 → IsZero (K.homology k))
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r)))) :
    let P := homComplex (R := R) E K
    let π := (Classical.choose (homComplex_projections_exists (R := R)))
      E K n (-n) 0 (by omega)
    ∃ f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0),
      IsIso f ∧ ∃ c : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0),
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π ≫ SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) ∧
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫ SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) := by
  dsimp
  obtain ⟨f, c, hc₁, hc₂⟩ := finiteFreeZero_homologyEvaluation_cycles R E K n hzero
  have hf := finiteFreeZero_homologyEvaluation_iso R E K n hK hzero hsupp hfree
    f c hc₁ hc₂
  exact ⟨f, hf, c, hc₁, hc₂⟩

end CategoryTheory
