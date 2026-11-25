/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionNormalFormChart
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization

/-! # Torsion normal form and its consecutive-quotient obstruction

## References

* Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8
* Stacks Tag 0ASV
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- On a finite stratum cover, each cohomology sheaf splits as a finite free sheaf
and a nilpotent-uniformizer torsion sheaf. The cokernel of the uniformizer on that
torsion sheaf is a quotient of a consecutive-quotient Tor sheaf. This is a normal-form
statement for arbitrary bounded constructible complete complexes; no Tor vanishing
or flatness of their cohomology is assumed. -/
theorem pbc_integral_cohomology_torsion_normal_form
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (q : ℤ) :
    let d := pbcIntegralDatum l E
    let B := pbcAdicCompletion T d
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K.obj))))
    ∃ (S : Stratification T)
      (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a)),
      ∀ (a : Fin S.n) (j : (V a).I₀),
        let g := (V a).f j ≫ S.immersion a
        let B' := (adicTowerInverseImage g).obj B
        let P := proEtaleRingModulePullback g B B' (Iso.refl _)
        ∃ (r : ℕ) (F N : pbcModules ((V a).X j) B'),
          (∀ U : ((V a).X j).ProEtᵒᵖ,
            Nonempty (Module.Basis (Fin r) (B'.obj.obj U) (F.val.obj U))) ∧
          Nonempty (P.obj ((DerivedCategory.homologyFunctor _ q).obj K.obj) ≅ F ⊞ N) ∧
          ∃ f : End N, IsNilpotent f ∧ ∃ n : ℕ,
            ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
                (pbcAdicProjection T d n))).obj
              ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
                ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
                (Iso.refl _)).obj (tor n)) ⟶ cokernel f.asHom,
              Epi t := by
  have hl' : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    simpa using (hl t)
  have hK := ((integralStratifiedPerfectCharacterization T l E hdim hl' K.obj).1).1 K.property
  obtain ⟨S, V, hch⟩ := IsIntegralStratifiedPerfect.exists_cover_charts T _ K.obj hK
  refine ⟨S, V, fun a j ↦ ?_⟩
  obtain ⟨C, hC, ⟨e⟩⟩ := hch a j
  exact torsion_normal_form_chart T l E _ K.obj q C hC e

end AlgebraicGeometry.Scheme
