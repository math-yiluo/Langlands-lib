/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore

/-! # A common module presentation for compact generation and exact localization

Source: Stacks Project, Tags 0F5V, 0F5X, and 05NU for the size extension.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

set_option linter.style.haveILetI false

/-- The Gabriel--Popescu abelian presentation and the compact triangulated source use
one and the same module category, linked by a triangulated equivalence.
Source: Stacks Project, Tags 0F5V and 0F5X (first paragraph), with Baer criterion 05NU.
(auxiliary; not a blueprint node)

Proof in words: choose a separator G of A. Shrink End(G) to universe w using local
smallness, and take its opposite ring S for left modules. Hom(G,-) gives U. Construct
F on a module M as the cokernel in A of the map between coproducts of G specified by
the canonical free presentation of M. This construction represents Hom(M,U(-)), giving
the adjunction. For modules of size w, Gabriel--Popescu gives exactness and the
invertible counit. For larger modules, first obtain large coproducts in A: a coproduct
P of A_i[0] in D(A) lies in D≤0, since its Hom into each Y in D≥1 is a product of zero
groups. Truncation then identifies Hom(P,X[0]) with Hom(H⁰(P),X), so H⁰(P) is the
coproduct of the A_i. The free presentation therefore constructs F at the required
size. Its counit agrees with the small construction. For an injective I in A, U(I)
is injective among small modules; Baer criterion tests ideals of the w-sized ring,
so it remains injective among the larger modules. Adjunction and enough injectives
then imply that F preserves monomorphisms. Being a left adjoint it is right exact,
so it is additive and exact. Choose the small-Hom derived category of modules by
its Grothendieck construction. The free rank-one module in degree zero is compact:
Hom from its shifts is cohomology, which commutes with direct sums. Vanishing of
all these groups detects zero objects, proving compact generation. Lift the object
universe of this very derived module category to the displayed universe and
transport the triangulated structure, shifts, coproducts and compact generation
along its equivalence e. The functor e is exact. No derived adjoint or derived
counit assertion is included in this presentation theorem. -/
theorem grothendieckDerived_gabriel_popescu_presentation
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (S : Type w) (rS : Ring S),
      letI := rS
      ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
      letI := hD
      ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
        (adj₀ : F ⊣ U) (addF : F.Additive)
        (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
      letI := addF
      letI := limF
      letI := colimF
      IsIso adj₀.counit ∧
      ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B ∧
      ∃ (e : B ≌ DerivedCategory (ModuleCat.{max w vH} S))
        (se : e.functor.CommShift ℤ),
      letI := se
      e.functor.IsTriangulated := by
  have hcore :
      ∃ (S : Type w) (rS : Ring S),
        letI := rS
        ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
        letI := hD
        ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
          (adj₀ : F ⊣ U) (addF : F.Additive)
          (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
        let _ := addF
        let _ := limF
        let _ := colimF
        IsIso adj₀.counit := by
    exact gabriel_popescu_abelian_core (A := A)
  obtain ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc⟩ := hcore
  letI := rS
  letI := hD
  letI := addF
  letI := limF
  letI := colimF
  refine ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc, ?_⟩
  exact compact_derived_source_core (A := A) (S := S)

end CategoryTheory
