/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.CategoryTheory.CartanEilenbergConeFiltrationData
import WeilConjectures.CategoryTheory.CartanEilenbergConeFiltrationProperties
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # The complex-degree filtration on an augmentation cone

Source: Stacks Project, Homology, Tag 0133, Lemma
`lemma-double-complex-gives-resolution`, and Tag 012W, Lemma
`lemma-biregular-ss-converges`.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration).
-/

@[expose] public section

universe uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The cone of the specified diagonal augmentation has a degreewise finite
complex-degree filtration. Its graded cohomology is the cohomology of the
extended column augmentation cones. No exactness assumption is made here.
Source: Stacks Project, Homology, Tag 0133, Lemma
`lemma-double-complex-gives-resolution`, the canonical augmentation and the
finite-diagonal filtration, with Tag 012W for the degreewise bounds.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration).

Proof.
1. Write J for the identity-mapped, extended and flipped bicomplex. The cone
in degree n is K^(n+1) plus the diagonal coproduct of J in degree n.
Put its K^(n+1) summand in complex degree n+1, and put the diagonal summand
I^(s,r), where s+r=n, in complex degree s. Define the step p to be the
sum of the images of precisely the summands with complex degree at least p.
This is an actual subobject construction from the cone biproduct inclusions
and diagonal coprojections, not a choice of a filtered model up to isomorphism.
2. The cone differential is minus d_K on the K summands, the total differential
on the I summands, and aug on the off-diagonal block. Each preserves or raises
complex degree. The specified equation haug puts the off-diagonal block into
complex degree n+1, so it too preserves the filtration. The resulting lifts
through the monic step inclusions are unique. They square to zero because the
cone differential does, giving subcomplexes and an antitone subobject filtration.
3. For n fixed, all I summands have b <= s <= n, and the only additional summand
is K^(n+1), which is zero if n+1 < b. Thus step b is the whole cone object and
step n+2 is zero, including empty diagonals. These are the required degreewise
finite bounds. No common global upper bound for the filtration is claimed.
4. In the quotient of step p by step p+1 all summands except complex degree p
disappear. What remains is the column I^(p,bullet), extended by zero, augmented
by K^p in resolution degree -1. The off-diagonal differential is exactly
(a.f p).f 0, using haug and the extension identifications. The differentials
raising complex degree vanish in this quotient. Its short complex in degree n
is therefore isomorphic to the short complex in degree n-p of the mapping cone
of extendMap (a.f p), with its negative-degree zero terms. This gives the
claimed homology isomorphism. Alternatively identify the entire graded complex
with that column cone shifted by -p, removing the shift differential sign by
the degreewise factors (-1)^(p*(n-p)). The identity functor's component
identifications remove the harmless identity-mapping wrapper on I.
This construction also applies to a zero column, a zero bicomplex, and all
integers p,n; no quasi-isomorphism hypothesis is used. -/
theorem cartanEilenberg_cone_filtration
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n)) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone aug),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n))) ∧
      (∀ n : ℤ, F.complexStep b n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      ∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).homology
            (n - p)) := by
  obtain ⟨F, hF⟩ := cartanEilenberg_cone_filtration_data K I a b hIbelow hKbelow aug haug
  obtain ⟨hbounds, hgraded⟩ := cartanEilenberg_cone_filtration_properties
    K I a b hIbelow hKbelow aug haug F hF
  exact ⟨F, hF, hbounds, hgraded⟩

end CategoryTheory.Functor
