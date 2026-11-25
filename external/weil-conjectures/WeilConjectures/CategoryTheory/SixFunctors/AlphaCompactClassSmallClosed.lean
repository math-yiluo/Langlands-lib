/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactExtensions
import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactFactorThrough
import WeilConjectures.CategoryTheory.SixFunctors.SmallBoundedTriangulatedHull

/-! # Krause's maximal alpha-compact class identification -/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Krause's maximal alpha-compact class is small and extension closed when
there is a small shift-closed perfect generating class of alpha-small objects.

Source: Krause, On Neeman's Well Generated Triangulated Categories (2001),
Lemma 5, pages 124--125; Localization theory, Sections 6.2--6.3.
(blueprint: new-sfb-alpha-compact-class-small-closed)

Proof in words: first show that the maximal alpha-compact class S is extension
closed. Take its finite extension hull. The alpha-small API preserves support
smallness along this construction. Coproduct factorization propagates across
cones by factoring the first restriction, lifting it through coproducts of fiber
triangles, and correcting the resulting cone map by a factorization from the
shifted preceding vertex. The finite extension hull therefore satisfies G4 and
is alpha-small, so maximality puts it back inside S. Together with the existing
shift and zero APIs, this makes S triangulated. The existing bounded-coproduct
API makes S closed under coproducts of fewer than alpha inputs. The hypotheses
on G exhibit G as a subclass of S.

Construct a small triangulated hull H of G inside S, closed under those bounded
coproducts. At each stage adjoin shifts, middle vertices of distinguished
triangles, and bounded coproducts, and take isomorphism closure. Include zero
and every earlier stage. Each operation preserves essential smallness by the
proved size API. Iterate through the initial ordinal of alpha; its index type
is v-small, so the union is essentially v-small. Regularity bounds the stages
of fewer than alpha inputs strictly below a single later stage. Thus this
union has all the required closure properties and stays inside S.

Let R consist of targets Y such that every map X to Y with X in S factors
through an object of H. It contains H, and is closed under isomorphisms and
shifts. For coproduct closure, G4 first factors component maps through objects
of S; membership in R factors those maps through H. Alpha-smallness restricts
the assembled map to fewer than alpha summands, whose coproduct belongs to H.
For cone closure, factor the connecting map through H0 in H and take its fiber
X'. Extension closure puts X' in S. Factor the lift from X' to the preceding
vertex through H1 in H. Complete the square to a cone H2 of H0[-1] to H1.
The discrepancy factors through H0, so the original map factors through the
binary sum of H2 and H0, an object of H. Thus R is localizing. The assumed
generation property makes R all of C. Factoring each identity shows that S
lies in the retract closure of H. Mathlib proves that retract closure preserves
essential smallness, and essential smallness passes to subclasses. The
extension closure proved at the beginning supplies the second conjunct.

Reference: https://ftp.gwdg.de/pub/misc/EMIS/journals/DMJDMV/vol-06/07.pdf,
Lemma 5 and its proof.
-/
theorem alphaCompactObjects_small_closed
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{v} C]
    (G : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} G]
    [G.IsStableUnderShift ℤ] (α : Cardinal.{v}) [Fact α.IsRegular]
    (hGsmall : ∀ X, G X → IsAlphaSmall X α)
    (hGfactor : G.IsCoproductFactorizationClass)
    (hGgen : ∀ (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated],
      (∀ (I : Type v) (Y : I → C), (∀ i, S (Y i)) → S (∐ Y)) →
      G ≤ S → ∀ X, S X) :
    ObjectProperty.EssentiallySmall.{v} (alphaCompactObjects C α) ∧
      (alphaCompactObjects C α).IsTriangulatedClosed₂ := by
  let := HasZeroObject.zero' C
  let S := alphaCompactObjects C α
  have : S.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X hX ↦ hX.shift n⟩⟩
  have : S.ContainsZero := ⟨0, Limits.isZero_zero C, isAlphaCompact_zero α⟩
  have hclosed : S.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    IsAlphaCompact.extension α T hT h₁ h₃)
  have : S.IsTriangulated := {}
  have hGS : G ≤ S := fun X hX ↦ ⟨G, hX, hGsmall, hGfactor⟩
  have hsum (I : Type v) (Y : I → C) (hI : HasCardinalLT I α)
      (hY : ∀ i, S (Y i)) : S (∐ Y) := IsAlphaCompact.coproduct α I Y hI hY
  obtain ⟨H, hsmall, hiso, htri, hGH, hHS, hHsum⟩ :=
    exists_small_bounded_triangulated_hull G S α hGS hsum
  have : ObjectProperty.EssentiallySmall.{v} H := hsmall
  have : H.IsClosedUnderIsomorphisms := hiso
  have : H.IsTriangulated := htri
  exact ⟨ObjectProperty.EssentiallySmall.of_le
    (alphaCompactObjects_le_retractClosure α G H hHS hHsum hGH hGgen), hclosed⟩

end CategoryTheory
