/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization

/-! # Maps from affine limits to affine étale objects

Source: Stacks Project, Tags 01ZC and 099S, finite presentation and affine limits.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Affine étale objects are finitely copresentable for affine inverse systems,
including systems whose index lies in a larger universe.

Source: Stacks Project, limits.tex, Proposition 32.6.1 (Tag 01ZC), and proetale.tex,
lemma-limit-pullback (Tag 099S)
(auxiliary; not a blueprint node).

Proof: forget the system to schemes over X. The affine stages have affine transition
maps, and their limit has the stated universal property in schemes over X. A map
from the limit to V descends to a stage because V -> X is locally of finite
presentation. On affine charts this follows by lifting finitely many algebra
generators and then killing finitely many relations at a common stage. A finite
affine cover of the quasi-compact source reduces the arbitrary-base assertion to
this affine calculation; the overlap equations descend by the same finite
generation argument. Two stage maps agreeing on the limit agree after refinement,
by the finite-type equality argument of Tag 01ZC. Neither argument bounds the
cardinality of the index: only finitely many indices and arrows are selected at
each step. Thus the restriction cocone on Hom(-, V) is jointly surjective and
has eventual equality, so it is a filtered colimit of sets. Taking opposites of
the arrows identifies it with the coyoneda image of the opposite cone. That cone
is a colimit by reflection of the original limit through the fully faithful
forgetful functor. Preservation of this colimit cocone gives the assertion.
The empty affine scheme is allowed; the index is nonempty by cofilteredness. -/
theorem affineEtale_largeLimit_preservesColimit {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ X.ProEt) (haff : ∀ i, IsAffine (D.obj i).left)
    (het : ∀ i, Etale (D.obj i).hom) (c : Cone D)
    (hc : IsLimit ((Scheme.ProEt.forget X).mapCone c))
    (V : X.ProEt) [IsAffine V.left] [Etale V.hom] :
    PreservesColimit D.op (coyoneda.obj (op (op V))) := by
  have hlim : IsLimit c := isLimitOfReflects (Scheme.ProEt.forget X) hc
  apply preservesColimit_of_preserves_colimit_cocone hlim.op
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    obtain ⟨i, b, hb⟩ := affineEtale_largeLimit_factorization D haff het c hc V a.unop
    exact ⟨op i, b.op, congrArg Quiver.Hom.op hb.symm⟩
  · intro i a b hab
    obtain ⟨k, f, hf⟩ := affineEtale_largeLimit_eventualEquality D haff het c hc V
      i.unop a.unop b.unop (congrArg Quiver.Hom.unop hab)
    exact ⟨op k, f.op, congrArg Quiver.Hom.op hf⟩

end AlgebraicGeometry.ProEtale
