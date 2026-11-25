/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# The contracted product of a torsor under change of coefficients

Source: Stacks Project, Cohomology on Sites, Tag 03AH (torsors);
blueprint pushout-fibre argument (blueprint: def-sc-contracted-product-presentation).
-/

@[expose] public section

universe uQ wQ

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf.Torsor

/-- A presentation of `T ∧ᴳ G'` as the sheaf quotient of `T × G'` by
`g • (t, h) = (g +ᵥ t, h - φ(g))`. The natural quotient map is invariant under that action
and equivariant for translation on the second factor. Its universal property against every
sheaf of sets is exactly the universal property of the sheafification of the orbit presheaf.
Source: Stacks, Tag 03AH (torsors); the blueprint's pushout-fibre quotient argument.
(blueprint: def-sc-contracted-product-presentation) -/
structure ContractedProductPresentation (S : AlgebraicGeometry.Scheme.{uQ})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uQ wQ + 1}} (φ : G ⟶ G')
    (T : Torsor G) (T' : Torsor G') where
  quotient (U : S.Etaleᵒᵖ) : T.sheaf.obj.obj U → G'.obj.obj U → T'.sheaf.obj.obj U
  quotient_natural {U V : S.Etaleᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U) :
    T'.sheaf.obj.map f (quotient U t h) =
      quotient V (T.sheaf.obj.map f t) (G'.obj.map f h)
  quotient_invariant (U : S.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U) :
    quotient U (T.vadd U g t) (h - φ.hom.app U g) = quotient U t h
  quotient_vadd (U : S.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) (h k : G'.obj.obj U) :
    quotient U t (h + k) = T'.vadd U k (quotient U t h)
  universal (F : Sheaf S.smallEtaleTopology (Type (max uQ wQ + 1)))
      (a : ∀ U : S.Etaleᵒᵖ, T.sheaf.obj.obj U → G'.obj.obj U → F.obj.obj U)
      (hn : ∀ ⦃U V : S.Etaleᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U)
        (h : G'.obj.obj U), F.obj.map f (a U t h) =
          a V (T.sheaf.obj.map f t) (G'.obj.map f h))
      (hi : ∀ (U : S.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U)
        (h : G'.obj.obj U), a U (T.vadd U g t) (h - φ.hom.app U g) = a U t h) :
    ∃! l : T'.sheaf ⟶ F, ∀ (U : S.Etaleᵒᵖ) (t : T.sheaf.obj.obj U)
      (h : G'.obj.obj U), l.hom.app U (quotient U t h) = a U t h

end CategoryTheory.Sheaf.Torsor
