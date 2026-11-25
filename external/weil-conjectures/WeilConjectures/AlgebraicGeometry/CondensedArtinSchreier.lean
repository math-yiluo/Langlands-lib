/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-! # Artin–Schreier sheaves with condensed coefficients

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/
def-fd-artin-schreier-sheaf.md, condensed-coefficients paragraph
(blueprint: lemma-artin-schreier-character-sheaf--1).

These are the image projector and ordinary module pullback on the pro-etale site.
The scalar ring is the ring of global sections of the condensed coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]

/-- The pushforward of the regular coefficient module along the degree-cardinality
Artin–Schreier map. Source: current blueprint, def-fd-artin-schreier-sheaf.md,
condensed-coefficients paragraph (blueprint: lemma-artin-schreier-character-sheaf--1). -/
def condensedArtinSchreierPushforward :=
  (CondensedRing.lowerStar Λ
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).obj
      (Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of k)))))

/-- Pullback of sections by a deck translation, defined by the adjunction unit,
identification of the pulled-back regular module, and composition of pushforwards.
Source: current blueprint, def-fd-artin-schreier-sheaf.md, translation action
(blueprint: lemma-artin-schreier-character-sheaf--1). -/
def condensedArtinSchreierTranslationAction (a : k) :
    End (condensedArtinSchreierPushforward Λ k) :=
  End.of <| (CondensedRing.lowerStar Λ
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
      (((CondensedRing.upperStarLowerStarAdjunction Λ
        (Etale.artinSchreierTranslation k a)).homEquiv _ _)
          (Functor.Monoidal.εIso
            (CondensedRing.upperStar Λ (Etale.artinSchreierTranslation k a))).inv) ≫
    (CondensedRing.lowerStarComp Λ (Etale.artinSchreierTranslation k a)
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).hom.app _ ≫
    eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj
      (Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of k))))))
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a))

/-- The character projector, with coefficient multiplication transported from the point.
`Ring.inverse q` is the inverse of the unit `q` in the coefficient ring, as required
in the source; the expression itself is also defined without invertibility.
Source: current blueprint, def-fd-artin-schreier-sheaf.md, displayed projector
(blueprint: lemma-artin-schreier-character-sheaf--1). -/
def condensedArtinSchreierProjector (ψ : AddChar k (MonObj.Γ Λ)) :
    End (condensedArtinSchreierPushforward Λ k) :=
  ∑ a : k, End.of ((condensedArtinSchreierTranslationAction Λ k a).asHom ≫
    (CondensedRing.lowerStar Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom
            (upperStarFromPoint (AffineSpace PUnit (Spec (.of k))))
            (Ring.inverse (Fintype.card k : MonObj.Γ Λ) * ψ (-a)))).asHom)

/-- The condensed Artin–Schreier sheaf is the actual image of its character projector.
Source: current blueprint, def-fd-artin-schreier-sheaf.md, condensed-coefficients paragraph
(blueprint: lemma-artin-schreier-character-sheaf--1). -/
def condensedArtinSchreierSheaf (ψ : AddChar k (MonObj.Γ Λ)) :=
  image ((condensedArtinSchreierProjector Λ k ψ)).asHom

/-- The Artin–Schreier sheaf of a global function is the ordinary pullback of the
character image along the morphism defined by that function. This is a module over
`p_X^* Λ`, including for the empty scheme.
Source: current blueprint, def-fd-artin-schreier-sheaf.md, definition of L_{psi,f}
(blueprint: lemma-artin-schreier-character-sheaf--1). -/
def condensedArtinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)) :=
  (CondensedRing.upperStar Λ
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)).obj
      (condensedArtinSchreierSheaf Λ k ψ)

end AlgebraicGeometry.ProEtale
