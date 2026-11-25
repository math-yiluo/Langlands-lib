/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Postcomposition of sheaves with a lax braided functor is lax braided

For a lax braided functor `G : A ⥤ B` preserving sheaves, the postcomposition
`sheafCompose J G : Sheaf J A ⥤ Sheaf J B` is lax braided for the braidings of sheaves
`CategoryTheory.Sheaf.braidedCategory`: it is the sheafification of the postcomposition of the
underlying presheaves, a composite of lax braided functors.

## Main results

- `CategoryTheory.Functor.LaxBraided.whiskeringRight`: postcomposition of functors with a lax
  braided functor is lax braided.
- `CategoryTheory.sheafComposeLaxBraided`: postcomposition of sheaves with a lax braided functor
  is lax braided.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

/-- Postcomposition of functors with a lax braided functor `L` is lax braided, for the pointwise
braidings. -/
instance Functor.LaxBraided.whiskeringRight {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [MonoidalCategory D] [MonoidalCategory E] [BraidedCategory D]
    [BraidedCategory E] (L : D ⥤ E) [L.LaxBraided] :
    ((Functor.whiskeringRight C D E).obj L).LaxBraided where
  braided F G := by
    ext X
    exact Functor.LaxBraided.braided (F := L) (F.obj X) (G.obj X)

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxBraided]

/-- The postcomposition of sheaves with a lax braided functor is lax braided: it is the
sheafification of the postcomposition of the underlying presheaves. -/
noncomputable instance sheafComposeLaxBraided : (sheafCompose J G).LaxBraided :=
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)
  Functor.LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)

end CategoryTheory
