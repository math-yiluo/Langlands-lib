/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.NormalizedGenericDataWithFactorization
import WeilConjectures.AlgebraicGeometry.NormalizedGenericDataLifts

/-!
# Normalized generic trivialization data

Source: Stacks Project, Tag 09Z6, generic trivialization and normalization, using Tag 09Z5.
(blueprint: lem-weil-pbc-constructible-module-normalized-generic-data).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Generic trivialization on an integral model, together with lifting of geometric points.

Source: Stacks Project, Tag 09Z6 (lemma-constructible-maps-into-constant), proof
of (1), the paragraph from the reduced closure through the generic inclusion, transferred
to (3); Tag 09Z5 (lemma-push-constant-sheaf-from-open).
(blueprint: lem-weil-pbc-constructible-module-normalized-generic-data).

Proof: Restrict the constructible sheaf to the residue field at x. Constructibility is
preserved by inverse image, using finite-value locally constant trivializations. Over this
field choose a finite separable extension K and a finite module M trivializing the sheaf.
Normalize the reduced closure of x in K to obtain an integral morphism nu from a normal
integral Y, with generic inclusion g from Spec K. The inverse-image composition comparison
and the pullback comparison for constant sheaves identify g^* nu^* F with g^* M_Y. The
normal constant generic-point theorem 09Z5 identifies the unit at M_Y as an isomorphism.
To apply its canonical-generic-inclusion formulation to g, factor g through the spectrum
of the residue field of its image. The residue-field map is an isomorphism by the
normalization theorem. At the generic point the local ring is a field, so its quotient
map to the residue field is an isomorphism too. Thus g differs from the canonical
Spec-of-the-generic-stalk inclusion by an isomorphism of source schemes. Inverse-image
composition and the units of the composite adjunction transport the unit isomorphism
along this source isomorphism.
For each algebraically closed Omega and geometric point s above x, its residue-field map
extends to K because K is algebraic over the residue field. Applying Spec gives w, and
the residue-field description of s and contravariant functoriality of Spec give
w followed by g and nu equal to s. The field extension used here is finite and therefore
algebraic; no finiteness of the normalization over X is asserted. If the base is empty there is no
x; the zero sheaf yields M = 0. No adjoint map out of F is constructed here. -/
theorem exists_constructible_module_normalized_generic_data
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
        (M : ModuleCat.{u + 1} Λ), Finite M ∧
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        Nonempty
          ((upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
           (upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
          ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
            ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s := by
  obtain ⟨Y, ν, hν, K, hK, g, M, hM, hu, he, a, ha, hcomp⟩ :=
    exists_constructible_module_normalized_generic_data_with_factorization Λ F hF x
  refine ⟨Y, ν, hν, K, hK, g, M, hM, hu, he, ?_⟩
  exact normalized_generic_data_lifts Λ F hF x Y ν hν K hK g a ha hcomp M hM hu he

end AlgebraicGeometry.Etale
