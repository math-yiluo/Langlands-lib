/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantMapOpenFactorization

/-! # Extending a stalk factorization of a finite constant map

Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A map from a finitely generated constant module sheaf that factors through a
subsheaf at one geometric stalk factors on a Zariski neighbourhood of that point.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
(blueprint: lem-weil-pbc-finite-constant-map-open-factorization).

Proof: Choose finitely many generators of N. Represent the images of these generators
under the stalk factorization by sections of F on a common pointed etale neighbourhood.
Refine this neighbourhood until their images under phi equal the sections of G obtained
from alpha and the corresponding constant generators. Equality of finitely many germs
is witnessed after a common refinement. The image U of this etale neighbourhood is
open and contains x. On its fibre product over U the two lifts of each generator have
the same image in G, namely the pullback of alpha of that constant generator. Monicity
of phi makes the lifts equal. Sheaf descent produces sections of F on U. Every relation
among the generators maps to zero in G since alpha is linear; monicity makes it zero
in F. Hence these sections define a linear map N to sections of the pullback of F.
The constant-sheaf/global-sections adjunction gives psi, and its composite with the
pullback of phi is the pullback of alpha, as is checked on the generators. The stalk
of the open restriction is the original stalk. No finite presentation of N is needed:
monicity kills all relations on the same U. For N=0 take the zero map and U=X. Neither
X nor G is required to be irreducible, Noetherian, finite, or constant. -/
theorem exists_open_factorization_of_finite_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N]
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (U : X.Opens) (_hU : x ∈ U)
      (ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
      ψ ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map α := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' Λ N
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Q := ModuleCat.of Λ (Fin n → Λ)
  let q' : Q ⟶ N := ModuleCat.ofHom q
  have : Epi q' := (ModuleCat.epi_iff_surjective q').mpr hq
  let S := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  obtain ⟨U, hU, β, hβ⟩ := exists_open_factorization_of_finite_free_constant_map
    φ n (C.map q' ≫ α) x (S.map (C.map q') ≫ l) (by
      rw [Category.assoc, hl, S.map_comp])
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι
  have : Epi (C.map q') := by infer_instance
  have : Epi (P.map (C.map q')) := by infer_instance
  have : StrongEpi (P.map (C.map q')) := strongEpi_of_epi _
  let sq : CommSq β (P.map (C.map q')) (P.map φ) (P.map α) :=
    ⟨by simpa only [Functor.map_comp] using hβ⟩
  exact ⟨U, hU, sq.lift, sq.fac_right⟩

end AlgebraicGeometry.Scheme
