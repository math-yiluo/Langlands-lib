import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Greenberg coefficient ring schemes

Let `R` be a local ring with residue field `k` and let `n` be a positive level. A
*Greenberg coefficient ring scheme* of level `n` is a functor `ℛ` from commutative
`k`-algebras to commutative `R`-algebras whose underlying sets are naturally the affine
spaces `Fin d → B`, whose `k`-points are `R ⧸ 𝔪ⁿ`, and which comes with a natural
reduction `ℛ(B) → B`, linear in the coordinates, with nilpotent kernel, such that
square-zero thickenings of `B` give nilpotent thickenings of `ℛ(B)`.

For a mixed-characteristic DVR with perfect residue field this is the truncated
Witt-vector ring scheme of Greenberg (KP §A.4); this file only records the interface used
to build Greenberg group schemes from it.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed

/-- **Greenberg coefficient ring scheme of level `n`.** A functor
`ℛ : CommAlgCat k ⥤ CommAlgCat R` (`k` the residue field of `R`) with

* natural coordinates `ℛ(B) ≃ (Fin dim → B)`, on which algebra maps act coordinatewise;
* an `R`-algebra isomorphism `ℛ(k) ≃ₐ[R] R ⧸ 𝔪ⁿ`;
* ring homomorphisms `red B : ℛ(B) → B`, given in coordinates by a fixed `k`-linear form,
  sending `algebraMap R (ℛ B) r` to the residue class of `r`, with nilpotent kernel;
* for every square-zero ideal `I` of `B`, the map `ℛ(B) → ℛ(B ⧸ I)` has nilpotent kernel. -/
structure GreenbergRingScheme (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ+) where
  /-- The coefficient ring functor `B ↦ ℛ(B)`. -/
  functor : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)) ⥤
    CommAlgCat.{u} (CommRingCat.of R)
  /-- The number of coordinates. -/
  dim : ℕ
  /-- The coordinates of `ℛ(B)`. -/
  coord : ∀ B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)),
    functor.obj B ≃ (Fin dim → B)
  /-- Algebra maps act on coordinates coordinatewise. -/
  coord_map : ∀ {B C : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R))}
    (f : B ⟶ C) (x : functor.obj B) (j : Fin dim),
    coord C ((functor.map f).hom x) j = f.hom (coord B x j)
  /-- The `k`-points of `ℛ` are the level-`n` congruence quotient `R ⧸ 𝔪ⁿ`. -/
  levelEquiv : functor.obj (CommAlgCat.of (CommRingCat.of (IsLocalRing.ResidueField R))
    (IsLocalRing.ResidueField R)) ≃ₐ[R] congruenceRing R n
  /-- The reduction homomorphism `ℛ(B) → B`. -/
  red : ∀ B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)),
    functor.obj B →+* B
  /-- The reduction is a fixed `k`-linear form in the coordinates. -/
  red_coord : ∃ c : Fin dim → IsLocalRing.ResidueField R,
    ∀ (B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R))) (x : functor.obj B),
      red B x = ∑ j, algebraMap (IsLocalRing.ResidueField R) B (c j) * coord B x j
  /-- The reduction sends the structure map of `R` to the residue map. -/
  red_algebraMap : ∀ (B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)))
    (r : R), red B (algebraMap R (functor.obj B) r) =
      algebraMap (IsLocalRing.ResidueField R) B (IsLocalRing.residue R r)
  /-- The kernel of the reduction is a nilpotent ideal. -/
  ker_red_nilpotent : ∀ B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)),
    IsNilpotent (RingHom.ker (red B))
  /-- Square-zero thickenings of coefficients give nilpotent thickenings of `ℛ`. -/
  ker_map_nilpotent : ∀ (B : CommAlgCat.{u} (CommRingCat.of (IsLocalRing.ResidueField R)))
    (I : Ideal B), I ^ 2 = ⊥ →
      IsNilpotent (RingHom.ker (functor.map (CommAlgCat.ofHom
        (Ideal.Quotient.mkₐ (CommRingCat.of (IsLocalRing.ResidueField R)) I))).hom)

end Langlands.GroupScheme.IntegralModel.GreenbergMixed
