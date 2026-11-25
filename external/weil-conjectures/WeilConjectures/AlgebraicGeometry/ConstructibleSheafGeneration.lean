/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.AlgebraicGeometry.AffineEtaleRankOneSeparating

/-!
# Constructible module sheaves generate the small etale topos

Source: Stacks Project, Tags 093B(2), 03EW(3), 03SA(3) and 03S8(3)
(blueprint: lem-weil-pbc-constructible-generation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every module sheaf on the small etale site of a quasi-compact quasi-separated scheme
is a quotient of a coproduct of constructible module sheaves, for finite commutative
coefficients. Source: Stacks Project, Tags 093B(2), 03EW(3) and 03S8(3)
(blueprint: lem-weil-pbc-constructible-generation).

Proof:
1. Choose a small covering family of affine etale objects
   (`lem-weil-pbc-affine-etale-essentially-small-cover`). The extensions by zero of the
   constant rank-one module sheaves form a separating family: their coproduct is a
   separator (`lem-weil-pbc-module-sheaves-grothendieck-abelian`). Small coproducts exist
   by `situation-conventions`.
2. Index summands by pairs consisting of an object of this covering family and a map
   from its extension by zero to `F`. The map from their coproduct to `F` is epic by
   `lem-weil-pbc-separating-family-epi-coproduct` (Stacks 03EW(3)).
3. Each affine source is quasi-compact and quasi-separated. Its extension by zero of
   the finite module `Λ` is constructible by `lem-weil-pbc-etale-free-sheaf-constructible`
   (Stacks 03S8(3)); this uses the quasi-compact quasi-separated hypothesis on `X`.
4. Take these extensions as the family `C`. Step 3 gives constructibility of every
   summand and step 2 gives the required epimorphism from the existing coproduct.
-/
theorem exists_epi_coproduct_constructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (I : Type (u + 1)) (C : I → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ i : I, IsConstructibleEtaleModuleSheaf (C i)) ∧
        ∃ (_ : HasCoproduct C) (π : ∐ C ⟶ F), Epi π := by
  classical
  let B := { U : X.Etale // IsAffine U.left }
  let G : B → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun U ↦
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) U.val.hom inferInstance).obj
      ((constantSheaf U.val.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  have hG : ObjectProperty.IsSeparating (.ofObj G) :=
    affine_etale_rankOne_isSeparating X Λ
  let I := Σ b : B, G b ⟶ F
  let C : I → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun i ↦ G i.1
  have hC (i : I) : IsConstructibleEtaleModuleSheaf (C i) := by
    let U := i.1
    let : IsAffine U.val.left := U.property
    exact isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := X) (U := U.val.left) U.val.hom (ModuleCat.of Λ Λ)
  let : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    GrothendieckTopology.hasSheafify_smallEtaleTopology _ X
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    Sheaf.instHasColimitsOfSize
  have hcop : HasCoproduct C := inferInstance
  let π : ∐ C ⟶ F := Sigma.desc (fun i : I ↦ i.2)
  have hπ : Epi π := by
    constructor
    intro Z f g h
    apply hG f g
    intro Y hY a
    obtain ⟨b, rfl⟩ := (ObjectProperty.ofObj_iff G Y).mp hY
    have hh := congrArg (fun q ↦ Sigma.ι C ⟨b, a⟩ ≫ q) h
    simpa [π, Category.assoc] using hh
  exact ⟨I, C, hC, hcop, π, hπ⟩

end AlgebraicGeometry.Scheme
