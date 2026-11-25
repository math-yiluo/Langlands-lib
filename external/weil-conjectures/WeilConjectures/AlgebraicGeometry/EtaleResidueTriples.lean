/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Étale algebras with a prime and a residue-field embedding

Source: Stacks Project, Tag 04HX, first paragraph of the proof
(blueprint: proposition-proper-base-change-projective-line--1).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Stacks, Tag 04HX (blueprint: proposition-proper-base-change-projective-line--1).
A triple consists of an étale map `A → B`, a prime `q` over `p`, and an embedding
`κ(q) → K` compatible with the fixed map `κ(p) → K`. Compatibility on `A` is equivalent
to compatibility on `κ(p)`, since residue fields are fraction fields of the quotients. -/
structure EtaleResidueTriple (A : CommRingCat.{u}) (p : Spec A)
    (K : Type u) [Field K] (χ : (Spec A).residueField p ⟶ CommRingCat.of K) where
  B : CommRingCat.{u}
  α : A ⟶ B
  etale : Etale (Spec.map α)
  q : Spec B
  over : Spec.map α q = p
  φ : (Spec B).residueField q ⟶ CommRingCat.of K
  compatible : α ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ =
    (ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ χ

/-- Stacks, Tag 04HX (blueprint: proposition-proper-base-change-projective-line--1).
Forget the prime and residue-field factorization, retaining the factorization `A → B → K`. -/
def EtaleResidueTriple.factorization {A : CommRingCat.{u}} {p : Spec A}
    {K : Type u} [Field K] {χ : (Spec A).residueField p ⟶ CommRingCat.of K}
    (t : EtaleResidueTriple A p K χ) :
    Under (Over.mk ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ χ)) :=
  Under.mk (Over.homMk (V := Over.mk
    ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)) t.α t.compatible)

/-- Stacks, Tag 04HX (blueprint: proposition-proper-base-change-projective-line--1).
The category of triples, with morphisms the `A`-ring maps commuting with their maps to `K`.
This is equivalent to inverse-image equality of primes and commutation on residue fields:
the kernel of `B → κ(q) → K` is `q`, and residue-field factorization is unique. -/
abbrev EtaleResidueTriples (A : CommRingCat.{u}) (p : Spec A)
    (K : Type u) [Field K] (χ : (Spec A).residueField p ⟶ CommRingCat.of K) :=
  InducedCategory (Under (Over.mk ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation p ≫ χ)))
    (EtaleResidueTriple.factorization (A := A) (p := p))

/-- Stacks, Tag 04HX (blueprint: proposition-proper-base-change-projective-line--1).
The ring diagram sending a triple to its ring `B` and a morphism to its underlying ring map. -/
def etaleResidueTriplesRingDiagram (A : CommRingCat.{u}) (p : Spec A)
    (K : Type u) [Field K] (χ : (Spec A).residueField p ⟶ CommRingCat.of K) :
    EtaleResidueTriples A p K χ ⥤ CommRingCat.{u} :=
  inducedFunctor _ ⋙ Under.forget _ ⋙ Over.forget _

end AlgebraicGeometry.Scheme
