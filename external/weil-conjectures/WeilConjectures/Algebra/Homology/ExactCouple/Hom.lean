/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Basic

/-!
# Morphisms of exact couples

A morphism of exact couples consists of morphisms `D i ⟶ D' i` and `E i ⟶ E' i` compatible with
the structure maps. It induces a morphism of the derived couples, hence of all the iterated
derived couples, and a morphism of the spectral sequences
(`CategoryTheory.ExactCouple.Hom.spectralSequenceMap`).

## Main definitions

- `CategoryTheory.ExactCouple.Hom`: morphisms of exact couples.
- `CategoryTheory.ExactCouple.Hom.derived`: the induced morphism of derived couples.
- `CategoryTheory.ExactCouple.Hom.spectralSequenceMap`: the induced morphism of spectral
  sequences.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type w} [AddCommGroup κ] {a b c : κ}

/-- A *morphism of exact couples* `X ⟶ Y`: morphisms `τD : X.D i ⟶ Y.D i` and
`τE : X.E i ⟶ Y.E i` compatible with `α`, `f` and `g`.

(blueprint: `lem-sp-couple-morphism`) -/
structure Hom (X Y : ExactCouple C a b c) where
  /-- The morphisms on the `D`-objects. -/
  τD (i : κ) : X.D i ⟶ Y.D i
  /-- The morphisms on the `E`-objects. -/
  τE (i : κ) : X.E i ⟶ Y.E i
  commα (i j : κ) : X.α i j ≫ τD j = τD i ≫ Y.α i j
  commf (i j : κ) : X.f i j ≫ τD j = τE i ≫ Y.f i j
  commg (i j : κ) : X.g i j ≫ τE j = τD i ≫ Y.g i j

namespace Hom

attribute [reassoc] commα commf commg

variable {X Y : ExactCouple C a b c} (φ : Hom X Y)

/-- The morphism of complexes `(E, d) ⟶ (E', d')` induced by a morphism of exact couples. -/
noncomputable def dMap : X.dComplex ⟶ Y.dComplex where
  f := φ.τE
  comm' i j _ := by
    dsimp
    rw [d, d, Category.assoc, φ.commg, φ.commf_assoc]

@[simp]
lemma dMap_f (i : κ) : φ.dMap.f i = φ.τE i := rfl

/-- The morphism `X.D' i ⟶ Y.D' i` induced on the images of `α`. -/
noncomputable def τD' (i : κ) : X.D' i ⟶ Y.D' i :=
  Abelian.monoLift (Y.ιD i) (X.ιD i ≫ φ.τD i) (by
    rw [← cancel_epi (X.πD i)]
    simp [φ.commα_assoc])

@[reassoc (attr := simp)]
lemma τD'_ιD (i : κ) : φ.τD' i ≫ Y.ιD i = X.ιD i ≫ φ.τD i :=
  Abelian.monoLift_comp _ _ _

@[reassoc]
lemma πD_τD' (i : κ) : X.πD i ≫ φ.τD' i = φ.τD (i - a) ≫ Y.πD i := by
  rw [← cancel_mono (Y.ιD i)]
  simp [commα]

@[reassoc]
lemma gCycles_cyclesMap (l k : κ) :
    X.gCycles l k ≫ HomologicalComplex.cyclesMap φ.dMap k = φ.τD l ≫ Y.gCycles l k := by
  rw [← cancel_mono (Y.dComplex.iCycles k)]
  simp [commg]

/-- The morphism of derived couples induced by a morphism of exact couples. -/
noncomputable def derived : Hom X.derived Y.derived where
  τD := φ.τD'
  τE i := HomologicalComplex.homologyMap φ.dMap i
  commα i j := by
    rw [← cancel_mono (Y.ιD j)]
    simp [commα]
  commf i j := by
    rw [← cancel_epi (X.dComplex.homologyπ i), ← cancel_mono (Y.ιD j)]
    simp [HomologicalComplex.homologyπ_naturality_assoc, commf]
  commg i j := by
    rw [← cancel_epi (X.πD i)]
    change X.πD i ≫ X.g' i j ≫ HomologicalComplex.homologyMap φ.dMap j =
      X.πD i ≫ φ.τD' i ≫ Y.g' i j
    rw [X.πD_g'_assoc, φ.πD_τD'_assoc, Y.πD_g', HomologicalComplex.homologyπ_naturality,
      φ.gCycles_cyclesMap_assoc]

/-- The morphisms of the iterated derived couples induced by a morphism of exact couples. -/
noncomputable def derivedIter : (n : ℕ) → Hom (X.derivedIter n) (Y.derivedIter n)
  | 0 => φ
  | n + 1 => (derivedIter n).derived

lemma derivedIter_succ_τE (n : ℕ) (i : κ) :
    (φ.derivedIter (n + 1)).τE i =
      HomologicalComplex.homologyMap (φ.derivedIter n).dMap i :=
  rfl

lemma homologyMap_dMap_comp_eqToHom (m n : ℕ) (h : m = n + 1) (pq : κ)
    (e₁ : (X.derivedIter n).dComplex.homology pq = (X.derivedIter m).dComplex.X pq)
    (e₂ : (Y.derivedIter n).dComplex.homology pq = (Y.derivedIter m).dComplex.X pq) :
    HomologicalComplex.homologyMap (φ.derivedIter n).dMap pq ≫ eqToHom e₂ =
      eqToHom e₁ ≫ ((φ.derivedIter m).dMap).f pq := by
  subst h
  simp [derivedIter_succ_τE]

/-- **The morphism of spectral sequences induced by a morphism of exact couples**: on the
`r`-th page it is the morphism of complexes `(E_r, d_r) ⟶ (E'_r, d'_r)` induced by the morphism
of the `(r - r₀)`-th derived couples, and it is compatible with the identifications of the
homology of a page with the next page.

(blueprint: `lem-sp-couple-morphism`) -/
noncomputable def spectralSequenceMap (r₀ : ℤ) :
    X.spectralSequence r₀ ⟶ Y.spectralSequence r₀ where
  hom r _ := (φ.derivedIter (r - r₀).toNat).dMap
  comm r r' pq hrr' hr := φ.homologyMap_dMap_comp_eqToHom _ _ (by omega) pq
    (X.homology_dComplex_derivedIter _ _ (by omega) pq)
    (Y.homology_dComplex_derivedIter _ _ (by omega) pq)

end Hom

end ExactCouple

end CategoryTheory
