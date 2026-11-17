import Langlands.GroupScheme.Reductive.AffineSplitIsogenyCellMap
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily
import Langlands.LinearAlgebra.RootDatumIsogenyReflections
import Langlands.LinearAlgebra.RootDatumRankTwoBase

/-! # Powered Weyl points and transport along simple words -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}

variable (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

/-- The inverse root bijection carries every reflection word to the corresponding word. -/
theorem indexEquiv_symm_wordPerm (l : List J) (j : J) :
    f.indexEquiv.symm (Langlands.LinearAlgebra.wordPerm P l j) =
      Langlands.LinearAlgebra.wordPerm Q (l.map f.indexEquiv.symm)
        (f.indexEquiv.symm j) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change f.indexEquiv.symm (P.reflectionPerm a
        (Langlands.LinearAlgebra.wordPerm P l j)) = _
    rw [f.indexEquiv_symm_reflectionPerm, ih]
    rfl

/-- The exponent attached to a root is unchanged by a reflection word. -/
theorem rootFactor_indexEquiv_symm_wordPerm (l : List J) (j : J) :
    f.rootFactor (f.indexEquiv.symm (Langlands.LinearAlgebra.wordPerm P l j)) =
      f.rootFactor (f.indexEquiv.symm j) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change f.rootFactor (f.indexEquiv.symm (P.reflectionPerm a
        (Langlands.LinearAlgebra.wordPerm P l j))) = _
    rw [f.indexEquiv_symm_reflectionPerm, f.rootFactor_reflectionPerm, ih]

/-- Transport a supplied simple word between bases whose simple roots correspond. -/
def transportSimpleWord {b : P.Base} {b' : Q.Base}
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    {α : J} (w : SimpleWord P b α) : SimpleWord Q b' (f.indexEquiv.symm α) where
  simple := f.indexEquiv.symm w.simple
  simple_mem := hb _ w.simple_mem
  word := w.word.map f.indexEquiv.symm
  word_mem := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact hb c (w.word_mem c hc)
  root_eq := by
    rw [← Langlands.LinearAlgebra.root_wordPerm,
      ← indexEquiv_symm_wordPerm]
    have hw : Langlands.LinearAlgebra.wordPerm P w.word w.simple = α :=
      P.root.injective ((Langlands.LinearAlgebra.root_wordPerm P _ _).trans w.root_eq)
    rw [hw]

variable (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

/-- Equal root factors give the same actual additive power map. -/
theorem rootPower_eq_of_factor_eq {a b : J'} (hab : f.rootFactor a = f.rootFactor b) :
    rootPower f hchar a = rootPower f hchar b := by
  apply Grp.hom_ext
  simp only [rootPower_hom, hab]

/-- A powered root map has the same value at one as its target parametrization. -/
theorem rootPoint_poweredRootFamily_one (u' : J' → (Ga R ⟶ H)) (j : J)
    (Z : Over (Spec (CommRingCat.of R))) :
    rootPoint (poweredRootFamily f hchar u' j) Z 1 =
      rootPoint (u' (f.indexEquiv.symm j)) Z 1 := by
  rw [rootPoint_poweredRootFamily, one_pow]

/-- Additivity forces the powered root map to retain its value at minus one as well. -/
theorem rootPoint_poweredRootFamily_neg_one (u' : J' → (Ga R ⟶ H)) (j : J)
    (Z : Over (Spec (CommRingCat.of R))) :
    rootPoint (poweredRootFamily f hchar u' j) Z (-1) =
      rootPoint (u' (f.indexEquiv.symm j)) Z (-1) := by
  rw [rootPoint_neg, rootPoint_poweredRootFamily_one, rootPoint_neg]

/-- The Weyl product of powered maps is exactly the reindexed target Weyl product. -/
theorem rootWeylPoint_poweredRootFamily (u' : J' → (Ga R ⟶ H)) (a : J) :
    rootWeylPoint P (poweredRootFamily f hchar u') a =
      rootWeylPoint Q u' (f.indexEquiv.symm a) := by
  simp only [rootWeylPoint, weylPoint, rootPoint_poweredRootFamily_one,
    rootPoint_poweredRootFamily_neg_one, f.indexEquiv_symm_reflectionPerm]

/-- The powered target map conjugated by a reindexed reflection word. -/
def poweredWordMap (u' : J' → (Ga R ⟶ H)) (l : List J) (j : J) : Ga R ⟶ H :=
  rootMap f hchar (f.indexEquiv.symm j)
    (wordConj Q u' (l.map f.indexEquiv.symm) (u' (f.indexEquiv.symm j)))

/-- Conjugation by the powered Weyl products commutes with the additive power map. -/
theorem wordConj_poweredRootFamily (u' : J' → (Ga R ⟶ H)) (l : List J) (j : J) :
    wordConj P (poweredRootFamily f hchar u') l (poweredRootFamily f hchar u' j) =
      poweredWordMap f hchar u' l j := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change wordConj P (poweredRootFamily f hchar u') l
        (poweredRootFamily f hchar u' j) ≫
          (H.innerIso (rootWeylPoint P (poweredRootFamily f hchar u') a)).hom = _
    rw [ih, rootWeylPoint_poweredRootFamily]
    change (rootPower f hchar (f.indexEquiv.symm j) ≫
        wordConj Q u' (l.map f.indexEquiv.symm) (u' (f.indexEquiv.symm j))) ≫
          (H.innerIso (rootWeylPoint Q u' (f.indexEquiv.symm a))).hom =
      rootPower f hchar (f.indexEquiv.symm j) ≫
        (wordConj Q u' (l.map f.indexEquiv.symm) (u' (f.indexEquiv.symm j)) ≫
          (H.innerIso (rootWeylPoint Q u' (f.indexEquiv.symm a))).hom)
    exact Category.assoc _ _ _

/-- The genuine target word family obtained from source simple words by the root bijection. -/
def targetWordFamily {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) (α' : J') : Ga R ⟶ H :=
  wordConj Q u' ((W (f.indexEquiv α')).word.map f.indexEquiv.symm)
    (u' (f.indexEquiv.symm (W (f.indexEquiv α')).simple))

/-- The exponent of the initial simple root equals the exponent of the word's final root. -/
theorem rootFactor_simpleWord {b : P.Base} {α : J} (w : SimpleWord P b α) :
    f.rootFactor (f.indexEquiv.symm w.simple) =
      f.rootFactor (f.indexEquiv.symm α) := by
  have hw : Langlands.LinearAlgebra.wordPerm P w.word w.simple = α :=
    P.root.injective ((Langlands.LinearAlgebra.root_wordPerm P _ _).trans w.root_eq)
  exact (rootFactor_indexEquiv_symm_wordPerm f w.word w.simple).symm.trans
    (congrArg (fun j => f.rootFactor (f.indexEquiv.symm j)) hw)

/-- Forming a Weyl family from powered simple maps equals powering the target word family. -/
theorem weylFamily_poweredRootFamily {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) (α : J) :
    weylFamily P W (poweredRootFamily f hchar u') α =
      poweredRootFamily f hchar (targetWordFamily f W u') α := by
  unfold weylFamily
  rw [wordConj_poweredRootFamily]
  simp only [poweredWordMap, poweredRootFamily, rootMap, targetWordFamily]
  rw [f.indexEquiv.apply_symm_apply]
  rw [rootPower_eq_of_factor_eq f hchar (rootFactor_simpleWord f (W α))]

/-- If the target roots and Weyl products are normalized on corresponding simple roots,
the transported word family consists of genuine target root parametrizations. -/
theorem isRootParametrization_targetWordFamily [DecidableEq I']
    {b : P.Base} {b' : Q.Base}
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α)
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    (u' : J' → (Ga R ⟶ H))
    (hu' : ∀ a' ∈ b'.support, IsRootParametrization i' (Q.root a') (u' a'))
    (hw' : ∀ a' ∈ b'.support,
      IsWeylPoint i' (rootWeylPoint Q u' a') (Q.reflection a'))
    (α' : J') :
    IsRootParametrization i' (Q.root α') (targetWordFamily f W u' α') := by
  let w := transportSimpleWord f hb (W (f.indexEquiv α'))
  have h := isRootParametrization_wordConj (P := Q) (u := u') (w := u' w.simple)
    w.word (fun a ha => hw' a (w.word_mem a ha)) (hu' w.simple w.simple_mem)
  rw [w.root_eq] at h
  simpa only [w, transportSimpleWord, targetWordFamily, Equiv.symm_apply_apply] using h

end Langlands.GroupScheme.AffineRootDatumIsogeny
