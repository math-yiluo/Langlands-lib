/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.RelativeFlatExtension
import WeilConjectures.Algebra.Homology.FlatAugmentationEpicification

/-!
# One extension of a flat replacement of a good truncation

Source: Stacks Project, Derived Categories, Lemma 06XX, induction step;
Cohomology on Sites, Lemma 077J
(blueprint: lem-pc-flat-truncation-successor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded-above flat complex augmented to one good truncation extends to a
bounded-above flat replacement of the next good truncation, termwise epic, compatible with
the given augmentation after including both truncations into `G`.
This is a single extension step, with the previous complex and augmentation prescribed;
it does not assert the existence of an infinite tower.

Source: Stacks Project, Derived Categories, Lemma 06XX, induction step, specialized
as in Cohomology on Sites, Lemma 077J
(blueprint: lem-pc-flat-truncation-successor).

Proof: Compose q with the inclusion j from the n-th to the (n+1)-st good truncation
and form its mapping cone C. Both its source and target are bounded above, so C is
bounded above. Resolve C by a bounded-above flat complex Q using the bounded flat
replacement theorem. The relative flat extension along Q -> C gives a bounded-above
flat complex F, a map t : E -> F and a quasi-isomorphism g : F -> G^{<= n+1} with
t >> g = q >> j. Adding flat identity disks makes g termwise epic without changing F
up to quasi-isomorphism. Composing with the inclusion into G gives the equality. -/
theorem exists_flat_truncation_successor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℕ)
    (E : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (q : E ⟶ G.truncLE (n : ℤ))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (E' : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : E ⟶ E') (q' : E' ⟶ G.truncLE ((n + 1 : ℕ) : ℤ)),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E'.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (E'.X i)) ∧ QuasiIso q' ∧
      (∀ i : ℤ, Epi (q'.f i)) ∧
      t ≫ q' ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) = q ≫ G.ιTruncLE (n : ℤ) := by
  let m : ℤ := ((n + 1 : ℕ) : ℤ)
  have hstrict : (G.truncLE (n : ℤ)).IsStrictlyLE m := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (G.truncLE (n : ℤ)).isZero_of_isStrictlyLE (n : ℤ) i (by dsimp [m] at hi; omega)
  have : IsIso ((G.truncLE (n : ℤ)).ιTruncLE m) := inferInstance
  let j : G.truncLE (n : ℤ) ⟶ G.truncLE m :=
    inv ((G.truncLE (n : ℤ)).ιTruncLE m) ≫ truncLEMap (G.ιTruncLE (n : ℤ)) m
  have hj : j ≫ G.ιTruncLE m = G.ιTruncLE (n : ℤ) := by
    dsimp [j]
    rw [Category.assoc, ιTruncLE_naturality, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((G.truncLE m).X i) :=
    ⟨m, fun i hi ↦ (G.truncLE m).isZero_of_isStrictlyLE m i hi⟩
  obtain ⟨b, hbE⟩ := hbounded
  let N : ℤ := max b m
  let cone := mappingCone (q ≫ j)
  have hcone : ∀ i : ℤ, N < i → IsZero (cone.X i) := by
    intro i hi
    rw [mappingCone.isZero_X_iff]
    constructor
    · exact hbE (i + 1) (by dsimp [N] at hi; omega)
    · exact (G.truncLE m).isZero_of_isStrictlyLE m i (by dsimp [N] at hi; omega)
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_boundedAbove_flat_replacement J R N
  let X : ObjectProperty.FullSubcategory
      (fun F : CochainComplex _ ℤ ↦ ∀ i : ℤ, N < i → IsZero (F.X i)) :=
    ⟨cone, hcone⟩
  obtain ⟨hflatQ, hboundQ, _, hquasiQ⟩ := hQ X
  obtain ⟨F, t, g, hb, hf, hg, ht⟩ :=
    exists_relative_boundedAbove_flat_extension E (G.truncLE m) (q ≫ j)
      ⟨b, hbE⟩ hflat (Q.obj X) (ε.app X) ⟨N, hboundQ⟩ hflatQ hquasiQ
  obtain ⟨F', s, g', hb', hf', hs, he', hsg⟩ :=
    exists_boundedAbove_flat_epicification F (G.truncLE m) g hb hH hf
  have : QuasiIso s := hs
  have : QuasiIso (s ≫ g') := by rw [hsg]; exact hg
  have hg' : QuasiIso g' := quasiIso_of_comp_left s g'
  refine ⟨F', t ≫ s, g', hb', hf', hg', he', ?_⟩
  change (t ≫ s) ≫ g' ≫ G.ιTruncLE m = q ≫ G.ιTruncLE (n : ℤ)
  calc
    (t ≫ s) ≫ g' ≫ G.ιTruncLE m = t ≫ (s ≫ g') ≫ G.ιTruncLE m := by
      simp only [Category.assoc]
    _ = t ≫ g ≫ G.ιTruncLE m := by rw [hsg]
    _ = (q ≫ j) ≫ G.ιTruncLE m := by rw [← Category.assoc, ht]
    _ = q ≫ G.ιTruncLE (n : ℤ) := by rw [Category.assoc, hj]

end CochainComplex
