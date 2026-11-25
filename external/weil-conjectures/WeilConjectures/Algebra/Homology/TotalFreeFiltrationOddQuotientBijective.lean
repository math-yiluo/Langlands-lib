/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationOddQuotientMap

/-!
# Degreewise bijectivity of the odd quotient map

Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-odd-quotient-bijective)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

private noncomputable def columnProjection (j : ℕ) (k : ℤ) :
    (K.total (ComplexShape.up ℤ)).X k ⟶ (S j).X₃.X (k + j) := by
  classical
  exact K.totalDesc (fun p q h ↦
    if hp : p = -(j : ℤ) then
      (K.XXIsoOfEq _ _ _ hp (by dsimp at h; omega)).hom ≫
        (e j).inv.f (k + j) ≫ (S j).g.f (k + j)
    else 0)

private lemma full_projection (j : ℕ) (k : ℤ) :
    full K j k ≫ columnProjection K S e j k =
      (e j).inv.f (k + j) ≫ (S j).g.f (k + j) := by
  classical
  simp [full, columnProjection]

private lemma other_projection (j a : ℕ) (ha : a ≠ j) (k : ℤ) :
    full K a k ≫ columnProjection K S e j k = 0 := by
  classical
  simp [full, columnProjection, show -(a : ℤ) ≠ -(j : ℤ) by omega]

private lemma lower_projection (j a : ℕ) (k : ℤ) :
    lower K S e a k ≫ columnProjection K S e j k = 0 := by
  by_cases ha : a = j
  · subst a
    simp only [lower, Category.assoc, full_projection]
    have he : (e j).hom.f (k + j) ≫ (e j).inv.f (k + j) = 𝟙 _ :=
      congrArg (fun f ↦ f.f (k + j)) (e j).hom_inv_id
    rw [← Category.assoc ((e j).hom.f _), he, Category.id_comp]
    exact congrArg (fun f ↦ f.f (k + j)) (S j).zero
  · simp [lower, other_projection K S e j a ha k]

private lemma projection_zero (j : ℕ) (k : ℤ)
    (x : (K.total (ComplexShape.up ℤ)).X k) (hx : x ∈ term K S e (2 * j + 1) k) :
    columnProjection K S e j k x = 0 := by
  suffices h : term K S e (2 * j + 1) k ≤
      LinearMap.ker (columnProjection K S e j k).hom from h hx
  apply iSup_le
  intro a
  apply sup_le
  · split_ifs with ha
    · rintro y ⟨z, rfl⟩
      exact congrArg (fun f ↦ f z) (other_projection K S e j a (by omega) k)
    · exact bot_le
  · split_ifs
    · rintro y ⟨z, rfl⟩
      exact congrArg (fun f ↦ f z) (lower_projection K S e j a k)
    · exact bot_le

private noncomputable def restrictedProjection (j : ℕ) (k : ℤ) :
    (complex K S e h_positive (2 * j + 1 + 1)).X k ⟶ (S j).X₃.X (k + j) :=
  ModuleCat.ofHom ((columnProjection K S e j k).hom.comp
    (term K S e (2 * j + 1 + 1) k).subtype)

private lemma restrictMap_projection_zero
    (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M N : ∀ k : ℤ, Submodule A (T.X k))
    (hM : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (hN : ∀ k l (x : T.X k), x ∈ N k → T.d k l x ∈ N l)
    (hMN : ∀ k, M k ≤ N k) (k : ℤ) (Z : ModuleCat.{u} A) (p : T.X k ⟶ Z)
    (hp : ∀ x, x ∈ M k → p x = 0) :
    (restrictMap T M N hM hN hMN).f k ≫
      ModuleCat.ofHom (p.hom.comp (N k).subtype) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hp x.val x.property

private lemma restrictedProjection_zero (j : ℕ) (k : ℤ) :
    (step K S e h_positive (2 * j + 1)).f k ≫
      restrictedProjection K S e h_positive j k = 0 := by
  exact restrictMap_projection_zero (K.total (ComplexShape.up ℤ))
    (term K S e (2 * j + 1)) (term K S e (2 * j + 1 + 1))
    (differential_mem K S e h_positive (2 * j + 1))
    (differential_mem K S e h_positive (2 * j + 1 + 1))
    (fun l ↦ term_mono K S e (Nat.le_succ (2 * j + 1)) l)
    k _ (columnProjection K S e j k) (projection_zero K S e j k)

private noncomputable def quotientProjection (j : ℕ) (k : ℤ) :
    (cokernel (step K S e h_positive (2 * j + 1))).X k ⟶ (S j).X₃.X (k + j) :=
  (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)
    (step K S e h_positive (2 * j + 1))).desc
      (CokernelCofork.ofπ (restrictedProjection K S e h_positive j k)
        (restrictedProjection_zero K S e h_positive j k))

private lemma quotientProjection_fac (j : ℕ) (k : ℤ) :
    (cokernel.π (step K S e h_positive (2 * j + 1))).f k ≫
      quotientProjection K S e h_positive j k =
        restrictedProjection K S e h_positive j k := by
  exact Cofork.IsColimit.π_desc
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)
      (step K S e h_positive (2 * j + 1)))

private lemma full_quotient_projection (j : ℕ) (k : ℤ) :
    (oddFullQuotientMap K S e h_positive j).f k ≫
      quotientProjection K S e h_positive j k = (S j).g.f (k + j) := by
  change fullToNext K S e h_positive j k ≫
    (cokernel.π (step K S e h_positive (2 * j + 1))).f k ≫
      quotientProjection K S e h_positive j k = _
  rw [quotientProjection_fac]
  have h := full_projection K S e j k
  have he : (e j).hom.f (k + j) ≫ (e j).inv.f (k + j) = 𝟙 _ :=
    congrArg (fun f ↦ f.f (k + j)) (e j).hom_inv_id
  ext x
  change (columnProjection K S e j k)
    (full K j k ((e j).hom.f (k + j) x)) = _
  have ht := congrArg (fun f ↦ f ((e j).hom.f (k + j) x)) h
  have hi := congrArg (fun f ↦ f x) he
  simpa using ht.trans (congrArg ((S j).g.f (k + j)) hi)

private lemma oddQuotientMap_fac (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) :
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).map
      (S j).g ≫ oddQuotientMap K S e h_positive h_exact j =
        oddFullQuotientMap K S e h_positive j := by
  let F := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
  have hs := (h_exact j).map_of_exact F
  have := hs.epi_g
  exact hs.exact.g_desc _ _

private lemma oddQuotientMap_left_inverse
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    (oddQuotientMap K S e h_positive h_exact j).f k ≫
      quotientProjection K S e h_positive j k = 𝟙 _ := by
  have hs := (h_exact j).map_of_exact
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) (k + j))
  have : Epi ((S j).g.f (k + j)) := hs.epi_g
  change (oddQuotientMap K S e h_positive h_exact j).f k ≫
    quotientProjection K S e h_positive j k = 𝟙 ((S j).X₃.X (k + j))
  rw [← cancel_epi ((S j).g.f (k + j)), Category.comp_id, ← Category.assoc]
  have hf := congrArg (fun f ↦ f.f k) (oddQuotientMap_fac K S e h_positive h_exact j)
  change (S j).g.f (k + j) ≫ (oddQuotientMap K S e h_positive h_exact j).f k = _ at hf
  rw [hf, full_quotient_projection]

private lemma term_next_le (j : ℕ) (k : ℤ) :
    term K S e (2 * j + 2) k ≤
      term K S e (2 * j + 1) k ⊔ LinearMap.range (full K j k).hom := by
  apply iSup_le
  intro a
  apply sup_le
  · split_ifs with ha
    · by_cases haj : a = j
      · subst a
        exact le_sup_right
      · apply le_trans _ le_sup_left
        apply le_trans _ (le_iSup (fun b : ℕ ↦
          (if 2 * b + 2 ≤ 2 * j + 1 then LinearMap.range (full K b k).hom else ⊥) ⊔
            (if 2 * b + 1 ≤ 2 * j + 1 then LinearMap.range (lower K S e b k).hom
              else ⊥)) a)
        rw [ite_eq_left (show 2 * a + 2 ≤ 2 * j + 1 by omega)]
        exact le_sup_left
    · exact bot_le
  · split_ifs with ha
    · apply le_trans _ le_sup_left
      apply le_trans _ (le_iSup (fun b : ℕ ↦
        (if 2 * b + 2 ≤ 2 * j + 1 then LinearMap.range (full K b k).hom else ⊥) ⊔
          (if 2 * b + 1 ≤ 2 * j + 1 then LinearMap.range (lower K S e b k).hom
            else ⊥)) a)
      rw [ite_eq_left (show 2 * a + 1 ≤ 2 * j + 1 by omega)]
      exact le_sup_right
    · exact bot_le

private lemma oddFullQuotientMap_surjective (j : ℕ) (k : ℤ) :
    Function.Surjective ((oddFullQuotientMap K S e h_positive j).f k) := by
  let π := (cokernel.π (step K S e h_positive (2 * j + 1))).f k
  have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective π).mp inferInstance
  intro z
  obtain ⟨x, hx⟩ := hπ z
  obtain ⟨y, hy, w, hw, heq⟩ := (Submodule.mem_sup).mp
    (term_next_le K S e j k x.property)
  obtain ⟨v, rfl⟩ := hw
  let y' : (complex K S e h_positive (2 * j + 1)).X k := ⟨y, hy⟩
  let v' := (e j).inv.f (k + j) v
  have he : (e j).inv.f (k + j) ≫ (e j).hom.f (k + j) = 𝟙 _ :=
    congrArg (fun f ↦ f.f (k + j)) (e j).inv_hom_id
  have hdecomp : x = (step K S e h_positive (2 * j + 1)).f k y' +
      fullToNext K S e h_positive j k v' := by
    apply Subtype.ext
    change x.val = y + full K j k ((e j).hom.f (k + j) v')
    have hv := congrArg (fun f ↦ f v) he
    change (e j).hom.f (k + j) v' = v at hv
    rw [hv]
    exact heq.symm
  have hz : (step K S e h_positive (2 * j + 1)).f k ≫ π = 0 :=
    congrArg (fun f ↦ f.f k) (cokernel.condition (step K S e h_positive (2 * j + 1)))
  refine ⟨v', ?_⟩
  change π (fullToNext K S e h_positive j k v') = z
  rw [← hx, hdecomp, map_add]
  have hzero := congrArg (fun f ↦ f y') hz
  change π ((step K S e h_positive (2 * j + 1)).f k y') = 0 at hzero
  rw [hzero, zero_add]

/-- The descended odd quotient map is degreewise bijective.
Source: Stacks Project, Tag 09KP, proof of lemma-resolve, successive quotients.
(blueprint: lem-pc-derived-total-filtration-odd-quotient-bijective)

Proof. Define a map from the total degree object to the third endpoint by
projecting to column -j, applying e_j inverse, and applying (S j).g. The total
coproduct universal property gives this map without any choice of vectors.
It vanishes on the full columns with a<j and on every lower piece, using the
short-complex zero relation when a=j. It therefore kills stage 2j+1.
Restrict it to stage 2j+2 and descend through the evaluated cokernel, which is
a cokernel since evaluation preserves colimits. Its composite with the
full-column map is (S j).g. The factorization equation defining oddQuotientMap
and epimorphy of (S j).g in every degree show that this projection is a left
inverse to oddQuotientMap, proving injectivity. For surjectivity, prove directly
from the supremum defining term that stage 2j+2 is contained in stage 2j+1
plus the range of the full column -j. Lift a quotient vector along its
surjective cokernel projection and decompose it into those two pieces. The
first is killed by the projection, and the second comes from the full-column
map. Its factorization through (S j).g gives a preimage under oddQuotientMap.
No splitting, freeness, or zero endpoint differential is used. The arguments
include j=0, zero modules, and the zero ring.
-/
theorem oddQuotientMap_bijective
    (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) (k : ℤ) :
    Function.Bijective ((oddQuotientMap K S e h_positive h_exact j).f k) := by
  constructor
  · intro x y hxy
    have h := oddQuotientMap_left_inverse K S e h_positive h_exact j k
    have hi (v : (S j).X₃.X (k + j)) := congrArg (fun f ↦ f v) h
    exact (hi x).symm.trans ((congrArg
      (quotientProjection K S e h_positive j k) hxy).trans (hi y))
  · intro z
    obtain ⟨v, hv⟩ := oddFullQuotientMap_surjective K S e h_positive j k z
    refine ⟨(S j).g.f (k + j) v, ?_⟩
    have hf := congrArg (fun f ↦ f.f k)
      (oddQuotientMap_fac K S e h_positive h_exact j)
    exact (congrArg (fun f ↦ f v) hf).trans hv

end CochainComplex.TotalFreeFiltration
