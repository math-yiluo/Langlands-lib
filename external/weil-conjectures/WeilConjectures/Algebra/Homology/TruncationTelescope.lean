/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# Homotopy colimit of good truncations

Source: Stacks Project, Cohomology on Sites, Lemmas 06YS and 077J;
Derived Categories, Lemma 0949
(blueprint: lem-pc-kflat-hocolim-truncations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

-- Transport a cone augmentation and compose with a colimit identification abstractly.
private theorem telescope_augmentation_comp
    {B : Type*} [Category* B] [Abelian B]
    {X Y K L : CochainComplex B ℤ} {φ ψ : X ⟶ Y} (h : φ = ψ)
    (g : mappingCone φ ⟶ K) (e : K ≅ L) (p : Y ⟶ K) (q : Y ⟶ L)
    (hinr : mappingCone.inr φ ≫ g = p)
    (hinl : (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom g) (add_zero _) = 0)
    (hg : QuasiIso g) (hp : p ≫ e.hom = q) :
    ∃ f : mappingCone ψ ⟶ L, mappingCone.inr ψ ≫ f = q ∧
      (mappingCone.inl ψ).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0 ∧
      QuasiIso f := by
  subst ψ
  have : QuasiIso g := hg
  refine ⟨g ≫ e.hom, ?_, ?_, inferInstance⟩
  · rw [← Category.assoc, hinr, hp]
  · rw [HomComplex.Cochain.ofHom_comp]
    rw [← HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [hinl, HomComplex.Cochain.zero_comp]

/-- (blueprint: lem-pc-kflat-hocolim-truncations) For a complex `K` of modules over a sheaf of
commutative rings on a site, the canonical map from the telescope of its good truncations to
`K` is a quasi-isomorphism. Also, filtered colimits preserve quasi-isomorphisms of such
complexes (Stacks, Tag 06YS).

Proof:
1. Apply `lem-pc-complex-hocolim-colimit` to the good truncations and their canonical
transition maps. Its telescope comparison gives a quasi-isomorphism to the termwise colimit.
2. In degree `i`, the term is zero for `n < i`, the cycles for `n = i`, and the term of
`K` for `n > i`. The transition maps are eventually identities, so this colimit is `K`.
Compose the telescope comparison with this isomorphism. The canonical cone map is zero
on the shifted summand and is the sum of the truncation inclusions on the unshifted summand.
3. By `lem-pur-ringed-site-grothendieck-abelian`, filtered colimits of sheaves of modules
on a small ringed site are exact. Hence they commute with kernels, images, and cohomology.
The induced map on each cohomology sheaf is the filtered colimit of isomorphisms, so it
is an isomorphism. This uses the meanings of cochain complexes and quasi-isomorphisms
in `def-pc-cochain-complex-modules` and `def-pc-quasi-iso-modules`.
The source uses these comparisons in 077J, invoked in the proof of 06YS. -/
theorem quasiIso_hocolim_truncLE_and_filtered_colimit
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    (R : Sheaf J CommRingCat.{u})
    (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    (let E : ℕ → CochainComplex
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
        fun n => K.truncLE (n : ℤ)
      let A := ∐ E
      ∃ t : ∀ n : ℕ, E n ⟶ E (n + 1),
        (∀ n, t n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) = K.ιTruncLE (n : ℤ)) ∧
        ∃ f : mappingCone
            (𝟙 A - Sigma.desc (fun n => t n ≫ Sigma.ι E (n + 1))) ⟶ K,
          mappingCone.inr _ ≫ f =
            Sigma.desc (fun n : ℕ => (K.ιTruncLE (n : ℤ) : E n ⟶ K)) ∧
            (mappingCone.inl _).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0 ∧
            QuasiIso f) ∧
      (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
        (F G : I ⥤ CochainComplex
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
        (α : F ⟶ G), (∀ i : I, QuasiIso (α.app i)) →
          QuasiIso (colim.map α)) := by
  let M := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have : HasColimitsOfShape (Discrete ℕ) M := inferInstance
  have : HasColimitsOfShape (Discrete ℕ) (CochainComplex M ℤ) := by
    refine ⟨fun F ↦ ?_⟩
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval M (.up ℤ) n) :=
      HasColimitsOfShape.has_colimit _
    exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩
  let E : ℕ → CochainComplex M ℤ := fun n ↦ K.truncLE (n : ℤ)
  let D : ℕ ⥤ CochainComplex M ℤ :=
    { obj := E
      map := fun {n m} f ↦ K.truncLEMapOfLE n m (by exact_mod_cast leOfHom f)
      map_id := fun n ↦ by
        dsimp [E]
        simp [← cancel_mono (K.ιTruncLE (n : ℤ))]
      map_comp := fun f g ↦ by
        simp [← cancel_mono (K.ιTruncLE _), Category.assoc] }
  let c : Cocone D :=
    { pt := K
      ι := { app := fun n ↦ K.ιTruncLE (n : ℤ)
             naturality := fun n m f ↦ by simp [D] } }
  have hc : IsColimit c := by
    apply HomologicalComplex.isColimitOfEval
    intro i
    apply isColimitOfIsEventuallyConstant _ (i.toNat + 1)
    intro n f
    apply isIso_ιTruncLE_f
    have hn := leOfHom f
    omega
  let e : colimit D ≅ K :=
    (colimit.isColimit D).coconePointUniqueUpToIso hc
  have he (n : ℕ) : colimit.ι D n ≫ e.hom = K.ιTruncLE (n : ℤ) := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n
  let t : ∀ n : ℕ, E n ⟶ E (n + 1) :=
    fun n ↦ D.map (homOfLE (Nat.le_succ n))
  have ht (n : ℕ) : t n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      K.ιTruncLE (n : ℤ) := by simp [t, D]
  have hs : telescopeColimitShift R D =
      𝟙 (∐ E) - Sigma.desc (fun n ↦ t n ≫ Sigma.ι E (n + 1)) := by
    change Sigma.desc (fun n ↦ Sigma.ι E n - t n ≫ Sigma.ι E (n + 1)) = _
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_sub, Category.comp_id, Sigma.ι_comp_desc]
  obtain ⟨g, hg, hz, hq⟩ := quasiIso_telescopeColimit R D
  constructor
  · refine ⟨t, ht, ?_⟩
    apply telescope_augmentation_comp hs g e (telescopeToColimit R D)
      (Sigma.desc (fun n : ℕ ↦ K.ιTruncLE (n : ℤ))) hg hz hq
    apply Sigma.hom_ext
    intro n
    simpa only [telescopeToColimit, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using he n
  · intro I _ _ F G α hα
    let _ := (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
    exact (HomologicalComplex.quasiIso M (.up ℤ)).colimMap α hα

end CochainComplex
