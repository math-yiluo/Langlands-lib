/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.TruncationTelescope
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex

/-!
# Telescope comparison for replacements of good truncations

Source: Stacks Project, Cohomology on Sites, proof of Lemma 06YS and Lemma 077J;
Derived Categories, Lemma 0949
(blueprint: lem-pc-flat-truncation-telescope-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

-- Compare augmentations in an arbitrary abelian category, before specializing to sheaves.
private theorem quasiIso_of_cone_map_augmentation
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {X Y X' Y' K : CochainComplex B ℤ}
    (φ : X ⟶ Y) (ψ : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (hcomm : φ ≫ b = a ≫ ψ) (ha : QuasiIso a) (hb : QuasiIso b)
    (f : mappingCone φ ⟶ K) (g : mappingCone ψ ⟶ K) (hg : QuasiIso g)
    (hinl : (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0)
    (hginl : (mappingCone.inl ψ).comp (HomComplex.Cochain.ofHom g) (add_zero _) = 0)
    (hinr : mappingCone.inr φ ≫ f = b ≫ mappingCone.inr ψ ≫ g) : QuasiIso f := by
  let m := mappingCone.map φ ψ a b hcomm
  have hm : QuasiIso m := by
    have : QuasiIso a := ha
    have : QuasiIso b := hb
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso B m).1
    exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap φ ψ a b hcomm))
      (DerivedCategory.mappingCone_triangle_distinguished φ)
      (DerivedCategory.mappingCone_triangle_distinguished ψ)
      (by exact inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
      (by exact inferInstanceAs (IsIso (DerivedCategory.Q.map b)))
  have heq : f = m ≫ g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply (mappingCone.ext_from_iff φ (i + 1) i rfl _ _).2
    constructor
    · have hf := congrArg
        (fun c : HomComplex.Cochain X K (-1) ↦ c.v (i + 1) i (by omega)) hinl
      have hg' := congrArg
        (fun c : HomComplex.Cochain X' K (-1) ↦ c.v (i + 1) i (by omega)) hginl
      rw [HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.ofHom_v,
        HomComplex.Cochain.zero_v] at hf hg'
      change (mappingCone.inl φ).v (i + 1) i (by omega) ≫ f.f i = 0 at hf
      change (mappingCone.inl ψ).v (i + 1) i (by omega) ≫ g.f i = 0 at hg'
      simp only [HomologicalComplex.comp_f]
      rw [← Category.assoc]
      simp only [m, mappingCone.map, mappingCone.inl_v_desc_f,
        HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
        Category.assoc]
      exact hf.trans ((congrArg (fun z ↦ a.f (i + 1) ≫ z) hg').trans
        comp_zero).symm
    · have hc : mappingCone.inr φ ≫ m = b ≫ mappingCone.inr ψ :=
        (mappingCone.triangleMap φ ψ a b hcomm).comm₂
      have hr : mappingCone.inr φ ≫ (m ≫ g) = b ≫ mappingCone.inr ψ ≫ g := by
        rw [← Category.assoc, hc, Category.assoc]
      exact congrArg (fun z ↦ z.f i) (hinr.trans hr.symm)
  rw [heq]
  have : QuasiIso m := hm
  have : QuasiIso g := hg
  infer_instance

/-- A canonical augmentation from the telescope of replacements of good truncations
is a quasi-isomorphism. No flatness or boundedness of the replacements is needed.
Source: Stacks Project, proof of Lemma 06YS via Lemma 077J; Derived Categories,
Lemma 0949 (blueprint: lem-pc-flat-truncation-telescope-comparison).

Proof: Take the truncation transition maps and canonical telescope augmentation
supplied by `quasiIso_hocolim_truncLE_and_filtered_colimit`. Truncation inclusions
are monomorphisms, so the assumed compatibility after inclusion in G implies that
q is a morphism of the two sequential systems. The sum of the maps q is a
quasi-isomorphism: the sheaf-module category is Grothendieck abelian by
`grothendieckAbelian_with_localized_generator`, hence its coproducts are exact.
Apply `HomologicalComplex.isStableUnderColimitsOfShape_quasiIso` to the discrete
natural transformation with components q. Compatibility gives
a square between the two one-minus-shift endomorphisms. Its induced cone map is a
quasi-isomorphism by the long exact cohomology sequences and the five lemma, because
both maps between the sums are quasi-isomorphisms. Compose this cone map with the
canonical truncation-telescope augmentation, which is a quasi-isomorphism by the
same theorem. On the unshifted summand this composite is the sum of q followed by
the truncation inclusions; on the shifted summand it is zero. The mapping-cone
extensionality theorem shows that this composite equals f. Thus f is a
quasi-isomorphism. This argument also covers the zero complex and towers without
split transition maps. -/
theorem quasiIso_flat_truncation_telescope
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (q : ∀ n : ℕ, E n ⟶ G.truncLE (n : ℤ))
    (hq : ∀ n : ℕ, QuasiIso (q n))
    (hcompat : ∀ n : ℕ, t n ≫ q (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      q n ≫ G.ιTruncLE (n : ℤ))
    (f : mappingCone (𝟙 (∐ E) -
      Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))) ⟶ G)
    (hinr : mappingCone.inr _ ≫ f =
      Sigma.desc (fun n : ℕ ↦ q n ≫ G.ιTruncLE (n : ℤ)))
    (hinl : (mappingCone.inl _).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0) :
    QuasiIso f := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have : HasColimitsOfShape (Discrete ℕ) A := inferInstance
  have : HasColimitsOfShape (Discrete ℕ) (CochainComplex A ℤ) := by
    refine ⟨fun F ↦ ?_⟩
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval A (.up ℤ) n) :=
      HasColimitsOfShape.has_colimit _
    exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩
  let := HasDerivedCategory.standard A
  let D : ℕ → CochainComplex A ℤ := fun n ↦ G.truncLE (n : ℤ)
  obtain ⟨v, hv, g, hginr, hginl, hg⟩ :=
    (quasiIso_hocolim_truncLE_and_filtered_colimit R G).1
  let σ : (∐ E) ⟶ (∐ D) := Limits.Sigma.map q
  have : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsStableUnderColimitsOfShape
      (Discrete ℕ) := by
    have : IsGrothendieckAbelian.{u} A :=
      (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
    have : AB4OfSize.{u} A := inferInstance
    have : AB4OfSize.{0} A := AB4OfSize_shrink A
    have : HasExactColimitsOfShape (Discrete ℕ) A := inferInstance
    infer_instance
  have hσ : QuasiIso σ := by
    let α : Discrete.functor E ⟶ Discrete.functor D :=
      Discrete.natTrans (fun n ↦ q n.as)
    exact (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).colimMap α
      (fun n ↦ hq n.as)
  let φ := 𝟙 (∐ E) - Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))
  let ψ := 𝟙 (∐ D) - Sigma.desc (fun n : ℕ ↦ v n ≫ Sigma.ι D (n + 1))
  have hcomm : φ ≫ σ = σ ≫ ψ := by
    dsimp [φ, ψ]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id]
    congr 1
    apply Sigma.hom_ext
    intro n
    have hqn : t n ≫ q (n + 1) = q n ≫ v n := by
      apply (cancel_mono (G.ιTruncLE ((n + 1 : ℕ) : ℤ))).1
      simpa only [Category.assoc, hv n] using hcompat n
    simp only [σ, Category.assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Sigma.ι_map_assoc, Sigma.ι_map]
    rw [← Category.assoc, hqn, Category.assoc]
  apply quasiIso_of_cone_map_augmentation φ ψ σ σ hcomm hσ hσ f g hg hinl hginl
  rw [hinr, hginr]
  apply Sigma.hom_ext
  intro n
  rw [Sigma.ι_map_assoc]
  conv_lhs => rw [Sigma.ι_comp_desc]
  exact (congrArg (fun z ↦ q n ≫ z)
    (Sigma.ι_comp_desc (fun n : ℕ ↦ G.ιTruncLE (n : ℤ)) n)).symm

end CochainComplex
