/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation
import WeilConjectures.AlgebraicGeometry.Morphisms.CartesianFamilyGenericLimit

/-!
# A normal Noetherian family system and its pointed generic fibres

## References

* Stacks Project, Tag 0EZJ, limit reduction before descent of the cover
* Stacks Project, Tag 0EZJ, proof of Lemma 58.31.9, paragraphs from absolute Noetherian
  approximation through the assertion that the generic fibre is a limit
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Approximate a smooth pointed family, retaining the inverse systems of its generic
fibres and generic base points. No finite cover or group action is involved. -/
theorem exists_normal_family_generic_limit {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ) :
    ∃ (I : Type u) (hcat : SmallCategory I),
      letI : SmallCategory I := hcat
      ∃ (_ : IsCofiltered I) (D K : I ⥤ Scheme.{u})
        (κ : (Functor.const I).obj Cη ⟶ D)
        (b : (Functor.const I).obj (Spec S.functionField) ⟶ K) (s : K ⟶ D),
        ∃ (_ : IsLimit (Cone.mk Cη κ))
          (_ : IsLimit (Cone.mk (Spec S.functionField) b)),
        (∀ i, CompactSpace (D.obj i)) ∧ (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
        (∀ i, CompactSpace (K.obj i)) ∧ (∀ i, QuasiSeparatedSpace (K.obj i)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f)) ∧
        (∀ i, sη ≫ κ.app i = b.app i ≫ s.app i) ∧
        ∃ (S₀ C₀ : I → Scheme.{u}) (hI₀ : ∀ i, IsIntegral (S₀ i)),
          letI : ∀ i, IsIntegral (S₀ i) := hI₀
          ∃ (c₀ : ∀ i, C₀ i ⟶ S₀ i) (σ₀ : ∀ i, S₀ i ⟶ C₀ i)
            (q₀ : ∀ i, D.obj i ⟶ Spec (S₀ i).functionField)
            (j₀ : ∀ i, D.obj i ⟶ C₀ i)
            (e : ∀ i, K.obj i ≅ Spec (S₀ i).functionField) (a : ∀ i, C ⟶ C₀ i),
            ∀ i, IsNoetherian (S₀ i) ∧ QuasiSeparatedSpace (S₀ i) ∧
              (∀ x : S₀ i, IsIntegrallyClosed ((S₀ i).presheaf.stalk x)) ∧
              QuasiCompact (c₀ i) ∧ QuasiSeparated (c₀ i) ∧ Smooth (c₀ i) ∧
              GeometricallyConnected (c₀ i) ∧ σ₀ i ≫ c₀ i = 𝟙 (S₀ i) ∧
              IsUnit (n : Γ(S₀ i, ⊤)) ∧
              IsPullback (q₀ i) (j₀ i) ((S₀ i).fromSpecStalk (genericPoint (S₀ i)))
                (c₀ i) ∧
              (e i).inv ≫ s.app i ≫ q₀ i = 𝟙 _ ∧
              (e i).inv ≫ s.app i ≫ j₀ i =
                (S₀ i).fromSpecStalk (genericPoint (S₀ i)) ≫ σ₀ i ∧
              κ.app i ≫ j₀ i = j ≫ a i := by
  classical
  obtain ⟨I, hcat, hmodel⟩ :=
    exists_normal_pointed_family_approximation hS c σ hσ n hn
  let : SmallCategory I := hcat
  obtain ⟨hco, X, Y, α, γ, hα, hγ, p, τ, hI, hXa, hdom, hcart, htrans,
    hσproj, hstage⟩ := hmodel
  let : IsCofiltered I := hco
  let : ∀ i, IsIntegral (X.obj i) := hI
  have hXqc (i : I) : CompactSpace (X.obj i) := by
    let : IsNoetherian (X.obj i) := (hstage i).1
    infer_instance
  have hXqs (i : I) : QuasiSeparatedSpace (X.obj i) := (hstage i).2.1
  have hpqc (i : I) : QuasiCompact (p.app i) := (hstage i).2.2.2.1
  have hpqs (i : I) : QuasiSeparated (p.app i) := (hstage i).2.2.2.2.1
  have hsec (i : I) : τ.app i ≫ p.app i = 𝟙 _ := (hstage i).2.2.2.2.2.2.2.1
  obtain ⟨D, K, κ, b, r, δ, t, e, hκ, hb, hDqc, hDqs, hKqc, hKqs, hDa, hKa,
    hpb, he, hκr, hκδ, hbt⟩ :=
    exists_cartesian_family_generic_limit X Y hXqc hXqs hXa α γ hα hγ c p
      hpqc hpqs hdom hcart htrans q j hCη
  let sectionMap (i : I) : K.obj i ⟶ D.obj i :=
    (hpb i).lift (𝟙 _) (t.app i ≫ τ.app i) (by simp [Category.assoc, hsec])
  have hsr (i : I) : sectionMap i ≫ r.app i = 𝟙 _ := by simp [sectionMap]
  have hsδ (i : I) : sectionMap i ≫ δ.app i = t.app i ≫ τ.app i := by
    simp [sectionMap]
  let s : K ⟶ D :=
    { app := sectionMap
      naturality := by
        intro i i' f
        apply (hpb i').hom_ext
        · rw [Category.assoc, hsr, Category.comp_id, Category.assoc,
            r.naturality, ← Category.assoc, hsr, Category.id_comp]
        · rw [Category.assoc, hsδ, t.naturality_assoc, τ.naturality,
            ← Category.assoc, ← hsδ, Category.assoc, ← δ.naturality, Category.assoc] }
  have hs (i : I) : sη ≫ κ.app i = b.app i ≫ s.app i := by
    apply (hpb i).hom_ext
    · change (sη ≫ κ.app i) ≫ r.app i = (b.app i ≫ sectionMap i) ≫ r.app i
      rw [Category.assoc, hκr, ← Category.assoc, hsq, Category.id_comp,
        Category.assoc, hsr, Category.comp_id]
    · change (sη ≫ κ.app i) ≫ δ.app i = (b.app i ≫ sectionMap i) ≫ δ.app i
      rw [Category.assoc, hκδ, ← Category.assoc, hsj, Category.assoc, hσproj,
        ← Category.assoc, ← hbt, Category.assoc, Category.assoc, hsδ]
  refine ⟨I, hcat, hco, D, K, κ, b, s, hκ, hb, hDqc, hDqs, hKqc, hKqs,
    hDa, hKa, hs, (fun i ↦ X.obj i), (fun i ↦ Y.obj i), hI, p.app, τ.app,
    (fun i ↦ r.app i ≫ (e i).hom), δ.app, e, γ.app, ?_⟩
  intro i
  obtain ⟨hN, hqs, hnormal, hqc, hqsc, hsm, hconn, hsec₀, hn₀⟩ := hstage i
  refine ⟨hN, hqs, hnormal, hqc, hqsc, hsm, hconn, hsec₀, hn₀, ?_, ?_, ?_, hκδ i⟩
  · apply (hpb i).of_iso (Iso.refl _) (e i) (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · have h := congrArg (fun f ↦ (e i).hom ≫ f) (he i)
      simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
        Category.comp_id, Iso.refl_hom] using h
    · simp
  · change ((e i).inv ≫ sectionMap i) ≫ (r.app i ≫ (e i).hom) = 𝟙 _
    rw [Category.assoc, ← Category.assoc (sectionMap i), hsr,
      Category.id_comp, Iso.inv_hom_id]
  · change ((e i).inv ≫ sectionMap i) ≫ δ.app i =
      (X.obj i).fromSpecStalk (genericPoint (X.obj i)) ≫ τ.app i
    rw [Category.assoc, hsδ, ← Category.assoc, he]


end AlgebraicGeometry.Scheme
