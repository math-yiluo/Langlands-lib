/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.LimitPullbackSectionsColimit
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
import Mathlib.Data.Finset.Order

/-!
# Eventual lifting of morphisms from finite affine etale free sheaves

Source: Stacks Project, Tags 09YU (3), 09YQ and 03S6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

private lemma transpose_comp_pullback {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (A G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Etale.upperStar (ModuleCat.{u + 1} Λ) h₂).obj A ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) h₂).obj G) :
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h₁₂).homEquiv _ _
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app A ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) h₁).map a ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app G) =
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h₂).homEquiv _ _ a ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) h₂).map
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h₁).unit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) h₂).obj G)) ≫
      (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app _ ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) h₁₂).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app G) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc,
    Etale.upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) h₁ h₂ A h₁₂ hh]
  simp only [Adjunction.comp_unit_app, Category.assoc]
  rw [← (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.naturality_assoc
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) h₁).map a)]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  erw [← (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h₁).unit.naturality a]
  simp only [Functor.map_comp, Category.assoc, Functor.id_map]

set_option maxRecDepth 4096 in
/-- Maps from a fixed finite affine free family into a pulled-back sheaf lift later.
The codomain is arbitrary, the family is already defined at i, and the comparison
is the canonical upperStar composition isomorphism. No constructibility is claimed.

Source: Stacks Project, Tag 09YU, fully faithful argument for (3), via Tag 09YQ
in degree zero, and Tag 03S6.
(blueprint: lem-weil-pbc-affine-free-etale-module-eventual-hom-lift).

Proof:
1. Write A for the finite sum of extensions by zero of the constant rank-one
   module on W. By the etale shriek/pullback and constant-sheaf adjunctions, each
   summand represents evaluation on W k; it is thus the sheaf P(W k) obtained by
   the sheafification, free-module and Yoneda adjunctions. Using the
   upperStar/lowerStar adjunction, a map from the inverse image
   of P(W k) to the inverse image of G is a section of the latter on the base change
   of W k; equivalently it is a section of lowerStar upperStar G on W k.
2. Restrict f to each coprojection, after the inverse-image coproduct comparison,
   and apply this section bijection. The surjectivity clause of
   `Etale.limit_pullback_sections_colimit` represents each generating section at
   some j_k greater than or equal to i. Directedness gives a common j and the
   theorem's transition and cocone identities transport each section to j without
   changing its image on the limit. For an empty family choose j = i.
3. Apply the inverse of the section bijection to obtain maps from each stage-i
   summand to the direct image of the stage-j pullback of G. Assemble these by
   Sigma.desc, then transpose their sum through the transition-map adjunction to
   obtain a. This avoids choosing a separate coproduct comparison.
4. The section bijection is natural. The private transpose_comp_pullback lemma
   proves its compatibility with pullback from the unit equation
   upperStarComp_hom_app_unit_app and naturality of the unit and lowerStarComp.
   Its resulting section map is exactly the map in the section-colimit theorem.
   Consequently the equation of generating sections in step 2 is the requested
   equation after precomposition with each pulled-back coprojection. The
   coproduct universal property gives the equation of arrows. With no summands
   both sides are the unique arrow from the pulled-back zero object. -/
theorem exists_affine_free_etaleModule_eventual_hom_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ]
    (i : I) (m : ℕ) (W : Fin m → (D.obj (op i)).Etale)
    (hW : ∀ k, IsAffine (W k).left)
    (G : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let Q : (D.obj (op i)).Etale →
        Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun Z ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) Z.hom inferInstance).obj
        ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ))
    let A := ∐ fun k : Fin m ↦ Q (W k)
    ∀ f : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj A ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj G,
      ∃ (j : I) (h : i ≤ j)
        (a : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj A ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G),
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op j))).map a ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
            (D.map (homOfLE h).op) (c.π.app (op i))
            (c.w (homOfLE h).op).symm).inv.app G =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
          (D.map (homOfLE h).op) (c.π.app (op i))
          (c.w (homOfLE h).op).symm).inv.app A ≫ f  := by
  classical
  intro Q A f
  have : ∀ k, IsAffine (W k).left := hW
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  let R := Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  let t (j : I) (h : i ≤ j) :=
    Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)
  let r (j : I) (h : i ≤ j) :=
    Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)
  let e (j : I) (h : i ≤ j) := Etale.upperStarComp (ModuleCat.{u + 1} Λ)
    (c.π.app (op j)) (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm
  let rho (j : I) (h : i ≤ j) : (r j h).obj ((t j h).obj G) ⟶ R.obj (L.obj G) :=
    (r j h).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op j))).unit.app
        ((t j h).obj G)) ≫
      (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
        (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm).hom.app _ ≫
      R.map ((e j h).inv.app G)
  let tau (j : I) (h : i ≤ j) (j' : I) (h' : j ≤ j') :
      (r j h).obj ((t j h).obj G) ⟶ (r j' (h.trans h')).obj ((t j' (h.trans h')).obj G) :=
    (r j h).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (D.map (homOfLE h').op)).unit.app ((t j h).obj G)) ≫
      (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
        (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
        (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
      (r j' (h.trans h')).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
          (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
          (by rw [← Functor.map_comp]; rfl)).inv.app G)
  let z (k : Fin m) := shriekEvalEquiv (W k) (R.obj (L.obj G))
    (adj.homEquiv _ _ (L.map (Sigma.ι (fun k ↦ Q (W k)) k) ≫ f))
  have hsec (k : Fin m) := Etale.limit_pullback_sections_colimit D c hc Λ i G (W k)
  have hsur (k : Fin m) : ∃ (j : I) (h : i ≤ j)
      (s : ((r j h).obj ((t j h).obj G)).obj.obj (op (W k))),
      (rho j h).hom.app (op (W k)) s = z k :=
    (hsec k).2.2.2.1 (z k)
  choose idx hidx sec hsec_eq using hsur
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image idx)).exists_le
  have h : i ≤ j := hj _ (Finset.mem_insert_self _ _)
  have hlate (k : Fin m) : idx k ≤ j :=
    hj _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, by simp, rfl⟩))
  let s (k : Fin m) : ((r j h).obj ((t j h).obj G)).obj.obj (op (W k)) :=
    (tau (idx k) (hidx k) j (hlate k)).hom.app (op (W k)) (sec k)
  have hs (k : Fin m) : (rho j h).hom.app (op (W k)) (s k) = z k :=
    ((hsec k).2.2.1 (idx k) j (hidx k) (hlate k) (sec k)).trans (hsec_eq k)
  let b (k : Fin m) : Q (W k) ⟶ (r j h).obj ((t j h).obj G) :=
    (shriekEvalEquiv (W k) _).symm (s k)
  let adjt := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (D.map (homOfLE h).op)
  let a : (t j h).obj A ⟶ (t j h).obj G := (adjt.homEquiv _ _).symm (Sigma.desc b)
  have ha : adjt.homEquiv A ((t j h).obj G) a = Sigma.desc b :=
    (adjt.homEquiv A ((t j h).obj G)).apply_symm_apply _
  refine ⟨j, h, a, ?_⟩
  apply (cancel_epi ((e j h).hom.app A)).mp
  change (e j h).hom.app A ≫ (_ ≫ (e j h).inv.app G) =
    (e j h).hom.app A ≫ ((e j h).inv.app A ≫ f)
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [Category.assoc]
  apply (adj.homEquiv _ _).injective
  rw [transpose_comp_pullback]
  apply Sigma.hom_ext
  intro k
  change Sigma.ι (fun k ↦ Q (W k)) k ≫
      (adjt.homEquiv _ _ a ≫ rho j h) =
    Sigma.ι (fun k ↦ Q (W k)) k ≫ adj.homEquiv _ _ f
  rw [ha]
  simp only [Sigma.ι_comp_desc_assoc]
  rw [← adj.homEquiv_naturality_left]
  apply (shriekEvalEquiv (W k) _).injective
  rw [shriekEvalEquiv_comp]
  change (rho j h).hom.app (op (W k))
      ((shriekEvalEquiv (W k) ((r j h).obj ((t j h).obj G)))
        ((shriekEvalEquiv (W k) ((r j h).obj ((t j h).obj G))).symm (s k))) = z k
  rw [Equiv.apply_symm_apply]
  exact hs k

end AlgebraicGeometry.Scheme
