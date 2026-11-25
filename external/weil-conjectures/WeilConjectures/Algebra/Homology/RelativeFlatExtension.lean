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
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# A relative flat replacement before imposing termwise epimorphy

Source: Stacks Project, Derived Categories, Lemma 06XX, triangle and homotopy
correction part of the induction step.
(blueprint: lem-pc-relative-flat-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

private theorem flat_biprod
    (M N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hM : SheafOfModules.IsFlat M) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat (M ⊞ N) := by
  let := SheafOfModules.monoidalCategory R
  let k : ULift.{u} WalkingPair → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun j ↦ (Limits.pair M N).obj ⟨j.down⟩
  have hk : SheafOfModules.IsFlat (∐ k) :=
    SheafOfModules.isFlat_coproduct R k (fun ⟨j⟩ ↦ by cases j <;> assumption)
  let k' : WalkingPair → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun j ↦ (Limits.pair M N).obj ⟨j⟩
  let e : (∐ k) ≅ M ⊞ N :=
    Sigma.whiskerEquiv (f := k) (g := k') Equiv.ulift (fun _ ↦ Iso.refl _) ≪≫
      (HasColimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _) : ∐ k' ≅ M ⨿ N) ≪≫
      (biprod.isoCoprod M N).symm
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e) hk

-- The twisted-sum construction only uses the abelian category and closure under biproducts.
private theorem relative_extension_of_flat_biprod
    {B : Type*} [Category* B] [Abelian B]
    (P : B → Prop) (hP : ∀ M N, P M → P N → P (M ⊞ N))
    (E H : CochainComplex B ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, P (E.X i))
    (Q : CochainComplex B ℤ) (r : Q ⟶ mappingCone f)
    (hQ : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (Q.X i))
    (hflatQ : ∀ i : ℤ, P (Q.X i)) (hr : QuasiIso r) :
    ∃ (F : CochainComplex B ℤ) (t : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, P (F.X i)) ∧ QuasiIso g ∧ t ≫ g = f := by
  -- Realize the triangle directly: the cone coordinates of r determine the twisted sum.
  let a (i : ℤ) := r.f i ≫ (mappingCone.fst f).1.v i (i + 1) rfl
  let b (i : ℤ) := r.f i ≫ (mappingCone.snd f).v i i (add_zero i)
  have ha (i : ℤ) :
      a i ≫ E.d (i + 1) (i + 1 + 1) + Q.d i (i + 1) ≫ a (i + 1) = 0 := by
    dsimp [a]
    have eq := r.comm i (i + 1)
    simp only [← Category.assoc] at eq ⊢
    rw [← eq]
    simp only [Category.assoc, mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
      Preadditive.comp_neg, add_neg_cancel]
  have hb (i : ℤ) : Q.d i (i + 1) ≫ b (i + 1) =
      a i ≫ f.f (i + 1) + b i ≫ H.d i (i + 1) := by
    dsimp [a, b]
    rw [← Category.assoc, ← r.comm, Category.assoc, mappingCone.d_snd_v f i
      (i + 1) rfl]
    simp [Preadditive.comp_add, Category.assoc]
  let d (i : ℤ) : E.X i ⊞ Q.X i ⟶ E.X (i + 1) ⊞ Q.X (i + 1) :=
    biprod.desc (E.d i (i + 1) ≫ biprod.inl)
      (-a i ≫ biprod.inl + Q.d i (i + 1) ≫ biprod.inr)
  have hd (i : ℤ) : d i ≫ d (i + 1) = 0 := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    have eq := ha i
    simpa only [Preadditive.neg_comp, neg_add, neg_zero] using congrArg Neg.neg eq
  let F := CochainComplex.of (fun i ↦ E.X i ⊞ Q.X i) d hd
  let t : E ⟶ F := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro i
    simp [F, d])
  let g : F ⟶ H := CochainComplex.ofHom (fun i ↦ biprod.desc (f.f i) (b i)) (by
    intro i
    apply biprod.hom_ext'
    · simp [F, d, f.comm]
    · simp [F, d, Preadditive.add_comp, Category.assoc, hb])
  refine ⟨F, t, g, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hE
    obtain ⟨q, hq⟩ := hQ
    refine ⟨max e q, fun i hi ↦ ?_⟩
    exact (biprod_isZero_iff _ _).2
      ⟨he i (lt_of_le_of_lt (le_max_left _ _) hi),
        hq i (lt_of_le_of_lt (le_max_right _ _) hi)⟩
  · intro i
    exact hP (E.X i) (Q.X i) (hflat i) (hflatQ i)
  -- Cone(g) and Cone(r) have the same three summands, in different orders.
  · let e (i : ℤ) : (mappingCone g).X i ≅ (mappingCone r).X i :=
      { hom :=
          ((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd) ≫
              (mappingCone.inl r).v (i + 1) i (by omega) +
            (((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst) ≫
                (mappingCone.inl f).v (i + 1) i (by omega) +
              (mappingCone.snd g).v i i (add_zero i) ≫ (mappingCone.inr f).f i) ≫
                (mappingCone.inr r).f i
        inv :=
          biprod.lift
              ((mappingCone.snd r).v i i (add_zero i) ≫
                (mappingCone.fst f).1.v i (i + 1) rfl)
              ((mappingCone.fst r).1.v i (i + 1) rfl) ≫
                (mappingCone.inl g).v (i + 1) i (by omega) +
            ((mappingCone.snd r).v i i (add_zero i) ≫
              (mappingCone.snd f).v i i (add_zero i)) ≫ (mappingCone.inr g).f i
        hom_inv_id := by
          apply mappingCone.ext_from g (i + 1) i rfl
          · apply biprod.hom_ext'
            all_goals
              apply mappingCone.ext_to g i (i + 1) rfl
              · apply biprod.hom_ext
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_to g i (i + 1) rfl
            · apply biprod.hom_ext
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
        inv_hom_id := by
          apply mappingCone.ext_from r (i + 1) i rfl
          · apply mappingCone.ext_to r i (i + 1) rfl
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · apply mappingCone.ext_to f i (i + 1) rfl
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_from f (i + 1) i rfl
            all_goals
              apply mappingCone.ext_to r i (i + 1) rfl
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · apply mappingCone.ext_to f i (i + 1) rfl
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add] }
    have he₁ (i : ℤ) : (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl =
        (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₂ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.fst f).1.v i (i + 1) rfl =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₃ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.snd f).v i i (add_zero i) =
          (mappingCone.snd g).v i i (add_zero i) := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₁' (i : ℤ) {Z : B}
        (k : Q.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl ≫ k =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd ≫ k := by
      rw [← Category.assoc, he₁, Category.assoc]
    have he₂' (i : ℤ) {Z : B}
        (k : E.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.fst f).1.v i (i + 1) rfl ≫ k =
            (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst ≫ k := by
      simp only [← Category.assoc, he₂]
    have he₃' (i : ℤ) {Z : B}
        (k : H.X i ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.snd f).v i i (add_zero i) ≫ k =
            (mappingCone.snd g).v i i (add_zero i) ≫ k := by
      simp only [← Category.assoc, he₃]
    have hd₁ (i : ℤ) : F.d i (i + 1) ≫ biprod.fst =
        biprod.fst ≫ E.d i (i + 1) - biprod.snd ≫ a i := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.comp_sub, Preadditive.add_comp, Category.assoc]
    have hd₂ (i : ℤ) : F.d i (i + 1) ≫ biprod.snd =
        biprod.snd ≫ Q.d i (i + 1) := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.add_comp, Category.assoc]
    have hg (i : ℤ) : g.f i = biprod.fst ≫ f.f i + biprod.snd ≫ b i := by
      change biprod.desc _ _ = _
      exact biprod.desc_eq
    let ec : mappingCone g ≅ mappingCone r :=
      HomologicalComplex.Hom.isoOfComponents e (by
        rintro i _ rfl
        apply mappingCone.ext_to r (i + 1) (i + 1 + 1) rfl
        · simp only [Category.assoc,
            mappingCone.d_fst_v r i (i + 1) (i + 1 + 1) rfl rfl,
            Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₁,
            mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
            hd₂]
        · apply mappingCone.ext_to f (i + 1) (i + 1 + 1) rfl
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
              Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₂', he₂,
              mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
              hd₁, Preadditive.comp_sub]
            change _ ≫ _ ≫ a (i + 1) + -(_ ≫ _ ≫ _) = -(_ - _)
            abel
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_snd_v f i (i + 1) rfl,
              he₁', he₂', he₃', he₃,
              mappingCone.d_snd_v g i (i + 1) rfl, hg, Preadditive.comp_add]
            change _ ≫ _ ≫ b (i + 1) + (_ + _) = (_ + _) + _
            abel)
    apply (mappingCone.quasiIso_iff_acyclic g).2
    have hc := (mappingCone.quasiIso_iff_acyclic r).1 hr
    intro i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hc i)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso ec)
  · ext i
    simp [t, g]

/-- A flat replacement of a mapping cone gives a relative flat replacement,
strictly as chain maps.
Termwise epimorphy of the new resolution is not asserted here.

Source: Stacks Project, Derived Categories, Lemma 06XX, triangle construction
and homotopy correction (https://stacks.math.columbia.edu/tag/06XX).
(blueprint: lem-pc-relative-flat-extension).

Proof: The prescribed quasi-isomorphism r : Q -> Cone(f), followed by the
cone projection to E[1], determines a triangle
E -> F -> Q -> E[1]. Realize it by the shifted cone of this composite; the
sequence E -> F -> Q is degreewise split and F^i is E^i plus Q^i. Thus F is
bounded above and flat by finite coproduct flatness. The cone triangle and this
triangle give a morphism of triangles with identity on E and Q -> C on the
third term. The middle map g : F -> H is a quasi-isomorphism by the long exact
cohomology sequences. The square with E commutes up to homotopy. Extend the
homotopy degreewise from E to F using the split retractions and subtract its
homotopy differential from g. This changes neither its cohomology maps nor its
chain-map property and gives t >> g = f strictly. Neither f nor its components
need be quasi-isomorphisms or epimorphisms. For E = 0 the given Q resolves H;
for H = 0 the cone construction still applies. Bounds on E and Q may differ. -/
theorem exists_relative_boundedAbove_flat_extension
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i))
    (Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (r : Q ⟶ mappingCone f)
    (hQ : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (Q.X i))
    (hflatQ : ∀ i : ℤ, SheafOfModules.IsFlat (Q.X i)) (hr : QuasiIso r) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (t : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso g ∧ t ≫ g = f := by
  exact relative_extension_of_flat_biprod
    (B := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (SheafOfModules.IsFlat (R := R)) (flat_biprod (R := R))
    E H f hE hflat Q r hQ hflatQ hr

end CochainComplex
