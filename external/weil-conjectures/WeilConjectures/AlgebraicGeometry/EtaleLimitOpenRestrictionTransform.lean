/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Mathlib.Algebra.Category.Grp.AB

/-! # Restriction transformation on canonical open diagrams

Source: Stacks Project, Tags 0A50 and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Construct only the restriction transformation, with its canonical components and right square.

Source: Stacks Project, Tags 0A50 and 09YQ, naturality of restriction.
(blueprint: lem-weil-pbc-etale-limit-open-restriction-transform).

Proof: At j take the pair of the actual restrictions from H^(q+1)(F_j), conjugated
by eH, eKU and eKV, and then the inverse of the evaluation biproduct/product
comparison. The projection identities characterize this morphism. To prove
naturality, postcompose with each biproduct projection and its supplied object
isomorphism. Substitute hH, hKU and hKV; coefficient naturality and pullback
composition identify both sides. For the right square, postcompose with the
ordinary product projections and use h₄U and h₄V. Substitute the canonical
single-open leg formulas hιU and hιV, then hB. Naturality of restriction under
the restricted cone projection and the coefficient leg identifies both sides.
No connecting morphism, difference map or exactness is needed. Empty factors
and coincident opens satisfy the same projection argument. -/
theorem etale_limit_open_restriction_transform
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (q + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (q + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (q + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (q + 1)))
    (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X)
    (KU : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKU : ∀ n j, (KU n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ U j).ι).obj (F j.val)) n))
    (hKU : ∀ n j k (f : j ⟶ k), (KU n).map f =
      (eKU n j).hom ≫ tailOpenCohomologyMapDegree D g₀ U F φ n f ≫ (eKU n k).inv)
    (ιU : ∀ n, KU n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) n)))
    (hιU : ∀ n j, (ιU n).app j =
      (eKU n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ U F G eG L n j)
    (KV : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKV : ∀ n j, (KV n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ V j).ι).obj (F j.val)) n))
    (hKV : ∀ n j k (f : j ⟶ k), (KV n).map f =
      (eKV n j).hom ≫ tailOpenCohomologyMapDegree D g₀ V F φ n f ≫ (eKV n k).inv)
    (ιV : ∀ n, KV n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) n)))
    (hιV : ∀ n j, (ιV n).app j =
      (eKV n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ V F G eG L n j)
    (ι₄ : KU (q + 1) ⊞ KV (q + 1) ⟶ (Functor.const (Set.Ici i₀)).obj
      (AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) (q + 1) ×
         Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) (q + 1))))
    (h₄U : ∀ j, ι₄.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶ KU (q + 1)).app j ≫ (ιU (q + 1)).app j)
    (h₄V : ∀ j, ι₄.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶ KV (q + 1)).app j ≫ (ιV (q + 1)).app j)
 :
    let t : Set.Ici i₀ ⥤ I :=
      (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from fun _ _ h ↦ h).functor
    let WU := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V
    let BP := fun n ↦ AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) n ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) n)
    let r' : B.pt ⟶ BP (q + 1) := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt (q + 1)).prod
        (cohomologyMap WV.ι L.pt (q + 1))).comp eB.hom.hom)
    let rf := fun j ↦ (eH j.val).hom ≫ AddCommGrpCat.ofHom
      (cohomologyMap (tailStageOpen D g₀ U j).ι (F j.val) (q + 1))
    let rg := fun j ↦ (eH j.val).hom ≫ AddCommGrpCat.ofHom
      (cohomologyMap (tailStageOpen D g₀ V j).ι (F j.val) (q + 1))
    ∃ r : t ⋙ H ⟶ KU (q + 1) ⊞ KV (q + 1),
      (∀ j, r.app j ≫ ι₄.app j = B.ι.app j.val ≫ r') ∧
      (∀ j, r.app j ≫ (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶
        KU (q + 1)).app j ≫ (eKU (q + 1) j).hom = rf j) ∧
      (∀ j, r.app j ≫ (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶
        KV (q + 1)).app j ≫ (eKV (q + 1) j).hom = rg j) := by
  let t : Set.Ici i₀ ⥤ I :=
    (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from fun _ _ h ↦ h).functor
  have component (W : X.Opens) (K : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ n j, (K n).obj j ≅ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n))
      (hK : ∀ n j k (f : j ⟶ k), (K n).map f =
        (eK n j).hom ≫ tailOpenCohomologyMapDegree D g₀ W F φ n f ≫ (eK n k).inv) :
      ∃ ρ : t ⋙ H ⟶ K (q + 1), ∀ j, ρ.app j =
        (eH j.val).hom ≫ AddCommGrpCat.ofHom
          (cohomologyMap (tailStageOpen D g₀ W j).ι (F j.val) (q + 1)) ≫
            (eK (q + 1) j).inv := by
    refine ⟨{ app := fun j ↦ (eH j.val).hom ≫
                  AddCommGrpCat.ofHom
                    (cohomologyMap (tailStageOpen D g₀ W j).ι (F j.val) (q + 1)) ≫
                      (eK (q + 1) j).inv
              naturality := ?_ }, fun _ ↦ rfl⟩
    intro j k f
    dsimp only [t, Functor.comp_obj, Monotone.functor] at *
    change H.map (homOfLE (show j.val ≤ k.val from f.le)) ≫ _ =
      _ ≫ (K (q + 1)).map f
    rw [hH, hK]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hc := openSquareCoefficient_cohomology
      (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
      (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
      (tailStageOpenMap D g₀ W f)
      (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
      (F j.val) (F k.val) (φ (homOfLE (show j.val ≤ k.val from f.le))) (q + 1)
    simpa only [tailOpenCohomologyMapDegree, Category.assoc] using
      congrArg (fun m ↦ (eH j.val).hom ≫ m ≫ (eK (q + 1) k).inv) hc.symm
  obtain ⟨ρU, hρU⟩ := component U KU eKU hKU
  obtain ⟨ρV, hρV⟩ := component V KV eKV hKV
  let r : t ⋙ H ⟶ KU (q + 1) ⊞ KV (q + 1) := biprod.lift ρU ρV
  have hrU (j : Set.Ici i₀) : r.app j ≫
      (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶ KU (q + 1)).app j = ρU.app j := by
    exact congrArg (fun m ↦ m.app j) (biprod.lift_fst ρU ρV)
  have hrV (j : Set.Ici i₀) : r.app j ≫
      (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶ KV (q + 1)).app j = ρV.app j := by
    exact congrArg (fun m ↦ m.app j) (biprod.lift_snd ρU ρV)
  have leg (W : X.Opens) (K : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ n j, (K n).obj j ≅ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n))
      (ι : ∀ n, K n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n)))
      (hι : ∀ n j, (ι n).app j =
        (eK n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ W F G eG L n j)
      (ρ : t ⋙ H ⟶ K (q + 1))
      (hρ : ∀ j, ρ.app j = (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (tailStageOpen D g₀ W j).ι (F j.val) (q + 1)) ≫
          (eK (q + 1) j).inv) (j : Set.Ici i₀) :
      ρ.app j ≫ (ι (q + 1)).app j = B.ι.app j.val ≫ eB.hom ≫
        AddCommGrpCat.ofHom
          (cohomologyMap ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι L.pt (q + 1)) := by
    dsimp only [t, Functor.comp_obj, Monotone.functor] at *
    rw [hρ, hι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (B.ι.app j.val) eB.hom _, hB]
    simp only [Category.assoc]
    apply congrArg (fun m ↦ (eH j.val).hom ≫ m)
    dsimp only [tailOpenCohomologyLegDegree]
    exact openSquareCoefficient_cohomology (c.π.app (op j.val))
      (tailStageOpen D g₀ W j).ι ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
      (tailLimitOpenMap D c g₀ W j)
      (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
      ((eG j.val).inv ≫ L.ι.app j.val) (q + 1)
  dsimp only [t, Functor.comp_obj, Monotone.functor] at *
  refine ⟨r, ?_, ?_, ?_⟩
  · intro j
    ext x
    apply Prod.ext
    · have h := congrArg (fun m ↦ r.app j ≫ m) (h₄U j)
      simp only [← Category.assoc, hrU] at h
      have hl := leg U KU eKU ιU hιU ρU hρU j
      exact (congrArg (fun m ↦ m x) h).trans (congrArg (fun m ↦ m x) hl)
    · have h := congrArg (fun m ↦ r.app j ≫ m) (h₄V j)
      simp only [← Category.assoc, hrV] at h
      have hl := leg V KV eKV ιV hιV ρV hρV j
      exact (congrArg (fun m ↦ m x) h).trans (congrArg (fun m ↦ m x) hl)
  · intro j
    rw [← Category.assoc, hrU, hρU]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro j
    rw [← Category.assoc, hrV, hρV]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale
