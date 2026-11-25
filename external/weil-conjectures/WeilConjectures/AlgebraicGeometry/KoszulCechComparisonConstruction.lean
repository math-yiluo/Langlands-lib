/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedDifferential

/-! # The canonical Koszul-to-Čech comparison

Source: Stacks Project, Tags 08CX, 08D0 and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
The power system, its colimit, and its comparison map retain the explicit basis formula
and the totalization sign of Tag 08D1. Existence proofs supply only verification data.
-/

@[expose] public section

universe uK wK vK

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)

variable (M : CochainComplex (ModuleCat.{uK} A) ℤ)

private def koszulCechPrecomp
    {L N : CochainComplex (ModuleCat.{uK} A) ℤ} (g : L ⟶ N) :
    CochainComplex.moduleHomComplex N M ⟶ CochainComplex.moduleHomComplex L M where
  f n := ModuleCat.ofHom
    { toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom g).comp z (zero_add n)
      map_add' := fun z z' ↦ CochainComplex.HomComplex.Cochain.comp_add _ z z' _
      map_smul' := fun a z ↦ CochainComplex.HomComplex.Cochain.comp_smul _ a z _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact CochainComplex.HomComplex.δ_ofHom_comp g z m

/-- The directed Hom-complex diagram with transitions given by precomposition.
The exponent at index e is e+1. Source: Stacks, Tags 08CX and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
Proof: extend koszulOpenTransition by zero and precompose Mathlib's linear cochains.
The chain-map identity and the signed Hom differential give commutation with d.
Identity and composition follow from the diagonal exterior-power comparison laws. -/
theorem koszulCechHomDiagram_exists :
    ∃ D : ℕ ⥤ CochainComplex (ModuleCat.{uK} A) ℤ,
      (∀ e, D.obj e = CochainComplex.moduleHomComplex
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M) ∧
      (∀ (a b : ℕ) (h : a ≤ b) (n : ℤ)
        (z : CochainComplex.HomComplex.Cochain
          ((koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat) M n)
        (ha : D.obj a = CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat) M)
        (hb : D.obj b = CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f b).extend ComplexShape.embeddingDownNat) M),
        ((eqToHom ha.symm ≫ D.map (homOfLE h) ≫ eqToHom hb).f n) z =
          (CochainComplex.HomComplex.Cochain.ofHom
            (HomologicalComplex.extendMap (koszulOpenTransition A r f a b h)
              ComplexShape.embeddingDownNat)).comp z (zero_add n)) := by
  let D : ℕ ⥤ CochainComplex (ModuleCat.{uK} A) ℤ :=
    { obj := fun e ↦ CochainComplex.moduleHomComplex
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
      map := fun {a b} h ↦ koszulCechPrecomp A M
        (HomologicalComplex.extendMap (koszulOpenTransition A r f a b (leOfHom h))
          ComplexShape.embeddingDownNat)
      map_id := by
        intro a
        apply HomologicalComplex.hom_ext
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (CochainComplex.HomComplex.Cochain.ofHom
          (HomologicalComplex.extendMap (koszulOpenTransition A r f a a _) _)).comp
            z (zero_add n) = z
        rw [koszulOpenTransition_id, HomologicalComplex.extendMap_id]
        exact CochainComplex.HomComplex.Cochain.id_comp z
      map_comp := by
        intro a b c hab hbc
        apply HomologicalComplex.hom_ext
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (CochainComplex.HomComplex.Cochain.ofHom
          (HomologicalComplex.extendMap (koszulOpenTransition A r f a c _) _)).comp
            z (zero_add n) =
          (CochainComplex.HomComplex.Cochain.ofHom
            (HomologicalComplex.extendMap (koszulOpenTransition A r f b c _) _)).comp
              ((CochainComplex.HomComplex.Cochain.ofHom
                (HomologicalComplex.extendMap (koszulOpenTransition A r f a b _) _)).comp
                  z (zero_add n)) (zero_add n)
        rw [← CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
          ← CochainComplex.HomComplex.Cochain.ofHom_comp,
          ← HomologicalComplex.extendMap_comp,
          koszulOpenTransition_comp A r f a b c (leOfHom hab) (leOfHom hbc)] }
  refine ⟨D, fun _ ↦ rfl, ?_⟩
  intro a b h n z ha hb
  have hha : ha = rfl := Subsingleton.elim _ _
  have hhb : hb = rfl := Subsingleton.elim _ _
  rw [hha, hhb]
  rfl

/-- The specified filtered system of A-linear total Hom complexes.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomDiagram : ℕ ⥤ CochainComplex (ModuleCat.{uK} A) ℤ :=
  (koszulCechHomDiagram_exists A r f M).choose

/-- The object identification at every positive exponent.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomObjIso (e : ℕ) : (koszulCechHomDiagram A r f M).obj e ≅
    CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M :=
  eqToIso ((koszulCechHomDiagram_exists A r f M).choose_spec.1 e)

/-- The direct limit in the category of complexes, hence computed degreewise.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomColimit : CochainComplex (ModuleCat.{uK} A) ℤ :=
  colimit (koszulCechHomDiagram A r f M)

/-- Cardinality identifies the Koszul term for a nonempty subset.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: a nonempty finite set has positive cardinality, so truncated subtraction gives
card(J)-1+1 = card(J). -/
theorem koszulCech_basis_card (J : Finset (Fin r)) (hJ : J.Nonempty) :
    J.card = J.card - 1 + 1 := by
  have h : 0 < J.card := Finset.card_pos.mpr hJ
  omega

/-- The extended tail degree attached to the subset J.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: card(J)>0, so negating card(J)-1 gives 1-card(J) in integer degrees. -/
theorem koszulCech_basis_degree (J : Finset (Fin r)) (hJ : J.Nonempty) :
    ComplexShape.embeddingDownNat.f (J.card - 1) = 1 - (J.card : ℤ) := by
  simp only [ComplexShape.embeddingDownNat_f]
  have h : 0 < J.card := Finset.card_pos.mpr hJ
  omega

/-- The ordered exterior basis vector in the Koszul tail, transported by extension.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechBasis (e : ℕ) (J : Finset (Fin r)) (hJ : J.Nonempty) :
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X (1 - (J.card : ℤ)) :=
  ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
    (koszulCech_basis_degree r J hJ)).inv
      (exteriorPower.ιMulti A (J.card - 1 + 1)
        (fun i ↦ Finsupp.single (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) (1 : A)))

private theorem koszulCechBasis_transition (a b : ℕ) (hab : a ≤ b)
    (J : Finset (Fin r)) (hJ : J.Nonempty) :
    (HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
      ComplexShape.embeddingDownNat).f (1 - (J.card : ℤ))
        (koszulCechBasis A r f b J hJ) =
      (∏ j ∈ J, f j) ^ (b - a) • koszulCechBasis A r f a J hJ := by
  rw [HomologicalComplex.extendMap_f _ _ (koszulCech_basis_degree r J hJ)]
  simp only [koszulCechBasis, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change ((koszulOpenTail A r f a).extendXIso ComplexShape.embeddingDownNat
      (koszulCech_basis_degree r J hJ)).inv
        (exteriorPower.map (J.card - 1 + 1) (koszulOpenDiagonal A r f (b - a))
          (exteriorPower.ιMulti A (J.card - 1 + 1)
            (fun i ↦ Finsupp.single (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i)
              (1 : A)))) = _
  rw [exteriorPower.map_apply_ιMulti]
  have hdiag : ∀ i : Fin (J.card - 1 + 1),
      koszulOpenDiagonal A r f (b - a)
          (Finsupp.single (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) 1) =
        f (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) ^ (b - a) •
          Finsupp.single (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) 1 := by
    intro i
    simp [koszulOpenDiagonal, Finsupp.linearCombination_single, Finsupp.smul_single]
  simp only [Function.comp_def, hdiag]
  rw [AlternatingMap.map_smul_univ]
  have hprod : (∏ i : Fin (J.card - 1 + 1),
      f (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) ^ (b - a)) =
        (∏ j ∈ J, f j) ^ (b - a) := by
    have hh := Finset.prod_map Finset.univ
      (J.orderEmbOfFin (koszulCech_basis_card r J hJ)).toEmbedding f
    rw [Finset.map_orderEmbOfFin_univ] at hh
    simpa only [Finset.prod_pow, RelEmbedding.coe_toEmbedding] using
      congrArg (fun x : A ↦ x ^ (b - a)) hh.symm
  rw [hprod]
  exact ((koszulOpenTail A r f a).extendXIso ComplexShape.embeddingDownNat
    (koszulCech_basis_degree r J hJ)).inv.hom.map_smul _ _

/-- The degree equality for evaluating a homogeneous Hom cochain on a basis vector.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: rearrange addition in ℤ. -/
theorem koszulCech_evaluation_degree (J : Finset (Fin r)) (n : ℤ) :
    1 - (J.card : ℤ) + n = n + 1 - (J.card : ℤ) := by
  ring

variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- Existence of the compatible Koszul-to-Čech cocone, with the denominator and sign formula.
The equation determines the localized value, since the product of the f_j is invertible
on its principal open. Source: Stacks, Tags 08D0 and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
Proof: restrict evaluation on the ordered wedge e_J to D(product f_j), divide by
(product f_j)^(e+1), and multiply by (-1)^(pq+p(p-1)/2), where p=card(J)-1 and q=n-p.
The negative tail differential and the signed Hom differential turn into the alternating
Čech total differential with this sign. A power transition multiplies e_J by product f_j,
so the fractions are compatible. This constructs a cocone without any quasi-coherence
hypothesis; quasi-coherence is only needed for it to be an isomorphism. -/
theorem koszulCechCocone_exists :
    ∃ c : Cocone (koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)),
      c.pt = (principalCechFunctor r f).obj F ∧
      ∀ (e : ℕ) (n : ℤ)
        (z : CochainComplex.HomComplex.Cochain
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
          (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
        (J : {J : Finset (Fin r) // J.Nonempty})
        (hc : c.pt = (principalCechFunctor r f).obj F),
        (∏ j ∈ J.val, f j) ^ (e + 1) •
          (((koszulCechHomObjIso A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
              e).inv ≫ c.ι.app e ≫ eqToHom hc ≫ (principalCechObjIso r f F).hom).f n) z J =
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          (modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
            ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
              (koszulCech_evaluation_degree r J.val n))
                (koszulCechBasis A r f e J.val J.property)) := by
  let M := (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
  let D := koszulCechHomDiagram A r f M
  let B (e : ℕ) (J : {J : Finset (Fin r) // J.Nonempty}) :=
    koszulCechBasis A r f e J.val J.property
  let g (e : ℕ) : CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M ⟶
        principalCechTotal r f F :=
    { f := fun n ↦ koszulCechLocalizedDegreeMap A r f F e n (B e)
      comm' := by
        intro n m h
        have hm : n + 1 = m := h
        subst m
        exact (koszulCechLocalizedDegreeMap_comm A r f F e (B e) (fun _ ↦ rfl) n).symm }
  have hg (e : ℕ) (n : ℤ)
      (z : CochainComplex.HomComplex.Cochain
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M n)
      (J : {J : Finset (Fin r) // J.Nonempty}) :
      (∏ j ∈ J.val, f j) ^ (e + 1) • (g e).f n z J =
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          (modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
            ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
              (koszulCech_evaluation_degree r J.val n))
                (koszulCechBasis A r f e J.val J.property)) := by
    change (∏ j ∈ J.val, f j) ^ (e + 1) •
        ((_ : ℤˣ) • koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ)))
          (∏ j ∈ J.val, f j) (e + 1) _) = _
    rw [smul_comm]
    congr 1
    exact (koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ)))
      (∏ j ∈ J.val, f j) (e + 1)).symm_apply_apply _
  have hcompat (a b : ℕ) (hab : a ≤ b) :
      koszulCechPrecomp A M
        (HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
          ComplexShape.embeddingDownNat) ≫ g b = g a := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext J
    let N := (affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X (n + 1 - (J.val.card : ℤ)))
    have hreg : IsSMulRegular (↑N) (∏ j ∈ J.val, f j) :=
      Scheme.Modules.isSMulRegular_of_le_basicOpen
        (M := F.X (n + 1 - (J.val.card : ℤ))) le_rfl
    apply hreg.pow (b + 1)
    change (∏ j ∈ J.val, f j) ^ (b + 1) •
        (g b).f n ((CochainComplex.HomComplex.Cochain.ofHom
          (HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
            ComplexShape.embeddingDownNat)).comp z (zero_add n)) J =
      (∏ j ∈ J.val, f j) ^ (b + 1) • (g a).f n z J
    apply (hg b n _ J).trans
    have hexp : b + 1 = (b - a) + (a + 1) := by omega
    rw [hexp, pow_add, mul_smul, hg a n z J]
    simp only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, ModuleCat.comp_apply,
      koszulCechBasis_transition A r f a b hab J.val J.property,
      map_smul]
    exact @smul_comm ℤˣ A N _ _ _ _ _ _
  let ι (e : ℕ) : D.obj e ⟶ (principalCechFunctor r f).obj F :=
    (koszulCechHomObjIso A r f M e).hom ≫ g e ≫ (principalCechObjIso r f F).inv
  have hι (a b : ℕ) (hab : a ≤ b) : D.map (homOfLE hab) ≫ ι b = ι a := by
    apply (cancel_mono (principalCechObjIso r f F).hom).mp
    apply (cancel_epi (koszulCechHomObjIso A r f M a).inv).mp
    simp only [ι, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    have hmap : (koszulCechHomObjIso A r f M a).inv ≫
        D.map (homOfLE hab) ≫ (koszulCechHomObjIso A r f M b).hom =
      koszulCechPrecomp A M
        (HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
          ComplexShape.embeddingDownNat) := by
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (koszulCechHomDiagram_exists A r f M).choose_spec.2 a b hab n z
        ((koszulCechHomDiagram_exists A r f M).choose_spec.1 a)
        ((koszulCechHomDiagram_exists A r f M).choose_spec.1 b)
    simpa only [← Category.assoc, hmap] using hcompat a b hab
  let c : Cocone D :=
    { pt := (principalCechFunctor r f).obj F
      ι := { app := ι
             naturality := by
               intro a b h
               have h' : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
               simpa [h'] using hι a b (leOfHom h) } }
  refine ⟨c, rfl, ?_⟩
  intro e n z J hc
  have hhc : hc = rfl := Subsingleton.elim _ _
  rw [hhc]
  change (∏ j ∈ J.val, f j) ^ (e + 1) •
      (((koszulCechHomObjIso A r f M e).inv ≫
        ((koszulCechHomObjIso A r f M e).hom ≫ g e ≫
          (principalCechObjIso r f F).inv) ≫ 𝟙 _ ≫
            (principalCechObjIso r f F).hom).f n) z J = _
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hg e n z J

/-- The canonical cocone supplied by the explicit localization formula.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechCocone := (koszulCechCocone_exists A r f F).choose

/-- The canonical colimit comparison to alternating Čech totalization.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechComparison :
    koszulCechHomColimit A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ⟶
        (principalCechFunctor r f).obj F :=
  colimit.desc _ (koszulCechCocone A r f F) ≫
    eqToHom (koszulCechCocone_exists A r f F).choose_spec.1

variable [HasDerivedCategory.{wK}
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vK} (ModuleCat.{uK} A)]

/-- The canonical map from the Koszul Hom colimit to RΓ(U,F), through alternating Čech.
Source: Stacks, Tags 08D1 and 08D2
(blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechDerivedComparison :
    DerivedCategory.Q.obj (koszulCechHomColimit A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) ⟶
        (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map (koszulCechComparison A r f F) ≫
    principalCechDerivedComparison r f F

end
end AlgebraicGeometry
