/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedKoszulDualBasis

/-! # Finite exterior Koszul complexes under scalar realization

Source: Stacks Project, more-algebra.tex, lemma-join-sequences-koszul-complex
(0664), and algebraization.tex, lemma-derived-completion-koszul (0A0E).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private def indexEquiv (r k : ℕ) (q : ℤ) (h : -(k : ℤ) = q) :
    Set.powersetCard (Fin r) k ≃ exteriorKoszulIndex r q where
  toFun I := ⟨I.1, by rw [I.2]; exact h.symm⟩
  invFun I := ⟨I.1, by
    change I.1.card = k
    have hi : q = -(I.1.card : ℤ) := I.2
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ordered exterior basis has the coproduct universal property. -/
private theorem isColimit_exteriorKoszulBasis {A : Type w} [CommRing A]
    (r : ℕ) (f : Fin r → A) (q : ℤ) :
    Nonempty (IsColimit (Cofan.mk ((exteriorKoszulExtended r f).X q)
      (exteriorKoszulBasis r f q))) := by
  classical
  by_cases hq : q ≤ 0
  · let k := (-q).toNat
    have hk : -(k : ℤ) = q := by dsimp [k]; omega
    let e := indexEquiv r k q hk
    let b := ((Finsupp.basisSingleOne :
      Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower k).reindex e
    let z := (ExteriorAlgebra.koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat hk
    have hb (I : exteriorKoszulIndex r q) : exteriorKoszulBasis r f q I =
        ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight (b I)) ≫ z.inv := by
      simp only [exteriorKoszulBasis, b, Module.Basis.reindex_apply, e, indexEquiv]
      rfl
    refine ⟨Cofan.IsColimit.mk _ (fun s ↦ z.hom ≫
      ModuleCat.ofHom (b.constr A (fun I ↦ s.inj I 1))) ?_ ?_⟩
    · intro s I
      change exteriorKoszulBasis r f q I ≫ _ = _
      rw [hb]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change b.constr A (fun I ↦ s.inj I 1) (x • b I) = s.inj I x
      simp only [map_smul, Module.Basis.constr_basis]
      simpa using (s.inj I).hom.map_smul x (1 : A) |>.symm
    · intro s g hg
      apply (cancel_epi z.inv).1
      simp only [Iso.inv_hom_id_assoc]
      apply ModuleCat.hom_ext
      apply b.ext
      intro I
      have hi := hg I
      change exteriorKoszulBasis r f q I ≫ g = s.inj I at hi
      rw [hb] at hi
      replace hi := congrArg (fun t ↦ t (1 : A)) hi
      simpa using hi
  · have hz : IsZero ((exteriorKoszulExtended r f).X q) := by
      apply HomologicalComplex.isZero_extend_X
      intro k
      change -(k : ℤ) ≠ q
      omega
    have : IsEmpty (exteriorKoszulIndex r q) := ⟨fun I ↦ by have := I.2; omega⟩
    refine ⟨Cofan.IsColimit.mk _ (fun _ ↦ 0) ?_ ?_⟩
    · intro s I
      exact isEmptyElim I
    · intro s g _
      exact hz.eq_of_src _ _

/-- A diagonal acts on an ordered wedge by the product of its entries. -/
private theorem exteriorKoszulBasis_diagonal {A : Type w} [CommRing A]
    (r : ℕ) (f g d : Fin r → A)
    (t : ExteriorAlgebra.koszulComplex A r f ⟶ ExteriorAlgebra.koszulComplex A r g)
    (ht : ∀ k, t.f k = ModuleCat.ofHom
      (exteriorPower.map k (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (d i)))))
    (q : ℤ) (I : exteriorKoszulIndex r q) :
    exteriorKoszulBasis r f q I ≫
        (HomologicalComplex.extendMap t ComplexShape.embeddingDownNat).f q =
      ModuleCat.ofHom (LinearMap.mul A A (∏ i ∈ I.1, d i)) ≫
        exteriorKoszulBasis r g q I := by
  classical
  let k := (-q).toNat
  have hk : -(k : ℤ) = q := by have := I.2; dsimp [k]; omega
  let B := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A))
  let S : Set.powersetCard (Fin r) k := ⟨I.1, by
    change I.1.card = k
    have := I.2
    dsimp [k]
    omega⟩
  have hw : exteriorPower.map k
      (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (d i)))
      (B.exteriorPower k S) = (∏ i ∈ I.1, d i) • B.exteriorPower k S := by
    simp only [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
    have hd : Finsupp.linearCombination A (fun i ↦ Finsupp.single i (d i)) ∘ B =
        fun i ↦ d i • B i := by
      funext i
      simp [B, Finsupp.smul_single]
    rw [hd]
    simp only [exteriorPower.ιMulti_family]
    rw [show (fun i ↦ d i • B i) ∘ Set.powersetCard.ofFinEmbEquiv.symm S =
      fun j ↦ d (Set.powersetCard.ofFinEmbEquiv.symm S j) •
        B (Set.powersetCard.ofFinEmbEquiv.symm S j) from rfl,
      AlternatingMap.map_smul_univ]
    congr 1
    apply Finset.prod_bij (fun j _ ↦ Set.powersetCard.ofFinEmbEquiv.symm S j)
    · intro j _
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).1 ⟨j, rfl⟩
    · intro i _ j _ h
      exact (Set.powersetCard.ofFinEmbEquiv.symm S).injective h
    · intro i hi
      obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S i).2 hi
      exact ⟨j, Finset.mem_univ _, hj⟩
    · intro j _
      rfl
  simp only [exteriorKoszulBasis]
  erw [HomologicalComplex.extendMap_f t ComplexShape.embeddingDownNat hk]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ht]
  apply (cancel_mono ((ExteriorAlgebra.koszulComplex A r g).extendXIso
    ComplexShape.embeddingDownNat hk).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change exteriorPower.map k
      (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (d i)))
      (x • B.exteriorPower k S) = ((∏ i ∈ I.1, d i) * x) • B.exteriorPower k S
  rw [map_smul, hw, smul_smul, mul_comm]

private def coefficientEnd
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (E : ModuleCat.{w} A ⥤ SheafOfModules.{w}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) [E.Additive]
    (c : SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O) ≅ E.obj (ModuleCat.of A A)) :
    A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) where
  toFun x := .of (c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) ≫ c.inv)
  map_one' := by
    apply End.ext
    have h : ModuleCat.ofHom (LinearMap.mul A A (1 : A)) = 𝟙 _ := by ext; simp
    change c.hom ≫ E.map _ ≫ c.inv = 𝟙 _
    rw [h, E.map_id, Category.id_comp, c.hom_inv_id]
  map_zero' := by
    apply End.ext
    have h : ModuleCat.ofHom (LinearMap.mul A A (0 : A)) = 0 := by ext; simp
    change c.hom ≫ E.map _ ≫ c.inv = 0
    rw [h, E.map_zero, zero_comp, comp_zero]
  map_add' x y := by
    apply End.ext
    have h : ModuleCat.ofHom (LinearMap.mul A A (x + y)) =
        ModuleCat.ofHom (LinearMap.mul A A x) +
          ModuleCat.ofHom (LinearMap.mul A A y) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact add_mul x y z
    change c.hom ≫ E.map _ ≫ c.inv = _
    rw [h, E.map_add, Preadditive.add_comp, Preadditive.comp_add, End.add_asHom]
  map_mul' x y := by
    apply End.ext
    have h : ModuleCat.ofHom (LinearMap.mul A A (x * y)) =
        ModuleCat.ofHom (LinearMap.mul A A y) ≫
          ModuleCat.ofHom (LinearMap.mul A A x) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact mul_assoc x y z
    change c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A (x * y))) ≫ c.inv =
      (c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A y)) ≫ c.inv) ≫
        (c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) ≫ c.inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [h, E.map_comp]
    simp only [Category.assoc]

private theorem exteriorKoszulBasis_zero {A : Type w} [CommRing A]
    (r : ℕ) (f : Fin r → A) :
    exteriorKoszulBasis r f 0 ⟨∅, rfl⟩ =
      ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
        ((ExteriorAlgebra.koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [exteriorKoszulBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.zeroEquiv_symm_apply]
  congr 3

/-- An additive functor preserving the regular module and scalar multiplications
identifies the finite exterior Koszul complex with the ordered positive tensor's dual.
No exactness, Noetherianity, quotients, augmentations or cones are involved.

Source: Stacks Project, more-algebra.tex, lemma-join-sequences-koszul-complex
(0664), and algebraization.tex, lemma-derived-completion-koszul (0A0E).
(auxiliary; not a blueprint node).

Proof: conjugate the image under E of scalar multiplication by the regular-module
isomorphism c. Functoriality and additivity make this a ring homomorphism from A
to the endomorphisms of O, and hs identifies its values on the generators with
the prescribed section scalars. In each integer degree the increasing exterior
wedge inclusions form a finite coproduct of copies of A; the positive-degree
case is the coproduct of an empty family into a zero object. E preserves these
finite coproducts, and precomposing their legs with c gives copies of O.
Take the normalized finite-subset basis of the actual dual tower from
exists_ringedKoszulDualBasis. Uniqueness of coproducts gives degreewise
isomorphisms matching these two bases. Test the chain square on each source
basis leg and use exteriorKoszulBasis_d and the dual differential matrix.
Additivity and the conjugated scalar identities identify the two finite sums.
For every n<=m, exteriorPower.map acts on the I wedge by the product of the
specified diagonal entries; the proof derives this directly from alternating
multilinearity. Comparing with the actual dual transition matrix proves the
whole naturality square, including n=m. Finally, the empty exterior basis
inclusion equals inverse zeroEquiv followed by the extension coordinate.
The normalization of the dual empty basis therefore gives the exact displayed
unit equation. Every construction works for r=0, the zero ring, and empty sites,
and no scalar or factorial is inverted. -/
theorem exteriorKoszul_scalar_realization
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (E : ModuleCat.{w} A ⥤ SheafOfModules.{w}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) [E.Additive]
    (c : SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O) ≅ E.obj (ModuleCat.of A A))
    (s : A → (O.obj ⋙ forget CommRingCat).sections)
    (hs : ∀ x : A, c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
      (ringedKoszulScalar O (s x)).asHom ≫ c.hom)
    (r : ℕ) (a : Fin r → A)
    (t : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (ht : ∀ n m h k, (t n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n)))))) :
    let H := E.mapHomologicalComplex (.up ℤ)
    ∃ e : ∀ n : ℕ, H.obj
        ((ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extend
          ComplexShape.embeddingDownNat) ≅ (ringedKoszulDualTower O r (fun i ↦ s (a i))).obj
            (op n),
      (∀ n m h, H.map (HomologicalComplex.extendMap (t n m h)
          ComplexShape.embeddingDownNat) ≫ (e n).hom =
        (e m).hom ≫ (ringedKoszulDualTower O r (fun i ↦ s (a i))).map (homOfLE h).op) ∧
      ∀ n, c.hom ≫ E.map
          (ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
            ((ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫ (e n).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r (fun i ↦ s (a i)) n).f 0 := by
  classical
  let H := E.mapHomologicalComplex (.up ℤ)
  let K (n : ℕ) := exteriorKoszulExtended r (fun i ↦ a i ^ (n + 1))
  let D := ringedKoszulDualTower O r (fun i ↦ s (a i))
  let ρ := coefficientEnd O E c
  have hscalar (x : A) : c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
      (ρ x).asHom ≫ c.hom := by
    change c.hom ≫ E.map _ = (c.hom ≫ E.map _ ≫ c.inv) ≫ c.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hρ (i : Fin r) : ρ (a i) = ringedKoszulScalar O (s (a i)) := by
    apply End.ext
    apply (cancel_mono c.hom).1
    rw [← hscalar, hs]
  obtain ⟨b, hb, hd, htower, hu⟩ := exists_ringedKoszulDualBasis O ρ r a
    (fun i ↦ s (a i)) hρ
  have hc (n : ℕ) (q : ℤ) :
      IsColimit (Cofan.mk (E.obj ((K n).X q))
        (fun I : exteriorKoszulIndex r q ↦ c.hom ≫ E.map
          (exteriorKoszulBasis r (fun i ↦ a i ^ (n + 1)) q I))) := by
    let B := exteriorKoszulBasis r (fun i ↦ a i ^ (n + 1)) q
    let h := isColimitCofanMkObjOfIsColimit E
      (fun _ : exteriorKoszulIndex r q ↦ ModuleCat.of A A)
      B
      (Classical.choice (isColimit_exteriorKoszulBasis r (fun i ↦ a i ^ (n + 1)) q))
    refine Cofan.IsColimit.mk _
      (fun z ↦ h.desc (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I))) ?_ ?_
    · intro z I
      have hf : E.map (B I) ≫ h.desc (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I)) =
          c.inv ≫ z.inj I :=
        h.fac (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I)) (Discrete.mk I)
      change (c.hom ≫ E.map (B I)) ≫
        h.desc (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I)) = _
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun f ↦ c.hom ≫ f) hf
    · intro z f hf
      apply h.hom_ext
      rintro ⟨I⟩
      change E.map (B I) ≫ f =
        E.map (B I) ≫ h.desc (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I))
      apply (cancel_epi c.hom).1
      have hi := hf I
      change (c.hom ≫ E.map (B I)) ≫ f = z.inj I at hi
      have hd : E.map (B I) ≫ h.desc (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I)) =
          c.inv ≫ z.inj I :=
        h.fac (Cofan.mk z.pt (fun I ↦ c.inv ≫ z.inj I)) (Discrete.mk I)
      rw [hd]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hi
  let v (n : ℕ) (q : ℤ) : E.obj ((K n).X q) ≅ (D.obj (op n)).X q :=
    (hc n q).coconePointUniqueUpToIso (Classical.choice (hb n q))
  have hv (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
      c.hom ≫ E.map (exteriorKoszulBasis r (fun i ↦ a i ^ (n + 1)) q I) ≫
        (v n q).hom = b n q I := by
    exact (hc n q).comp_coconePointUniqueUpToIso_hom
      (Classical.choice (hb n q)) (Discrete.mk I)
  have hcomm (n : ℕ) (q : ℤ) :
      E.map ((K n).d q (q + 1)) ≫ (v n (q + 1)).hom =
        (v n q).hom ≫ (D.obj (op n)).d q (q + 1) := by
    apply (hc n q).hom_ext
    rintro ⟨I⟩
    change (c.hom ≫ E.map _) ≫ (E.map _ ≫ _) =
      (c.hom ≫ E.map _) ≫ (_ ≫ _)
    simp only [Category.assoc]
    rw [← E.map_comp_assoc, exteriorKoszulBasis_d, E.map_sum]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum]
    rw [reassoc_of% (hv n q I), hd]
    apply Finset.sum_congr rfl
    intro L _
    rw [E.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (hscalar
      (exteriorKoszulCoefficient r (fun i ↦ a i ^ (n + 1)) q I L)), hv]
  let e (n : ℕ) : H.obj (K n) ≅ D.obj (op n) :=
    HomologicalComplex.Hom.isoOfComponents (v n) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      exact (hcomm n i).symm)
  refine ⟨e, ?_, ?_⟩
  · intro n m h
    apply HomologicalComplex.hom_ext
    intro q
    apply (hc m q).hom_ext
    rintro ⟨I⟩
    change (c.hom ≫ E.map _) ≫ (E.map _ ≫ (v n q).hom) =
      (c.hom ≫ E.map _) ≫ ((v m q).hom ≫ _)
    simp only [Category.assoc]
    rw [← E.map_comp_assoc, exteriorKoszulBasis_diagonal r _ _
      (fun i ↦ a i ^ (m - n)) (t n m h) (ht n m h), E.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (hscalar (∏ i ∈ I.1, a i ^ (m - n))), hv,
      reassoc_of% (hv m q I), htower]
  · intro n
    change c.hom ≫ E.map _ ≫ (v n 0).hom = _
    rw [← exteriorKoszulBasis_zero]
    rw [hv, hu]

end CategoryTheory
