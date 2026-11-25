/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulTransitions
import WeilConjectures.CategoryTheory.RingedNegativeKoszulFactorHomTensor

/-! # Duality between positive and negative two-term Koszul tensors

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the identification of finite free dual complexes.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

attribute [local instance] SheafOfModules.monoidalCategory

private theorem tensor_inclusion_map (O : Sheaf J CommRingCat.{u})
    (F K L : ringedSiteComplex O) (f : K ⟶ L)
    (x : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶ F.X 0)
    (y : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶ K.X 0) :
    (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      MonoidalCategory.tensorHom x y ≫
      CochainComplex.ιMapBifunctor F K (MonoidalCategory.curriedTensor _) 0 0 0 (by omega) ≫
      (((ringedKoszulTensor O).obj F).map f).f 0 =
    (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      MonoidalCategory.tensorHom x (y ≫ f.f 0) ≫
      CochainComplex.ιMapBifunctor F L (MonoidalCategory.curriedTensor _) 0 0 0 (by omega) := by
  change _ ≫ _ ≫ _ ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 F) f
      (MonoidalCategory.curriedTensor _) (.up ℤ)).f 0 = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp]
  simp only [MonoidalCategory.curriedTensor_obj_map,
    MonoidalCategory.tensorHom_comp_whiskerLeft_assoc]

attribute [local irreducible] homComplexFunctor

private theorem duality (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ∀ m : ℕ, ringedNegativeKoszul O r b m ≅
        (ringedKoszulDualTower O r b).obj (op m),
      (∀ m, ringedNegativeKoszulTransition O r b m ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O r b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, ringedNegativeKoszulBasis O r b m ∅ 0 ≫ (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r b m).f 0) := by
  induction r with
  | zero => exact ringedNegativeKoszulZeroDuality O b
  | succ r ih =>
    obtain ⟨e, he, hu⟩ := ih (fun i ↦ b i.succ)
    obtain ⟨a, ha, hs, hv⟩ := ringedNegativeKoszulFactorHomTensor O (b 0)
    let T := ringedKoszulTensor O
    let U := ringedSiteRingComplex O
    let H := (homComplexFunctor (R := O)).flip.obj U
    let P := ringedKoszulDiagram O r (fun i ↦ b i.succ)
    let N := ringedNegativeKoszul O r (fun i ↦ b i.succ)
    change (∀ m : ℕ, N m ≅ H.obj (op (P.obj m))) at e
    change (∀ (m : ℕ) (K : ringedSiteComplex O),
      (T.obj (ringedNegativeKoszulFactor O (b 0) m)).obj (H.obj (op K)) ≅
        H.obj (op ((T.obj (ringedKoszulFactor O (b 0) m)).obj K))) at a
    let E (m : ℕ) :=
      ((T.obj (ringedNegativeKoszulFactor O (b 0) m)).mapIso (e m)) ≪≫ a m (P.obj m)
    refine ⟨E, ?_, ?_⟩
    · intro m
      let f := ringedNegativeKoszulTransition O r (fun i ↦ b i.succ) m
      let g := P.map (homOfLE (Nat.le_succ m))
      let d := ringedNegativeKoszulFactorTransition O (b 0) m
      let c := ringedKoszulFactorStep O (b 0) m
      have htail : f ≫ (e m).hom = (e (m + 1)).hom ≫ H.map g.op := he m
      have hnat : (T.obj (ringedNegativeKoszulFactor O (b 0) m)).map
            (H.map g.op) ≫ (a m (P.obj m)).hom =
          (a m (P.obj (m + 1))).hom ≫
            H.map ((T.obj (ringedKoszulFactor O (b 0) m)).map g).op :=
        ha m (P.obj (m + 1)) (P.obj m) g
      have hfactor : (T.map d).app (H.obj (op (P.obj (m + 1)))) ≫
            (a m (P.obj (m + 1))).hom =
          (a (m + 1) (P.obj (m + 1))).hom ≫
            H.map ((T.map c).app (P.obj (m + 1))).op := hs m (P.obj (m + 1))
      have hp : (T.obj (ringedKoszulFactor O (b 0) m)).map g ≫
            (T.map c).app (P.obj (m + 1)) =
          (ringedKoszulDiagram O (r + 1) b).map (homOfLE (Nat.le_succ m)) := by
        change _ = ((T.map ((ringedKoszulFactors O (b 0)).map
            (homOfLE (Nat.le_succ m)))).app (P.obj m) ≫
          (T.obj (ringedKoszulFactor O (b 0) (m + 1))).map g)
        rw [show (ringedKoszulFactors O (b 0)).map (homOfLE (Nat.le_succ m)) = c from
          Functor.ofSequence_map_homOfLE_succ _ m]
        exact (T.map c).naturality g
      change ((T.map d).app (N (m + 1)) ≫
          (T.obj (ringedNegativeKoszulFactor O (b 0) m)).map f) ≫
            ((T.obj (ringedNegativeKoszulFactor O (b 0) m)).map (e m).hom ≫
              (a m (P.obj m)).hom) =
        ((T.obj (ringedNegativeKoszulFactor O (b 0) (m + 1))).map (e (m + 1)).hom ≫
          (a (m + 1) (P.obj (m + 1))).hom) ≫
            H.map ((ringedKoszulDiagram O (r + 1) b).map
              (homOfLE (Nat.le_succ m))).op
      rw [Category.assoc, ← Functor.map_comp_assoc, htail, Functor.map_comp_assoc]
      rw [← NatTrans.naturality_assoc, hnat, reassoc_of% hfactor]
      simp only [Category.assoc]
      rw [← Functor.map_comp, ← op_comp, hp]
    · intro m
      have hb : ringedNegativeKoszulBasis O (r + 1) b m ∅ 0 =
          (MonoidalCategory.leftUnitor
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
            MonoidalCategory.tensorHom (ringedNegativeKoszulFactorBasis O (b 0) m 0)
              (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m ∅ 0) ≫
            CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O (b 0) m)
              (N m) (MonoidalCategory.curriedTensor _) 0 0 0 (by omega) := by
        let q (i : ℤ) :
            SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
              (ringedNegativeKoszul O (r + 1) b m).X 0 :=
          (MonoidalCategory.leftUnitor
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
            MonoidalCategory.tensorHom (ringedNegativeKoszulFactorBasis O (b 0) m i)
              (ringedNegativeKoszulBasis O r (fun j ↦ b j.succ) m ∅ (0 - i)) ≫
            CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O (b 0) m)
              (N m) (MonoidalCategory.curriedTensor _) i (0 - i) 0 (by omega)
        simp only [ringedNegativeKoszulBasis, Finset.preimage_empty]
        change q (if (0 : Fin (r + 1)) ∈ (∅ : Finset _) then -1 else 0) = q 0
        exact congrArg q (ite_eq_right (Finset.notMem_empty (0 : Fin (r + 1))))
      change _ ≫ (((T.obj (ringedNegativeKoszulFactor O (b 0) m)).map (e m).hom).f 0 ≫
        (a m (P.obj m)).hom.f 0) = _
      rw [hb, ← Category.assoc]
      rw [show (_ ≫ _ ≫ _) ≫
          ((T.obj (ringedNegativeKoszulFactor O (b 0) m)).map (e m).hom).f 0 = _ by
        simpa only [Category.assoc] using
          tensor_inclusion_map O _ _ _ (e m).hom
            (ringedNegativeKoszulFactorBasis O (b 0) m 0)
            (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m ∅ 0)]
      have hu' := hu m
      dsimp only [ringedKoszulDualUnit, HomologicalComplex.comp_f] at hu'
      rw [hu']
      have hproj : ringedKoszulProjection O (r + 1) b m =
          (T.map (ringedKoszulFactorProjection O (b 0) m)).app (P.obj m) ≫
            (T.obj U).map (ringedKoszulProjection O r (fun i ↦ b i.succ) m) ≫
            (ringedKoszulUnitTensorIso O).hom := by
        rfl
      rw [ringedKoszulDualUnit, hproj]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      exact hv m (P.obj m) (ringedKoszulProjection O r (fun i ↦ b i.succ) m)

/-- For a nonempty list, the ordered negative two-term tensors are the internal duals
of the positive
ones, compatibly with their explicit transitions and empty-subset units.
This assertion is entirely on one ringed site: it has no exterior algebra,
coefficient ring, scheme, sheafification or scalar transport.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the displayed finite free dual identification.
(auxiliary; not a blueprint node).

Proof: the positive factor is O --b^(m+1)--> O in degrees 0 and 1. In its
internal Hom into O[0], project the degree n product to p=-n: every other
factor has zero target. Evaluation at 1 identifies the two surviving internal
Hom sheaves with O. The degree -1 differential has coefficient -(-1)^(-1)=1,
so it is multiplication by b^(m+1). Precomposition with the positive step
(1,b) gives (b,1) on the negative factor. On finite tensors, evaluate a tensor
of functionals on a tensor of vectors with the sign from moving each
functional past the earlier vectors. On a basis indexed by subsets this sign
is (-1) to the number of pairs of selected indices. It compensates for the
Hom differential sign, so this is a chain map. The dual-basis map is its
inverse: in each degree the finite sum and product are identified by the
finite basis. Induct on the ordered factors to obtain the isomorphism.
Evaluation is natural in both factors; apply it to (1,b) in every positive
factor to get precisely ringedNegativeKoszulTransition. At the empty subset
there is no interchange sign. Its tensor of sections 1 is the functional
given by the positive projection to O[0], normalized by evaluation at 1;
this is exactly ringedKoszulDualUnit with the displayed single-complex
identification. The empty tensor is handled separately by ringedNegativeKoszulZeroDuality.
No scalar is inverted and all finite free identities hold over the zero ring
and on the empty site. -/
theorem ringedNegativeKoszulSuccDuality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ∀ m : ℕ, ringedNegativeKoszul O (r + 1) b m ≅
        (ringedKoszulDualTower O (r + 1) b).obj (op m),
      (∀ m, ringedNegativeKoszulTransition O (r + 1) b m ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O (r + 1) b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, ringedNegativeKoszulBasis O (r + 1) b m ∅ 0 ≫ (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O (r + 1) b m).f 0) := by
  exact duality O (r + 1) b

end CategoryTheory
