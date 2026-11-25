/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints

/-!
# Derivation coefficients on the dual-number diagonal

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, the square-zero
pushout calculation; blueprint `def-wf-lie-algebra-derivation`, the dual-number description.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.GrpObj

-- The construction follows the private helpers in Sheaf.AlgebraicGeometry.DualNumbersDiagonal.
-- Keeping these helpers private avoids changing the interface of that module.
private def diagonalRingHom {R : Type u} [CommRing R] :
    DualNumber (DualNumber R) →+* DualNumber R where
  toFun x := x.fst + TrivSqZeroExt.inr x.snd.fst
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [mul_add, add_mul]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [add_assoc, add_left_comm, add_comm]

private noncomputable def diagonalNatTrans : CommRingCat.dualNumber ⋙ CommRingCat.dualNumber ⟶
    CommRingCat.dualNumber where
  app R := CommRingCat.ofHom diagonalRingHom
  naturality R T f := by
    ext x : 2
    change diagonalRingHom (DualNumber.mapRingHom (DualNumber.mapRingHom f.hom) x) =
      DualNumber.mapRingHom f.hom (diagonalRingHom x)
    apply TrivSqZeroExt.ext
    · simp only [diagonalRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero,
        DualNumber.fst_mapRingHom]
    · simp only [diagonalRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, DualNumber.snd_mapRingHom,
        DualNumber.fst_mapRingHom]
      exact (map_add f.hom _ _).symm

private noncomputable def diagonalMap (S : Scheme.{u}) :
    S.dualNumbers ⟶ S.dualNumbers.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft S.presheaf diagonalNatTrans ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := S.dualNumbers.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    have h := (S.presheaf.isUnit_germ_dualNumber_iff x U hxU
      (diagonalRingHom g)).mp hs
    apply (S.dualNumbers.presheaf.isUnit_germ_dualNumber_iff x U hxU g).mpr
    apply (S.presheaf.isUnit_germ_dualNumber_iff x U hxU g.fst).mpr
    simpa [diagonalRingHom] using h

private theorem diagonal_coefficient_heq (S Y : Scheme.{u})
    (F : S.dualNumbers.dualNumbers ⟶ Y) (V : TopologicalSpace.Opens Y)
    (a : Γ(Y, V)) :
    HEq ((diagonalMap S ≫ F).app V a).snd
      ((F.app V a).fst.snd + (F.app V a).snd.fst) := by
  simp only [Scheme.Hom.comp_app]
  change HEq (diagonalRingHom (F.app V a)).snd
    ((F.app V a).fst.snd + (F.app V a).snd.fst)
  simp [diagonalRingHom]

private theorem first_coefficient_heq (S Y : Scheme.{u})
    (F : S.dualNumbers.dualNumbers ⟶ Y) (V : TopologicalSpace.Opens Y)
    (a : Γ(Y, V)) :
    HEq ((S.dualNumbers.dualNumbersι ≫ F).app V a).snd (F.app V a).fst.snd := by
  simp only [Scheme.Hom.comp_app]
  rfl

private theorem second_coefficient_heq (S Y : Scheme.{u})
    (F : S.dualNumbers.dualNumbers ⟶ Y) (V : TopologicalSpace.Opens Y)
    (a : Γ(Y, V)) :
    HEq ((S.dualNumbersι.dualNumbers ≫ F).app V a).snd (F.app V a).snd.fst := by
  simp only [Scheme.Hom.comp_app]
  let R := Γ(S, F ⁻¹ᵁ V)
  change HEq
    (DualNumber.mapRingHom (TrivSqZeroExt.fstHom R R R).toRingHom (F.app V a)).snd
    (F.app V a).snd.fst
  simp

private theorem section_add_heq (S : Scheme.{u}) {U W : TopologicalSpace.Opens S}
    (h : U = W) {x y : Γ(S, U)} {x' y' : Γ(S, W)}
    (hx : HEq x x') (hy : HEq y y') : HEq (x + y) (x' + y') := by
  subst W
  cases hx
  cases hy
  rfl

private theorem coefficient_congr {S Y : Scheme.{u}} {v w : S.dualNumbers ⟶ Y}
    (h : v = w) (V : TopologicalSpace.Opens Y) (a : Γ(Y, V)) :
    HEq (v.app V a).snd (w.app V a).snd := by
  cases h
  rfl

private theorem transported_d_heq {S : Scheme.{u}} (X : Over S)
    (v : Scheme.dualNumbersOver S ⟶ X) (g : S ⟶ X.left)
    (h : S.dualNumbersι ≫ v.left = g)
    {V : (TopologicalSpace.Opens X.left)ᵒᵖ} (a : Γ(X.left, V.unop)) :
    HEq ((h ▸ infDerivation X v).d a) (v.left.app V.unop a).snd := by
  cases h
  rfl


/-- On the dual-number diagonal the first-order coefficient is the sum of the
first-order coefficients on the two axes, after identifying the common reduction.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, applied sectionwise.
(blueprint: lem-ag-dual-numbers-diagonal-coefficients)

Proof: Compose with the comparison from the iterated thickening S[epsilon][delta]
to the product. On sections the axis restrictions take a double dual number to
its first dual-number component, and apply the constant projection to both of
its components, respectively. The diagonal sends epsilon and delta to epsilon.
It kills their product, since epsilon squared is zero. Write a double dual
number as its constant, epsilon, delta, and epsilon-delta terms: the coefficient
of epsilon on the diagonal is the sum of its epsilon and delta coefficients.
The comparison composed with the diagonal is the categorical diagonal, because
both its projections are identities. Its restrictions to the two axes are the
categorical axes, by the corresponding projection identities. Apply the
coefficient calculation to the section map of f on each target open.
The three equations of reductions identify all inverse-image opens and the
pushforward module structures with those of g. Equality transport therefore
turns the coefficient identity into exactly the displayed derivation identity.
No finiteness or smoothness assumption is needed; the calculation holds for the
zero ring as well. -/
theorem infDerivation_diagonal_coefficients {S : Scheme.{u}} (X : Over S)
    (f : Scheme.dualNumbersOver S ⊗ Scheme.dualNumbersOver S ⟶ X)
    (g : S ⟶ X.left)
    (hd : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g)
    (h₁ : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S))
        (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) ≫ f).left = g)
    (h₂ : S.dualNumbersι ≫
      (lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
        (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g) :
    let D₀ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      hd ▸ infDerivation X (lift (𝟙 _) (𝟙 _) ≫ f)
    let D₁ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      h₁ ▸ infDerivation X (lift (𝟙 _) (toUnit _ ≫ Scheme.dualNumbersιOver S) ≫ f)
    let D₂ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      X.hom.pullbackPresheafHom :=
      h₂ ▸ infDerivation X (lift (toUnit _ ≫ Scheme.dualNumbersιOver S) (𝟙 _) ≫ f)
    ∀ {V : (TopologicalSpace.Opens X.left)ᵒᵖ} (a : Γ(X.left, V.unop)),
      D₀.d a = D₁.d a + D₂.d a := by
  let k := lift (Scheme.dualNumbersProjεOver S) (Scheme.dualNumbersProjδOver S)
  have he₁ : Scheme.dualNumbersιεOver S ≫ k =
      lift (𝟙 (Scheme.dualNumbersOver S))
        (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjεOver]
    · apply Over.OverMorphism.ext
      simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjδOver, Over.toUnit_left]
  have he₂ : Scheme.dualNumbersιδOver S ≫ k =
      lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
        (𝟙 (Scheme.dualNumbersOver S)) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      simp [Scheme.dualNumbersιδOver, Scheme.dualNumbersProjεOver, Over.toUnit_left]
    · apply Over.OverMorphism.ext
      simp [Scheme.dualNumbersιδOver, Scheme.dualNumbersProjδOver, ← Scheme.Hom.dualNumbers_comp,
        Scheme.Hom.dualNumbers_id]
  have diagonalMap_proj₁ :
      diagonalMap S ≫ S.dualNumbers.dualNumbersProj = 𝟙 _ := by
    refine Scheme.Hom.ext rfl fun U ↦ ?_
    simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
    erw [eqToHom_refl, Category.comp_id]
    ext a : 2
    change diagonalRingHom (TrivSqZeroExt.inl a) = a
    ext <;> simp [diagonalRingHom]
  have diagonalMap_proj₂ :
      diagonalMap S ≫ S.dualNumbersProj.dualNumbers = 𝟙 _ := by
    refine Scheme.Hom.ext rfl fun U ↦ ?_
    simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
    erw [eqToHom_refl, Category.comp_id]
    ext a : 2
    change diagonalRingHom (DualNumber.mapRingHom (TrivSqZeroExt.inlHom _ _) a) = a
    ext <;> simp [diagonalRingHom]
  let d : Scheme.dualNumbersOver S ⟶ Scheme.dualNumbers₂Over S := Over.homMk (diagonalMap S) (by
    change diagonalMap S ≫ (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj) =
      S.dualNumbersProj
    rw [← Category.assoc, diagonalMap_proj₁, Category.id_comp])
  have hdiag : d ≫ k = lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [k, Category.assoc, lift_fst, lift_snd]
    · apply Over.OverMorphism.ext
      exact diagonalMap_proj₁
    · apply Over.OverMorphism.ext
      exact diagonalMap_proj₂
  let F := k.left ≫ f.left
  have e₀ : (lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left =
      diagonalMap S ≫ F := by
    rw [← hdiag]
    change (diagonalMap S ≫ k.left) ≫ f.left = diagonalMap S ≫ (k.left ≫ f.left)
    exact Category.assoc _ _ _
  have e₁ : (lift (𝟙 (Scheme.dualNumbersOver S))
      (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) ≫ f).left =
      S.dualNumbers.dualNumbersι ≫ F := by
    rw [← he₁]
    change (S.dualNumbers.dualNumbersι ≫ k.left) ≫ f.left =
      S.dualNumbers.dualNumbersι ≫ (k.left ≫ f.left)
    exact Category.assoc _ _ _
  have e₂ : (lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
      (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = S.dualNumbersι.dualNumbers ≫ F := by
    rw [← he₂]
    change (S.dualNumbersι.dualNumbers ≫ k.left) ≫ f.left =
      S.dualNumbersι.dualNumbers ≫ (k.left ≫ f.left)
    exact Category.assoc _ _ _
  dsimp only
  intro V a
  have c₀ := (transported_d_heq X _ g hd a).trans
    ((coefficient_congr e₀ V.unop a).trans
      (diagonal_coefficient_heq S X.left F V.unop a))
  have c₁ := (transported_d_heq X _ g h₁ a).trans
    ((coefficient_congr e₁ V.unop a).trans
      (first_coefficient_heq S X.left F V.unop a))
  have c₂ := (transported_d_heq X _ g h₂ a).trans
    ((coefficient_congr e₂ V.unop a).trans
      (second_coefficient_heq S X.left F V.unop a))
  have hb := congrArg (fun m : S ⟶ X.left ↦ m.base) hd
  rw [e₀] at hb
  change (𝟙 S.carrier ≫ (𝟙 S.carrier ≫ F.base)) = g.base at hb
  simp only [Category.id_comp] at hb
  have hopen : g ⁻¹ᵁ V.unop = F ⁻¹ᵁ V.unop := by
    change (TopologicalSpace.Opens.map g.base).obj V.unop =
      (TopologicalSpace.Opens.map F.base).obj V.unop
    rw [hb]
  exact eq_of_heq (c₀.trans (section_add_heq S hopen c₁ c₂).symm)

end AlgebraicGeometry.GrpObj
