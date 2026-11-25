/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechCapPresheafLocalIso

/-! # The degree-zero insertion identity before sheafification

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

private noncomputable def capIntoCap {X : Scheme.{u}} (G : X.Modules)
    (W Z Y : X.Opens) (h : W ⊓ Z ≤ Y) :
    cechCapModule G Y ⟶ (cechCapPresheafFunctor W).obj (cechCapModule G Z) where
  app V := ModuleCat.ofHom
    (X := (cechCapModule G Y).obj V)
    (Y := ((cechCapPresheafFunctor W).obj (cechCapModule G Z)).obj V)
    { toFun := fun s ↦ G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
      map_add' := by intros; simp
      map_smul' := by
        intro a s
        change G.val.map
            (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
              rw [inf_assoc]; exact inf_le_inf_left _ h)).op
            ((X.ringCatSheaf.obj.map
              (homOfLE (inf_le_left : V.unop ⊓ Y ≤ V.unop)).op a) •
                (show G.val.obj (op (V.unop ⊓ Y)) from s)) =
          (X.ringCatSheaf.obj.map
            (homOfLE (inf_le_left : (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ W)).op
              (X.ringCatSheaf.obj.map
                (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a)) •
            G.val.map
              (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
                rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
        rw [PresheafOfModules.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← RingCat.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl }
  naturality := by
    intro V T f
    ext s
    change G.val.map
        (homOfLE (show (T.unop ⊓ W) ⊓ Z ≤ T.unop ⊓ Y by
          rw [inf_assoc]; exact inf_le_inf_left _ h)).op
        (G.val.map (homOfLE (inf_le_inf_right Y (leOfHom f.unop))).op s) =
      G.val.map
        (homOfLE (inf_le_inf_right Z (inf_le_inf_right W (leOfHom f.unop)))).op
          (G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
            rw [inf_assoc]; exact inf_le_inf_left _ h)).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl

private theorem capIntoCap_comp {X : Scheme.{u}} (G : X.Modules)
    (W Z Y A : X.Opens) (h : W ⊓ Z ≤ Y) (h' : Y ≤ A) :
    cechCapModuleMap G h' ≫ capIntoCap G W Z Y h =
      capIntoCap G W Z A (h.trans h') := by
  ext V s
  change G.val.map
      (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op
      (G.val.map (homOfLE (inf_le_inf_left V.unop h')).op s) =
    G.val.map
      (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ A by
        rw [inf_assoc]; exact inf_le_inf_left _ (h.trans h'))).op s
  rw [← PresheafOfModules.map_comp_apply]
  rfl

private theorem capIntoCap_unit {X : Scheme.{u}} (G : X.Modules) (W Z : X.Opens) :
    capIntoCap G W Z Z inf_le_right =
      (cechCapPresheafUnit W).app (cechCapModule G Z) := by
  ext V s
  rfl

private theorem capIntoCap_map_unit {X : Scheme.{u}} (G : X.Modules) (W Z : X.Opens) :
    capIntoCap G W Z W inf_le_left =
      (cechCapPresheafFunctor W).map (cechCapModuleUnit G Z) := by
  ext V s
  rfl

private def singletonTuple {r : ℕ} (i : Fin r) : Fin 1 ↪o Fin r :=
  OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    exact False.elim ((not_lt_of_ge (by exact le_of_eq (Subsingleton.elim b a))) hab))

private def pairTuple {r : ℕ} (i j : Fin r) (h : i < j) : Fin 2 ↪o Fin r :=
  OrderEmbedding.ofStrictMono (Fin.cases i (fun _ ↦ j)) (by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim (lt_irrefl _ hab)
    · exact h
    · simp at hab
    · exact False.elim (lt_irrefl _ hab))

private theorem singletonIntersection {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (t : Fin 1 ↪o Fin r) :
    alternatingCechIntersection U t = U (t 0) := by
  simp [alternatingCechIntersection]

private theorem pairIntersection {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (i j : Fin r) (h : i < j) :
    alternatingCechIntersection U (pairTuple i j h) = U i ⊓ U j := by
  apply le_antisymm
  · exact le_inf (iInf_le _ (0 : Fin 2)) (iInf_le _ (1 : Fin 2))
  · apply le_iInf
    intro k
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

/-- Degree-zero insertion expresses restriction as an augmentation plus a boundary term.
Source: Stacks Project, Tag 02FU, insertion cancellation in degree zero;
Tag 01FM for the increasing-tuple convention.
(blueprint: lem-pc-s3-alternating-cech-presheaf-degree-zero-identity).

Proof: Put K(P)(V)=P(V intersect U i), with scalars restricted from V. Define p
by projection onto the singleton i, whose intersection is U i. For each singleton
j, define the j coordinate of h by the pair {i,j}: when i<j take its coordinate
with positive sign, when j<i with negative sign, and when i=j take zero. Its
sections live on V intersect U i intersect U j, precisely the j coordinate of
K(P0)(V). The canonical intersection equalities identify these modules; all maps
are O(V)-linear and natural in V. The j coordinate of d followed by h is the
restriction of the j section minus the restriction of the i section. The latter
is the j coordinate of p followed by K(augmentation). Their sum is restriction
to U i. For j=i the first term is zero and the second is restriction itself.
Equality in the finite product proves the stated identity. No sheafification or
integer extension occurs here. For r=0 there is no i; for r=1 the differential
term is zero; empty intersections give the same identity in zero modules. -/
theorem alternatingCechSheafPresheaf_degreeZero_identity
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let K := cechCapPresheafFunctor (U i)
    let P₀ := alternatingCechSheafPresheafTerms U G 0
    let P₁ := alternatingCechSheafPresheafTerms U G 1
    ∃ p : P₀ ⟶ K.obj G.val, ∃ h : P₁ ⟶ K.obj P₀,
      (cechCapPresheafUnit (U i)).app P₀ =
        alternatingCechSheafPresheafD U G 0 ≫ h +
          p ≫ K.map (alternatingCechSheafPresheafZero U G) := by
  classical
  dsimp only
  let K := cechCapPresheafFunctor (U i)
  let Q := fun t : Fin 1 ↪o Fin r ↦ cechCapModule G (alternatingCechIntersection U t)
  let P₀ := alternatingCechSheafPresheafTerms U G 0
  let P₁ := alternatingCechSheafPresheafTerms U G 1
  have : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  let p : P₀ ⟶ K.obj G.val := Pi.π Q (singletonTuple i) ≫
    cechCapModuleMap G (by simp [alternatingCechIntersection, singletonTuple])
  let hj (t : Fin 1 ↪o Fin r) : P₁ ⟶ K.obj (Q t) :=
    if h : i < t 0 then
      Pi.π _ (pairTuple i (t 0) h) ≫
        capIntoCap G (U i) (alternatingCechIntersection U t)
          (alternatingCechIntersection U (pairTuple i (t 0) h))
          (by rw [singletonIntersection, pairIntersection])
    else if h' : t 0 < i then
      -(Pi.π _ (pairTuple (t 0) i h') ≫
        capIntoCap G (U i) (alternatingCechIntersection U t)
          (alternatingCechIntersection U (pairTuple (t 0) i h'))
          (by rw [singletonIntersection, pairIntersection, inf_comm]))
    else 0
  let h : P₁ ⟶ K.obj P₀ := Pi.lift hj ≫ inv (piComparison K Q)
  refine ⟨p, h, ?_⟩
  apply (cancel_mono (piComparison K Q)).mp
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, piComparison_comp_π, Preadditive.add_comp]
  have hh : h ≫ K.map (Pi.π Q t) = hj t := by
    dsimp only [h]
    rw [Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]
  rw [hh]
  clear hh
  have hn := (cechCapPresheafUnit (U i)).naturality (Pi.π Q t)
  change Pi.π Q t ≫ (cechCapPresheafUnit (U i)).app (Q t) =
    (cechCapPresheafUnit (U i)).app P₀ ≫ K.map (Pi.π Q t) at hn
  rw [← hn]
  have haug : p ≫ K.map (alternatingCechSheafPresheafZero U G) ≫ K.map (Pi.π Q t) =
      Pi.π Q (singletonTuple i) ≫
        capIntoCap G (U i) (alternatingCechIntersection U t)
          (alternatingCechIntersection U (singletonTuple i))
          (by simp [alternatingCechIntersection, singletonTuple]) := by
    rw [← K.map_comp, alternatingCechSheafPresheafZero, Pi.lift_comp_π]
    dsimp only [p]
    rw [Category.assoc, ← capIntoCap_map_unit, capIntoCap_comp]
  rw [haug]
  have transport (a b : Fin 1 ↪o Fin r)
      (ha : U i ⊓ alternatingCechIntersection U t ≤ alternatingCechIntersection U a)
      (hb : U i ⊓ alternatingCechIntersection U t ≤ alternatingCechIntersection U b)
      (hab : a = b) :
      Pi.π Q a ≫ capIntoCap G (U i) (alternatingCechIntersection U t)
        (alternatingCechIntersection U a) ha =
      Pi.π Q b ≫ capIntoCap G (U i) (alternatingCechIntersection U t)
        (alternatingCechIntersection U b) hb := by
    subst b
    rfl
  by_cases hij : i < t 0
  · rw [show hj t = Pi.π _ (pairTuple i (t 0) hij) ≫
        capIntoCap G (U i) (alternatingCechIntersection U t)
          (alternatingCechIntersection U (pairTuple i (t 0) hij))
          (by rw [singletonIntersection, pairIntersection]) from dite_eq_left hij]
    simp only [alternatingCechSheafPresheafD, Pi.lift_comp_π_assoc, Category.assoc,
      Preadditive.sum_comp, Preadditive.zsmul_comp]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
    simp only [capIntoCap_comp]
    have h0 : (Fin.succAboveOrderEmb (0 : Fin 2)).trans (pairTuple i (t 0) hij) = t := by
      ext k
      fin_cases k
      rfl
    have h1 : (Fin.succAboveOrderEmb (1 : Fin 2)).trans (pairTuple i (t 0) hij) =
        singletonTuple i := by
      ext k
      fin_cases k
      rfl
    rw [transport _ _ _ inf_le_right h0, capIntoCap_unit]
    rw [transport _ _ _ (by simp [alternatingCechIntersection, singletonTuple]) h1]
    abel
  · by_cases hji : t 0 < i
    · have hhj : hj t = -(Pi.π _ (pairTuple (t 0) i hji) ≫
          capIntoCap G (U i) (alternatingCechIntersection U t)
            (alternatingCechIntersection U (pairTuple (t 0) i hji))
            (by rw [singletonIntersection, pairIntersection, inf_comm])) := by
        dsimp only [hj]
        rw [dite_eq_right hij, dite_eq_left hji]
      rw [hhj, Preadditive.comp_neg]
      simp only [alternatingCechSheafPresheafD, Pi.lift_comp_π_assoc, Category.assoc,
        Preadditive.sum_comp, Preadditive.zsmul_comp]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
      simp only [capIntoCap_comp]
      have h0 : (Fin.succAboveOrderEmb (0 : Fin 2)).trans (pairTuple (t 0) i hji) =
          singletonTuple i := by
        ext k
        fin_cases k
        rfl
      have h1 : (Fin.succAboveOrderEmb (1 : Fin 2)).trans (pairTuple (t 0) i hji) = t := by
        ext k
        fin_cases k
        rfl
      rw [transport _ _ _ inf_le_right h1, capIntoCap_unit]
      rw [transport _ _ _ (by simp [alternatingCechIntersection, singletonTuple]) h0]
      abel
    · have he : t = singletonTuple i := by
        ext k
        fin_cases k
        exact le_antisymm (le_of_not_gt hij) (le_of_not_gt hji)
      have hhj : hj t = 0 := by
        dsimp only [hj]
        rw [dite_eq_right hij, dite_eq_right hji]
      rw [hhj, comp_zero, zero_add]
      rw [transport _ _ _ inf_le_right he.symm, capIntoCap_unit]

end AlgebraicGeometry

