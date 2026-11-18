import Langlands.Cohomology.SiteCech.FiniteCechPresentation

/-! # Differential compatibility of finite tuple-cone presentations -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial BigOperators

universe u v w a

variable {C : Type u} [Category.{v} C]

/-- Reindex a finite tuple by a simplex morphism, using the fixed finite
enumerations in the canonical tuple-cone presentation. -/
def cechTupleIndexMap {m n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌) :
    Fin (Fintype.card (Fin (k + 1) → Fin m)) →
      Fin (Fintype.card (Fin (n + 1) → Fin m)) :=
  fun i => Fintype.equivFin _ ((Fintype.equivFin _).symm i ∘ θ.toOrderHom)

@[simp]
theorem cechTupleIndexMap_tuple {m n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (i : Fin (Fintype.card (Fin (k + 1) → Fin m))) :
    (Fintype.equivFin _).symm (cechTupleIndexMap θ i) =
      (Fintype.equivFin _).symm i ∘ θ.toOrderHom :=
  Equiv.symm_apply_apply _ _

/-- The universal map to the tuple cone with reindexed projections. -/
def tupleConeMap {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ n (α : Fin (n + 1) → Fin m),
      WidePullbackCone (fun j => f (α j)))
    (hc : ∀ n α, IsLimit (c n α)) {n k : ℕ}
    (θ : ⦋n⦌ ⟶ ⦋k⦌) (α : Fin (k + 1) → Fin m) :
    (c k α).pt ⟶ (c n (α ∘ θ.toOrderHom)).pt :=
  WidePullbackCone.IsLimit.lift (hc n _) (c k α).base
    (fun j => (c k α).π (θ.toOrderHom j))
    (fun j => (c k α).condition (θ.toOrderHom j))

@[reassoc (attr := simp)]
theorem tupleConeMap_π {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ n (α : Fin (n + 1) → Fin m),
      WidePullbackCone (fun j => f (α j)))
    (hc : ∀ n α, IsLimit (c n α)) {n k : ℕ}
    (θ : ⦋n⦌ ⟶ ⦋k⦌) (α : Fin (k + 1) → Fin m) (j : Fin (n + 1)) :
    tupleConeMap f c hc θ α ≫ (c n (α ∘ θ.toOrderHom)).π j =
      (c k α).π (θ.toOrderHom j) :=
  WidePullbackCone.IsLimit.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleConeMap_base {m : ℕ} {U : C} {V : Fin m → C}
    (f : ∀ i, V i ⟶ U)
    (c : ∀ n (α : Fin (n + 1) → Fin m),
      WidePullbackCone (fun j => f (α j)))
    (hc : ∀ n α, IsLimit (c n α)) {n k : ℕ}
    (θ : ⦋n⦌ ⟶ ⦋k⦌) (α : Fin (k + 1) → Fin m) :
    tupleConeMap f c hc θ α ≫ (c n (α ∘ θ.toOrderHom)).base =
      (c k α).base :=
  WidePullbackCone.IsLimit.lift_base _ _ _ _

variable [LocallySmall.{w} C]
variable (J : GrothendieckTopology C) {ι : Type a} (B : ι → C)
variable {U : C} (s : FiniteBasisCover J B U)
variable (b : ∀ n, (Fin (n + 1) → Fin s.size) → ι)
variable (c : ∀ n (α : Fin (n + 1) → Fin s.size),
  WidePullbackCone (fun j => s.arrow (α j)))
variable (hc : ∀ n α, IsLimit (c n α))
variable (e : ∀ n α, (c n α).pt ≅ B (b n α))

/-- Transport a tuple map to basis representatives with an explicitly supplied
identification of the target tuple. -/
def FiniteBasisCover.tupleMapArrowTo {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (α : Fin (k + 1) → Fin s.size) (β : Fin (n + 1) → Fin s.size)
    (h : β = α ∘ θ.toOrderHom) : B (b k α) ⟶ B (b n β) :=
  (e k α).inv ≫ tupleConeMap s.arrow c hc θ α ≫
    (e n (α ∘ θ.toOrderHom)).hom ≫
      eqToHom (congrArg (fun γ => B (b n γ)) h.symm)

/-- A transported tuple map has the prescribed presheaf projection. -/
theorem FiniteBasisCover.tupleMapArrowTo_π {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (α : Fin (k + 1) → Fin s.size) (β : Fin (n + 1) → Fin s.size)
    (h : β = α ∘ θ.toOrderHom) (j : Fin (n + 1)) :
    shrinkYoneda.{w}.map (s.tupleMapArrowTo J B b c hc e θ α β h) ≫
      shrinkYoneda.{w}.map ((e n β).inv ≫ (c n β).π j) ≫
        Sigma.ι (fun l => shrinkYoneda.{w}.obj (B (s.index l))) (β j) =
      shrinkYoneda.{w}.map ((e k α).inv ≫ (c k α).π (θ.toOrderHom j)) ≫
        Sigma.ι (fun l => shrinkYoneda.{w}.obj (B (s.index l)))
          (α (θ.toOrderHom j)) := by
  subst β
  simp only [FiniteBasisCover.tupleMapArrowTo, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp]
  simp [Category.assoc]

/-- A transported tuple map has the prescribed presheaf base map. -/
theorem FiniteBasisCover.tupleMapArrowTo_base {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (α : Fin (k + 1) → Fin s.size) (β : Fin (n + 1) → Fin s.size)
    (h : β = α ∘ θ.toOrderHom) :
    shrinkYoneda.{w}.map (s.tupleMapArrowTo J B b c hc e θ α β h) ≫
      shrinkYoneda.{w}.map ((e n β).inv ≫ (c n β).base) =
      shrinkYoneda.{w}.map ((e k α).inv ≫ (c k α).base) := by
  subst β
  simp [FiniteBasisCover.tupleMapArrowTo, ← Functor.map_comp, Category.assoc]

/-- The tuple map transported to the chosen basis representatives. -/
def FiniteBasisCover.tupleMapArrow {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (i : Fin (Fintype.card (Fin (k + 1) → Fin s.size))) :
    B ((s.cechPresentationOfCones J B b c hc e).index k i) ⟶
      B ((s.cechPresentationOfCones J B b c hc e).index n
        (cechTupleIndexMap θ i)) :=
  s.tupleMapArrowTo J B b c hc e θ ((Fintype.equivFin _).symm i)
    ((Fintype.equivFin _).symm (cechTupleIndexMap θ i))
    (cechTupleIndexMap_tuple θ i)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inverse presentation intertwines each simplex map with the
map of tuple cones, on every finite summand. -/
theorem FiniteBasisCover.cechPresentationOfCones_ι_inv_map
    {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌)
    (i : Fin (Fintype.card (Fin (k + 1) → Fin s.size))) :
    Sigma.ι (fun i => shrinkYoneda.{w}.obj
        (B (b k ((Fintype.equivFin _).symm i)))) i ≫
      ((s.cechPresentationOfCones J B b c hc e).iso k).inv ≫
        (s.presheafArrow J B).cechNerve.map θ.op =
      shrinkYoneda.{w}.map (s.tupleMapArrow J B b c hc e θ i) ≫
        Sigma.ι (fun i => shrinkYoneda.{w}.obj
          (B (b n ((Fintype.equivFin _).symm i))))
            (cechTupleIndexMap θ i) ≫
              ((s.cechPresentationOfCones J B b c hc e).iso n).inv := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Arrow.cechNerve_map, Category.assoc, WidePullback.lift_π]
    erw [FiniteBasisCover.cechPresentationOfCones_ι_inv_π,
      FiniteBasisCover.cechPresentationOfCones_ι_inv_π]
    change (_ : _ ⟶ ∐ (fun k => shrinkYoneda.{w}.obj (B (s.index k)))) = _
    dsimp only [FiniteBasisCover.tupleMapArrow,
      FiniteBasisCover.cechPresentationOfCones, FiniteBasisCover.presheafArrow,
      Arrow.mk_left, Arrow.mk_right]
    exact (s.tupleMapArrowTo_π J B b c hc e θ _ _ (cechTupleIndexMap_tuple θ i) j).symm
  · simp only [Arrow.cechNerve_map, Category.assoc, WidePullback.lift_base]
    erw [FiniteBasisCover.cechPresentationOfCones_ι_inv_base,
      FiniteBasisCover.cechPresentationOfCones_ι_inv_base]
    change (_ : _ ⟶ shrinkYoneda.{w}.obj U) = _
    dsimp only [FiniteBasisCover.tupleMapArrow,
      FiniteBasisCover.cechPresentationOfCones, FiniteBasisCover.presheafArrow,
      Arrow.mk_left, Arrow.mk_right]
    exact (s.tupleMapArrowTo_base J B b c hc e θ _ _ (cechTupleIndexMap_tuple θ i)).symm

/-- The ordinary map on finite representable sums induced by a simplex map. -/
def FiniteBasisCover.tuplePresheafMap {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌) :
    (∐ fun i => shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index k i))) ⟶
    ∐ fun i => shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index n i)) :=
  Sigma.map' (cechTupleIndexMap θ)
    (fun i => shrinkYoneda.{w}.map (s.tupleMapArrow J B b c hc e θ i))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical finite presentation identifies the actual nerve map with the
coproduct of the universal tuple maps. -/
theorem FiniteBasisCover.cechPresentationOfCones_inv_map
    {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌) :
    ((s.cechPresentationOfCones J B b c hc e).iso k).inv ≫
        (s.presheafArrow J B).cechNerve.map θ.op =
      s.tuplePresheafMap J B b c hc e θ ≫
        ((s.cechPresentationOfCones J B b c hc e).iso n).inv := by
  apply Sigma.hom_ext
  intro i
  simp only [FiniteBasisCover.tuplePresheafMap, Sigma.ι_comp_map'_assoc]
  exact s.cechPresentationOfCones_ι_inv_map J B b c hc e θ i

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

set_option backward.isDefEq.respectTransparency false in
/-- On each summand, the inverse free-term comparison is the free image of the
inverse presheaf comparison. -/
theorem FiniteBasisCover.CechPresentation.ι_freeTermIso_inv
    (p : s.CechPresentation J B) (n : ℕ) (i : Fin (p.size n)) :
    Sigma.ι (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (B (p.index n j)))) i ≫
      (p.freeTermIso J B R n).inv =
        (freeSheafFunctor J R).map
          (Sigma.ι (fun j => shrinkYoneda.{w}.obj (B (p.index n j))) i ≫
            (p.iso n).inv) := by
  change Sigma.ι _ i ≫ ((PreservesCoproduct.iso (freeSheafFunctor J R)
    (fun j => shrinkYoneda.{w}.obj (B (p.index n j)))).inv ≫
      (freeSheafFunctor J R).map (p.iso n).inv) = _
  rw [PreservesCoproduct.inv_hom, ← Category.assoc, ι_comp_sigmaComparison,
    Functor.map_comp]

/-- The free-sheaf coproduct map induced by the universal tuple maps. -/
def FiniteBasisCover.tupleFreeMap {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌) :
    (∐ fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index k i)))) ⟶
    ∐ fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index n i))) :=
  Sigma.map' (cechTupleIndexMap θ)
    (fun i => (freeSheafFunctor J R).map
      (shrinkYoneda.{w}.map (s.tupleMapArrow J B b c hc e θ i)))

set_option backward.isDefEq.respectTransparency false in
/-- Free sheaves carry the actual nerve-map square to the chosen free-term
comparison isomorphisms. -/
theorem FiniteBasisCover.cechPresentationOfCones_free_inv_map
    {n k : ℕ} (θ : ⦋n⦌ ⟶ ⦋k⦌) :
    ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R k).inv ≫
        (freeCechNerve J R (s.presheafArrow J B)).map θ.op =
      s.tupleFreeMap J B b c hc e R θ ≫
        ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R n).inv := by
  apply Sigma.hom_ext
  intro i
  dsimp only [FiniteBasisCover.tupleFreeMap]
  erw [Sigma.ι_comp_map'_assoc, ← Category.assoc,
    FiniteBasisCover.CechPresentation.ι_freeTermIso_inv,
    FiniteBasisCover.CechPresentation.ι_freeTermIso_inv]
  change (freeSheafFunctor J R).map _ ≫
      (freeSheafFunctor J R).map ((s.presheafArrow J B).cechNerve.map θ.op) = _
  rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc]
  exact congrArg ((freeSheafFunctor J R).map)
    (s.cechPresentationOfCones_ι_inv_map J B b c hc e θ i)

/-- The signed finite-sum boundary obtained by omitting each tuple entry. -/
def FiniteBasisCover.tupleFreeBoundary (n : ℕ) :
    (∐ fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index (n + 1) i)))) ⟶
    ∐ fun i => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj
      (B ((s.cechPresentationOfCones J B b c hc e).index n i))) :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
    s.tupleFreeMap J B b c hc e R (SimplexCategory.δ j)

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary signed boundary agrees with the actual free Čech differential
through the canonical term isomorphisms. -/
theorem FiniteBasisCover.cechPresentationOfCones_free_inv_d (n : ℕ) :
    ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R (n + 1)).inv ≫
        (freeCechChainComplex J R (s.presheafArrow J B)).d (n + 1) n =
      s.tupleFreeBoundary J B b c hc e R n ≫
        ((s.cechPresentationOfCones J B b c hc e).freeTermIso J B R n).inv := by
  change _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (freeCechNerve J R (s.presheafArrow J B))).d (n + 1) n = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  dsimp only [FiniteBasisCover.tupleFreeBoundary, SimplicialObject.δ]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteBasisCover.cechPresentationOfCones_free_inv_map]

end Langlands.Cohomology.SiteCech
