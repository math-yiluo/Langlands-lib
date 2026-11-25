/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject

/-!
# Matching objects as limits over proper faces

Source: Stacks Project, simplicial.tex, Lemma 0186 (lemma-formula-limit), restricted to
injective proper faces (auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialObject

/-- The property selecting injective proper faces in the over category of `[n]`.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node). -/
def properFaceProperty (n : ℕ) : ObjectProperty (Over ⦋n⦌) :=
  fun a ↦ a.left.len < n ∧ Function.Injective a.hom.toOrderHom

/-- The category `I_n` of injective proper faces, with commuting triangles as arrows.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node). -/
abbrev ProperFaceCategory (n : ℕ) := (properFaceProperty n).FullSubcategory

/-- The codimension-one face omitting `i` as an object of `I_(n+1)`.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node). -/
def properFace (n : ℕ) (i : Fin (n + 2)) : ProperFaceCategory (n + 1) :=
  ⟨Over.mk (SimplexCategory.δ i), Nat.lt_succ_self n,
    SimplexCategory.mono_iff_injective.mp
      (inferInstance : Mono (SimplexCategory.δ i))⟩

/-- The contravariant proper-face diagram `P_n(K)`.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node). -/
def properFaceDiagram {C : Type u} [Category.{v} C] (K : SimplicialObject C) (n : ℕ) :
    (ProperFaceCategory n)ᵒᵖ ⥤ C :=
  ((properFaceProperty n).ι ⋙ Over.forget ⦋n⦌).op ⋙ K

private theorem face_factor (n : ℕ) (a : ProperFaceCategory (n + 1)) :
    ∃ (i : Fin (n + 2)) (ε : a.obj.left ⟶ ⦋n⦌),
      ε ≫ SimplexCategory.δ i = a.obj.hom := by
  obtain ⟨i, ε, hε⟩ := SimplexCategory.eq_comp_δ_of_not_surjective a.obj.hom (by
    intro h
    have hcard := Fintype.card_le_of_surjective _ h
    simp only [Fintype.card_fin] at hcard
    have := a.property.1
    omega)
  exact ⟨i, ε, hε.symm⟩

private theorem family_factor {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C}
    (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 1))
    (a : ProperFaceCategory (n + 1)) (i : Fin (n + 2))
    (ε : a.obj.left ⟶ ⦋n⦌) (hε : ε ≫ SimplexCategory.δ i = a.obj.hom) :
    x.app (op a) = x.app (op (properFace n i)) ≫ K.map ε.op := by
  let f : a ⟶ properFace n i := ObjectProperty.homMk (Over.homMk ε hε)
  simpa [properFaceDiagram, f] using x.naturality f.op

private theorem family_ext {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C}
    {x y : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 1)}
    (h : ∀ i, x.app (op (properFace n i)) = y.app (op (properFace n i))) : x = y := by
  apply NatTrans.ext
  funext a
  obtain ⟨i, ε, hε⟩ := face_factor n a.unop
  rw [family_factor K n x a.unop i ε hε, family_factor K n y a.unop i ε hε, h]

private noncomputable def extendFamily {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C} (x : Fin (n + 2) → (W ⟶ K _⦋n⦌))
    (hx : ∀ (a : ProperFaceCategory (n + 1)) (i j : Fin (n + 2))
      (ε φ : a.obj.left ⟶ ⦋n⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
      φ ≫ SimplexCategory.δ j = a.obj.hom → x i ≫ K.map ε.op = x j ≫ K.map φ.op) :
    (Functor.const _).obj W ⟶ properFaceDiagram K (n + 1) := by
  classical
  choose i ε hε using face_factor n
  refine { app := fun a ↦ x (i a.unop) ≫ K.map (ε a.unop).op, naturality := ?_ }
  intro a b f
  dsimp [properFaceDiagram]
  rw [Category.id_comp, Category.assoc, ← K.map_comp]
  apply (hx b.unop (i a.unop) (i b.unop)
    (f.unop.hom.left ≫ ε a.unop) (ε b.unop) ?_ (hε b.unop)).symm
  rw [Category.assoc, hε]
  exact Over.w f.unop.hom

private theorem extendFamily_factor {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C} (x : Fin (n + 2) → (W ⟶ K _⦋n⦌))
    (hx : ∀ (a : ProperFaceCategory (n + 1)) (i j : Fin (n + 2))
      (ε φ : a.obj.left ⟶ ⦋n⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
      φ ≫ SimplexCategory.δ j = a.obj.hom → x i ≫ K.map ε.op = x j ≫ K.map φ.op)
    (a : ProperFaceCategory (n + 1)) (i : Fin (n + 2))
    (ε : a.obj.left ⟶ ⦋n⦌) (hε : ε ≫ SimplexCategory.δ i = a.obj.hom) :
    (extendFamily K n x hx).app (op a) = x i ≫ K.map ε.op := by
  classical
  dsimp [extendFamily]
  apply hx
  · exact (face_factor n a).choose_spec.choose_spec
  · exact hε

private theorem extendFamily_face {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C} (x : Fin (n + 2) → (W ⟶ K _⦋n⦌))
    (hx : ∀ (a : ProperFaceCategory (n + 1)) (i j : Fin (n + 2))
      (ε φ : a.obj.left ⟶ ⦋n⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
      φ ≫ SimplexCategory.δ j = a.obj.hom → x i ≫ K.map ε.op = x j ≫ K.map φ.op)
    (i : Fin (n + 2)) :
    (extendFamily K n x hx).app (op (properFace n i)) = x i := by
  simpa [properFace] using
    extendFamily_factor K n x hx (properFace n i) i (𝟙 _) (by simp [properFace])

private theorem factor_independent_one {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) {W : C} (x : Fin 2 → (W ⟶ K _⦋0⦌))
    (a : ProperFaceCategory 1) (i j : Fin 2) (ε φ : a.obj.left ⟶ ⦋0⦌)
    (hε : ε ≫ SimplexCategory.δ i = a.obj.hom)
    (hφ : φ ≫ SimplexCategory.δ j = a.obj.hom) :
    x i ≫ K.map ε.op = x j ≫ K.map φ.op := by
  have he : ε = φ := Subsingleton.elim _ _
  have : Epi ε := SimplexCategory.epi_iff_surjective.mpr (by
    intro z
    exact ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩)
  have hij : i = j := SimplexCategory.δ_injective
    ((cancel_epi ε).mp (by rw [hε, he, hφ]))
  subst j
  rw [he]

private theorem factor_independent_lt {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C}
    (x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌))
    (hx : ∀ p : (matchingBoundaryShape n).R,
      x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
        x p.val.2 ≫ (matchingBoundaryIndex K n).snd p)
    (a : ProperFaceCategory (n + 2)) (i j : Fin (n + 3)) (hij : i < j)
    (ε φ : a.obj.left ⟶ ⦋n + 1⦌)
    (hε : ε ≫ SimplexCategory.δ i = a.obj.hom)
    (hφ : φ ≫ SimplexCategory.δ j = a.obj.hom) :
    x i ≫ K.map ε.op = x j ≫ K.map φ.op := by
  let i' : Fin (n + 2) := i.castLT (Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt))
  let j' : Fin (n + 2) := j.pred (Fin.ne_zero_of_lt hij)
  have hδ : SimplexCategory.δ j' ≫ SimplexCategory.δ i =
      SimplexCategory.δ i' ≫ SimplexCategory.δ j := by
    exact (SimplexCategory.δ_comp_δ' (i := i') (j := j)
      (by simpa [i'] using hij)).symm
  obtain ⟨ξ, hξ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' ε j' (by
    intro z hz
    have h := congrArg (fun f ↦ f.toOrderHom z) (hε.trans hφ.symm)
    change i.succAbove (ε.toOrderHom z) = j.succAbove (φ.toOrderHom z) at h
    rw [hz, Fin.succAbove_pred_of_lt _ _ hij] at h
    exact (Fin.ne_succAbove j (φ.toOrderHom z)) h)
  have hφ' : φ = ξ ≫ SimplexCategory.δ i' := by
    apply (cancel_mono (SimplexCategory.δ j)).mp
    rw [hφ, Category.assoc, ← hδ, ← Category.assoc, ← hξ, hε]
  rw [hξ, hφ']
  simp only [op_comp, K.map_comp]
  simpa only [matchingBoundaryIndex, SimplicialObject.δ, i', j', Category.assoc] using
    congrArg (fun f ↦ f ≫ K.map ξ.op) (hx ⟨(i, j), hij⟩)

private theorem factor_independent {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C}
    (x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌))
    (hx : ∀ p : (matchingBoundaryShape n).R,
      x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
        x p.val.2 ≫ (matchingBoundaryIndex K n).snd p)
    (a : ProperFaceCategory (n + 2)) (i j : Fin (n + 3))
    (ε φ : a.obj.left ⟶ ⦋n + 1⦌)
    (hε : ε ≫ SimplexCategory.δ i = a.obj.hom)
    (hφ : φ ≫ SimplexCategory.δ j = a.obj.hom) :
    x i ≫ K.map ε.op = x j ≫ K.map φ.op := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact factor_independent_lt K n x hx a i j hij ε φ hε hφ
  · have : ε = φ := (cancel_mono (SimplexCategory.δ i)).mp (hε.trans hφ.symm)
    rw [this]
  · exact (factor_independent_lt K n x hx a j i hji φ ε hφ hε).symm

private theorem restrict_compatible {C : Type u} [Category.{v} C]
    (K : SimplicialObject C) (n : ℕ) {W : C}
    (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 2))
    (p : (matchingBoundaryShape n).R) :
    x.app (op (properFace (n + 1) p.val.1)) ≫ (matchingBoundaryIndex K n).fst p =
      x.app (op (properFace (n + 1) p.val.2)) ≫ (matchingBoundaryIndex K n).snd p := by
  let i : Fin (n + 2) := p.val.1.castLT
    (Nat.lt_of_lt_of_le p.property (Nat.le_of_lt_succ p.val.2.isLt))
  let j : Fin (n + 2) := p.val.2.pred (Fin.ne_zero_of_lt p.property)
  have hδ : SimplexCategory.δ j ≫ SimplexCategory.δ p.val.1 =
      SimplexCategory.δ i ≫ SimplexCategory.δ p.val.2 :=
    (SimplexCategory.δ_comp_δ' (i := i) (j := p.val.2)
      (by simpa [i] using p.property)).symm
  let a : ProperFaceCategory (n + 2) :=
    ⟨Over.mk (SimplexCategory.δ j ≫ SimplexCategory.δ p.val.1), by
      constructor
      · exact Nat.lt_add_of_pos_right (by decide)
      · exact SimplexCategory.mono_iff_injective.mp
          (inferInstance : Mono (SimplexCategory.δ j ≫ SimplexCategory.δ p.val.1))⟩
  exact (family_factor K (n + 1) x a p.val.1 (SimplexCategory.δ j) rfl).symm.trans
    (family_factor K (n + 1) x a p.val.2 (SimplexCategory.δ i) hδ.symm)

/-- Degree one: compatible proper-face families are arbitrary pairs, naturally in the
vertex. The same matching object is a limit over proper faces, with components computed
by any face factorization, and its matching map has the prescribed components uniquely.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node).
Proof: every proper injective face factors through a codimension-one face
[lem-weil-pbc-simplex-face-factorization]. In degree one these are exactly the two vertices,
so restriction is a bijection onto pairs, commuting with precomposition. The product
universal property [lem-weil-pbc-simplicial-matching-object] gives the limit over these
faces; the matching-map identities give all its components and limit uniqueness. -/
theorem matching_object_proper_faces_one {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (c : Fan (fun _ : Fin 2 ↦ K _⦋0⦌))
    (hc : IsLimit c) (μ : K _⦋1⦌ ⟶ c.pt)
    (hμ : ∀ i : Fin 2, μ ≫ c.proj i = K.δ i) :
    (∃ E : ∀ W : C,
        ((Functor.const _).obj W ⟶ properFaceDiagram K 1) ≃
          (Fin 2 → (W ⟶ K _⦋0⦌)),
      (∀ (W : C) (x : (Functor.const _).obj W ⟶ properFaceDiagram K 1) (i : Fin 2),
        E W x i = x.app (op (properFace 0 i))) ∧
      (∀ (W W' : C) (f : W' ⟶ W)
          (x : (Functor.const _).obj W ⟶ properFaceDiagram K 1) (i : Fin 2),
        E W' ((Functor.const _).map f ≫ x) i = f ≫ E W x i)) ∧
    (∃ π : (Functor.const _).obj c.pt ⟶ properFaceDiagram K 1,
      Nonempty (IsLimit (Cone.mk c.pt π)) ∧
      (∀ (a : ProperFaceCategory 1) (i : Fin 2)
          (ε : a.obj.left ⟶ ⦋0⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
        π.app (op a) = c.proj i ≫ K.map ε.op) ∧
      (∀ a : ProperFaceCategory 1, μ ≫ π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ μ' : K _⦋1⦌ ⟶ c.pt,
        (∀ a : ProperFaceCategory 1, μ' ≫ π.app (op a) = K.map a.obj.hom.op) →
          μ' = μ)) := by
  classical
  let E (W : C) :
      ((Functor.const _).obj W ⟶ properFaceDiagram K 1) ≃
        (Fin 2 → (W ⟶ K _⦋0⦌)) :=
    { toFun := fun x i ↦ x.app (op (properFace 0 i))
      invFun := fun x ↦ extendFamily K 0 x (factor_independent_one K x)
      left_inv := fun x ↦ family_ext K 0 (fun i ↦ extendFamily_face K 0 _ _ i)
      right_inv := fun x ↦ funext (fun i ↦ extendFamily_face K 0 x _ i) }
  refine ⟨⟨E, (by intros; rfl), (by intros; rfl)⟩, ?_⟩
  let π := extendFamily K 0 c.proj (factor_independent_one K c.proj)
  have hπ (i : Fin 2) : π.app (op (properFace 0 i)) = c.proj i :=
    extendFamily_face K 0 c.proj _ i
  have hfac (a : ProperFaceCategory 1) (i : Fin 2) (ε : a.obj.left ⟶ ⦋0⦌)
      (hε : ε ≫ SimplexCategory.δ i = a.obj.hom) :
      π.app (op a) = c.proj i ≫ K.map ε.op :=
    extendFamily_factor K 0 c.proj _ a i ε hε
  refine ⟨π, ?_, hfac, ?_, ?_⟩
  · refine ⟨{
      lift := fun s ↦ Fan.IsLimit.lift hc (fun i ↦ s.π.app (op (properFace 0 i)))
      fac := ?_
      uniq := ?_ }⟩
    · intro s a
      obtain ⟨i, ε, hε⟩ := face_factor 0 a.unop
      rw [show (Cone.mk c.pt π).π.app a = π.app a from rfl, hfac a.unop i ε hε]
      rw [← Category.assoc, Fan.IsLimit.fac]
      exact (family_factor K 0 s.π a.unop i ε hε).symm
    · intro s f hf
      apply Fan.IsLimit.hom_ext hc
      intro i
      rw [Fan.IsLimit.fac]
      have h := hf (op (properFace 0 i))
      change f ≫ π.app (op (properFace 0 i)) = _ at h
      simpa only [hπ] using h
  · intro a
    obtain ⟨i, ε, hε⟩ := face_factor 0 a
    rw [hfac a i ε hε, ← Category.assoc, hμ]
    change K.map (SimplexCategory.δ i).op ≫ K.map ε.op = K.map a.obj.hom.op
    rw [← K.map_comp, ← op_comp, hε]
  · intro μ' hμ'
    apply Fan.IsLimit.hom_ext hc
    intro i
    rw [hμ]
    have h := hμ' (properFace 0 i)
    change μ' ≫ π.app (op (properFace 0 i)) = K.δ i at h
    simpa only [hπ] using h

/-- Degrees at least two: restriction to codimension-one faces gives the natural compatible
face-tuple bijection. Every limiting boundary cone is also a limit over all proper faces;
its components are independent of factorization, and characterize its matching map.
Source: Stacks, Tag 0186 (auxiliary; not a blueprint node).
Proof: factor each proper face through a missing vertex using
[lem-weil-pbc-simplex-face-factorization]. Restriction of a compatible family satisfies the
face-pair equations by [lem-weil-pbc-simplex-face-face-identity]. Conversely assign to a
proper face the composite through any missing vertex. Two choices factor through the face
omitting both vertices; the same identity and the tuple equation identify the composites.
This proves independence and, using functoriality [def-weil-pbc-simplicial-object], family
compatibility. The constructions are inverse and commute with precomposition. Apply this
to the boundary projections; composing the resulting bijection with the matching object's
universal property [lem-weil-pbc-simplicial-matching-object] proves the limit property.
Finally the matching-map face equations and functoriality give every proper-face component;
uniqueness follows from the limit property. -/
theorem matching_object_proper_faces_succ_succ {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (K : SimplicialObject C) (n : ℕ)
    (c : Cone (matchingBoundaryIndex K n).multicospan) (hc : IsLimit c)
    (μ : K _⦋n + 2⦌ ⟶ c.pt)
    (hμ : ∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = K.δ i) :
    (∃ E : ∀ W : C,
        ((Functor.const _).obj W ⟶ properFaceDiagram K (n + 2)) ≃
          {x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌) //
            ∀ p : (matchingBoundaryShape n).R,
              x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
                x p.val.2 ≫ (matchingBoundaryIndex K n).snd p},
      (∀ (W : C) (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 2))
          (i : Fin (n + 3)), (E W x).val i = x.app (op (properFace (n + 1) i))) ∧
      (∀ (W W' : C) (f : W' ⟶ W)
          (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 2)) (i : Fin (n + 3)),
        (E W' ((Functor.const _).map f ≫ x)).val i = f ≫ (E W x).val i)) ∧
    (∃ π : (Functor.const _).obj c.pt ⟶ properFaceDiagram K (n + 2),
      Nonempty (IsLimit (Cone.mk c.pt π)) ∧
      (∀ (a : ProperFaceCategory (n + 2)) (i : Fin (n + 3))
          (ε : a.obj.left ⟶ ⦋n + 1⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
        π.app (op a) = c.π.app (WalkingMulticospan.left i) ≫ K.map ε.op) ∧
      (∀ a : ProperFaceCategory (n + 2), μ ≫ π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ μ' : K _⦋n + 2⦌ ⟶ c.pt,
        (∀ a : ProperFaceCategory (n + 2),
          μ' ≫ π.app (op a) = K.map a.obj.hom.op) → μ' = μ)) := by
  classical
  let E (W : C) :
      ((Functor.const _).obj W ⟶ properFaceDiagram K (n + 2)) ≃
        {x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌) //
          ∀ p : (matchingBoundaryShape n).R,
            x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
              x p.val.2 ≫ (matchingBoundaryIndex K n).snd p} :=
    { toFun := fun x ↦ ⟨fun i ↦ x.app (op (properFace (n + 1) i)),
          restrict_compatible K n x⟩
      invFun := fun x ↦ extendFamily K (n + 1) x.val (factor_independent K n x.val x.property)
      left_inv := fun x ↦ family_ext K (n + 1)
        (fun i ↦ extendFamily_face K (n + 1) _ _ i)
      right_inv := fun x ↦ Subtype.ext (funext
        (fun i ↦ extendFamily_face K (n + 1) x.val
          (factor_independent K n x.val x.property) i)) }
  refine ⟨⟨E, (by intros; rfl), (by intros; rfl)⟩, ?_⟩
  let π := extendFamily K (n + 1) (Multifork.ι c)
    (factor_independent K n (Multifork.ι c) (Multifork.condition c))
  have hπ (i : Fin (n + 3)) : π.app (op (properFace (n + 1) i)) = (Multifork.ι c) i :=
    extendFamily_face K (n + 1) (Multifork.ι c) _ i
  have hfac (a : ProperFaceCategory (n + 2)) (i : Fin (n + 3))
      (ε : a.obj.left ⟶ ⦋n + 1⦌) (hε : ε ≫ SimplexCategory.δ i = a.obj.hom) :
      π.app (op a) = c.π.app (WalkingMulticospan.left i) ≫ K.map ε.op :=
    extendFamily_factor K (n + 1) (Multifork.ι c) _ a i ε hε
  refine ⟨π, ?_, hfac, ?_, ?_⟩
  · refine ⟨{
      lift := fun s ↦ Multifork.IsLimit.lift hc
        (fun i ↦ s.π.app (op (properFace (n + 1) i))) (restrict_compatible K n s.π)
      fac := ?_
      uniq := ?_ }⟩
    · intro s a
      obtain ⟨i, ε, hε⟩ := face_factor (n + 1) a.unop
      rw [show (Cone.mk c.pt π).π.app a = π.app a from rfl, hfac a.unop i ε hε]
      change _ ≫ (Multifork.ι c) i ≫ K.map ε.op = _
      rw [← Category.assoc, Multifork.IsLimit.fac]
      exact (family_factor K (n + 1) s.π a.unop i ε hε).symm
    · intro s f hf
      apply Multifork.IsLimit.hom_ext hc
      intro i
      rw [Multifork.IsLimit.fac]
      have h := hf (op (properFace (n + 1) i))
      change f ≫ π.app (op (properFace (n + 1) i)) = _ at h
      simpa only [hπ] using h
  · intro a
    obtain ⟨i, ε, hε⟩ := face_factor (n + 1) a
    rw [hfac a i ε hε, ← Category.assoc, hμ]
    change K.map (SimplexCategory.δ i).op ≫ K.map ε.op = K.map a.obj.hom.op
    rw [← K.map_comp, ← op_comp, hε]
  · intro μ' hμ'
    apply Multifork.IsLimit.hom_ext hc
    intro i
    change μ' ≫ c.π.app (WalkingMulticospan.left i) =
      μ ≫ c.π.app (WalkingMulticospan.left i)
    rw [hμ]
    have h := hμ' (properFace (n + 1) i)
    change μ' ≫ π.app (op (properFace (n + 1) i)) = K.δ i at h
    simpa only [hπ, Multifork.ι] using h

end CategoryTheory.SimplicialObject
