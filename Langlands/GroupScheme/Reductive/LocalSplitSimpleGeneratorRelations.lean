import Langlands.GroupScheme.Reductive.LocalSplitGeneratorRelations
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell

/-! # Big-cell gluing from simple-root generator relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalSplitCell

section WeylGenerators

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u} {m n : ℕ}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {Ω : cellObj R I m n ⟶ G.X} {Ω' : cellObj R I m n ⟶ H.X}

/-- Right-good pairs are closed under conjugation. -/
theorem RightGood.conj [IsAffine H.X.left] [IsOpenImmersion Ω.left] (hΩ : HasCellFactors Ω)
    {Z : Over (Spec (CommRingCat.of R))} {g₁ g₂ : Z ⟶ G.X} {h₁ h₂ : Z ⟶ H.X}
    (hg₁ : RightGood Ω Ω' g₁ h₁) (hg₂ : RightGood Ω Ω' g₂ h₂) :
    RightGood Ω Ω' (g₁ * g₂ * g₁⁻¹) (h₁ * h₂ * h₁⁻¹) :=
  (hg₁.mul hΩ hg₂).mul hΩ hg₁.inv

/-- The pulled-back Weyl point `v'(-1) v(1) v'(-1)` is right-good when its three factors
are. -/
theorem rightGood_constantPoint_weylPoint [IsAffine H.X.left] [IsOpenImmersion Ω.left]
    (hΩ : HasCellFactors Ω) {v w : Ga R ⟶ G} {v' w' : Ga R ⟶ H}
    (h₁ : ∀ Z : Over (Spec (CommRingCat.of R)),
      RightGood Ω Ω' (rootPoint v Z 1) (rootPoint v' Z 1))
    (h₂ : ∀ Z : Over (Spec (CommRingCat.of R)),
      RightGood Ω Ω' (rootPoint w Z (-1)) (rootPoint w' Z (-1)))
    (Z : Over (Spec (CommRingCat.of R))) :
    RightGood Ω Ω' (G.constantPoint (weylPoint v w) Z) (H.constantPoint (weylPoint v' w') Z) := by
  rw [constantPoint_weylPoint, constantPoint_weylPoint]
  exact ((h₂ Z).mul hΩ (h₁ Z)).mul hΩ (h₂ Z)

variable (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Conjugation along a word of right-good Weyl points preserves right-goodness of root
points. -/
theorem rightGood_rootPoint_wordConj [IsAffine H.X.left] [IsOpenImmersion Ω.left]
    (hΩ : HasCellFactors Ω) {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)} (l : List J)
    (hN : ∀ j ∈ l, ∀ Z : Over (Spec (CommRingCat.of R)), RightGood Ω Ω'
      (G.constantPoint (rootWeylPoint P u j) Z) (H.constantPoint (rootWeylPoint P u' j) Z))
    {w : Ga R ⟶ G} {w' : Ga R ⟶ H}
    (hw : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)),
      RightGood Ω Ω' (rootPoint w Z c) (rootPoint w' Z c))
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    RightGood Ω Ω' (rootPoint (wordConj P u l w) Z c) (rootPoint (wordConj P u' l w') Z c) := by
  induction l with
  | nil => exact hw Z c
  | cons j l ih =>
    change RightGood Ω Ω'
      (rootPoint (wordConj P u l w ≫ (G.innerIso (rootWeylPoint P u j)).hom) Z c)
      (rootPoint (wordConj P u' l w' ≫ (H.innerIso (rootWeylPoint P u' j)).hom) Z c)
    rw [rootPoint_comp, rootPoint_comp, GroupScheme.comp_innerIso_hom,
      GroupScheme.comp_innerIso_hom]
    exact (hN j List.mem_cons_self Z).conj hΩ
      (ih fun j' hj' => hN j' (List.mem_cons_of_mem _ hj'))

/-- If the simple-root points at all arguments and the points `u_{-a}(-1)` are right-good,
then so are all points of the Weyl family. -/
theorem rightGood_rootPoint_weylFamily [IsAffine H.X.left] [IsOpenImmersion Ω.left]
    (hΩ : HasCellFactors Ω) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hs : ∀ a ∈ b.support, ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)),
      RightGood Ω Ω' (rootPoint (u a) Z c) (rootPoint (u' a) Z c))
    (hneg : ∀ a ∈ b.support, ∀ Z : Over (Spec (CommRingCat.of R)),
      RightGood Ω Ω' (rootPoint (u (P.reflectionPerm a a)) Z (-1))
        (rootPoint (u' (P.reflectionPerm a a)) Z (-1)))
    (α : J) (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    RightGood Ω Ω' (rootPoint (weylFamily P W u α) Z c)
      (rootPoint (weylFamily P W u' α) Z c) :=
  rightGood_rootPoint_wordConj P hΩ (W α).word
    (fun j hj => rightGood_constantPoint_weylPoint hΩ
      (fun Z => hs j ((W α).word_mem j hj) Z 1) (hneg j ((W α).word_mem j hj)))
    (hs _ (W α).simple_mem) Z c

/-- Right translation by the simple-root points `u_a(c)`, for every simple root `a` and every
global function `c`, carries relations between `G`-cell points to the same relations between
`H`-cell points, over local test rings with separably closed residue fields. -/
def SimpleRootRelations (Ω : cellObj R I m n ⟶ G.X) (Ω' : cellObj R I m n ⟶ H.X)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (x y : Over.mk s ⟶ cellObj R I m n)
    (a : J), a ∈ b.support → ∀ c : Γ((Over.mk s).left, ⊤),
    (x ≫ Ω) * rootPoint (u a) (Over.mk s) c = y ≫ Ω →
      (x ≫ Ω') * rootPoint (u' a) (Over.mk s) c = y ≫ Ω'

/-- Right translation by the points `u_{-a}(-1)`, for every simple root `a`, carries relations
between `G`-cell points to the same relations between `H`-cell points, over local test rings
with separably closed residue fields. The index of `-a` is `P.reflectionPerm a a`. -/
def NegSimpleRelations (Ω : cellObj R I m n ⟶ G.X) (Ω' : cellObj R I m n ⟶ H.X)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (x y : Over.mk s ⟶ cellObj R I m n)
    (a : J), a ∈ b.support →
    (x ≫ Ω) * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) = y ≫ Ω →
      (x ≫ Ω') * rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-1) = y ≫ Ω'

variable {P}

theorem rightGood_simpleRootPoint {b : P.Base} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hS : SimpleRootRelations P Ω Ω' b u u') {a : J} (ha : a ∈ b.support)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    RightGood Ω Ω' (rootPoint (u a) Z c) (rootPoint (u' a) Z c) := by
  intro B _ _ _ sB f x y hxy
  rw [comp_rootPoint] at hxy ⊢
  exact hS B sB x y a ha _ hxy

theorem rightGood_negSimpleRootPoint {b : P.Base} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)} (hN : NegSimpleRelations P Ω Ω' b u u') {a : J}
    (ha : a ∈ b.support) (Z : Over (Spec (CommRingCat.of R))) :
    RightGood Ω Ω' (rootPoint (u (P.reflectionPerm a a)) Z (-1))
      (rootPoint (u' (P.reflectionPerm a a)) Z (-1)) := by
  intro B _ _ _ sB f x y hxy
  rw [comp_rootPoint, map_neg, map_one] at hxy ⊢
  exact hN B sB x y a ha hxy

/-- The simple-root relations give the root relations of the Weyl families. -/
theorem rootRelations_weylFamily [IsAffine H.X.left] [IsOpenImmersion Ω.left]
    (hΩ : HasCellFactors Ω) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)} (hS : SimpleRootRelations P Ω Ω' b u u')
    (hN : NegSimpleRelations P Ω Ω' b u u') :
    RootRelations Ω Ω' (weylFamily P W u) (weylFamily P W u') := by
  intro A _ _ _ s x y α c hxy
  have h := rightGood_rootPoint_weylFamily P hΩ W
    (fun a ha Z c => rightGood_simpleRootPoint hS ha Z c)
    (fun a ha Z => rightGood_negSimpleRootPoint hN ha Z) α (Over.mk s) c
  have e := h A s (𝟙 _) x y (by rw [Category.id_comp]; exact hxy)
  rwa [Category.id_comp] at e

variable [DecidableEq I] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {neg : Fin m → J} {pos : Fin n → J}

/-- **Big-cell gluing from simple-root relations.** Take Weyl-normalized simple-root data for
`G` and `H` and form the two Weyl families. If right translation by the simple-root points and
by the points `u_{-a}(-1)` carries relations between cell points of the Weyl family of `G` to
the same relations for `H`, over local test rings with separably closed residue fields, then
`G` and `H` are isomorphic by an isomorphism matching the big-cell maps. -/
theorem exists_iso_of_simpleRootRelations (hG : IsReductive G) (hH : IsReductive H)
    {b : P.Base} (W : ∀ α, SimpleWord P b α) {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a))
    (hw' : ∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a))
    [IsOpenImmersion (cellMap i (weylFamily P W u) neg pos).left]
    [IsOpenImmersion (cellMap i' (weylFamily P W u') neg pos).left]
    (hS : SimpleRootRelations P (cellMap i (weylFamily P W u) neg pos)
      (cellMap i' (weylFamily P W u') neg pos) b u u')
    (hN : NegSimpleRelations P (cellMap i (weylFamily P W u) neg pos)
      (cellMap i' (weylFamily P W u') neg pos) b u u') :
    ∃ ψ : G ≅ H, cellMap i (weylFamily P W u) neg pos ≫ ψ.hom.hom.hom =
      cellMap i' (weylFamily P W u') neg pos := by
  have := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hΩ : HasCellFactors (cellMap i (weylFamily P W u) neg pos) := hasCellFactors_cellMap hG
  exact exists_iso_of_rootRelations (ch := fun α => P.root α) hG hH
    (fun α Z t c => (isRootParametrization_weylFamily hu hw W α).equivariant Z t c)
    (fun α Z t c => (isRootParametrization_weylFamily hu' hw' W α).equivariant Z t c)
    (rootRelations_weylFamily hΩ W hS hN)

end WeylGenerators

end LocalSplitCell

open LocalSplitCell in
/-- Big-cell gluing over an arbitrary commutative ring from simple-root relations. Let `G` and
`H` be reductive with fibrewise maximal coordinate split tori `i`, `i'` carrying the same
fibrewise root datum `P`, and take Weyl-normalized simple-root data `u`, `u'` for a base `b`.
If right translation by the simple-root points `u_a(c)` and by the points `u_{-a}(-1)`
transfers relations between the big-cell points of the two Weyl families, over local test
rings with separably closed residue fields, then `G ≅ H` matching the two big-cell maps. -/
def LocalSplitSimpleRootRelationIsomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (J : Type u)
    (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H),
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i' →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I H i' P →
      ∀ (b : P.Base) (W : ∀ α, SimpleWord P b α)
        (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a)) →
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) →
      (∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a)) →
      (∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) →
      ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
        (x y : Over.mk s ⟶ cellObj R I m n) (a : J), a ∈ b.support →
        ∀ c : Γ((Over.mk s).left, ⊤),
        (x ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u a) (Over.mk s) c =
          y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) →
        (x ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u' a) (Over.mk s) c =
          y ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) →
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
        (x y : Over.mk s ⟶ cellObj R I m n) (a : J), a ∈ b.support →
        (x ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) =
          y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) →
        (x ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-1) =
          y ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) →
      ∃ ψ : G ≅ H,
        cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) ≫
            ψ.hom.hom.hom =
          cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))

/-- Simple-root relations suffice for big-cell gluing of the Weyl families. -/
theorem localSplitSimpleRootRelationIsomorphism :
    LocalSplitSimpleRootRelationIsomorphismStatement.{u} := by
  intro R _ I _ _ J G H _ _ hG hH i i' hmax hmax' P hP hP' b W u u' hu hw hu' hw' m n neg pos
    hS hN
  have : IsOpenImmersion (LocalSplitCell.cellMap i (LocalSplitCell.weylFamily P W u)
      (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _
      (LocalSplitCell.isRootParametrization_weylFamily hu hw W) neg pos
  have : IsOpenImmersion (LocalSplitCell.cellMap i' (LocalSplitCell.weylFamily P W u')
      (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hH hmax' hP' b _
      (LocalSplitCell.isRootParametrization_weylFamily hu' hw' W) neg pos
  exact LocalSplitCell.exists_iso_of_simpleRootRelations hG hH W hu hw hu' hw' hS hN

end Langlands.GroupScheme
