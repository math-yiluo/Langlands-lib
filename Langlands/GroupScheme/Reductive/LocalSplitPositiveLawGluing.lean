import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell
import Langlands.GroupScheme.Reductive.LocalSplitSimpleGeneratorRelations

/-! # Big-cell gluing from laws of the positive cell factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section PositiveLaw

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- If right multiplication by `g` changes the positive cell factor of a cell point `x` into the
positive factor with coordinates `z`, then it changes the cell point `x` into the cell point with
the negative and torus coordinates of `x` and positive coordinates `z`. -/
theorem comp_cellMap_mul_of_orderedProduct_mul {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ cellObj R I m n) (g : Z ⟶ G.X) (z : Fin n → Γ(Z.left, ⊤))
    (h : orderedProduct u pos Z (posCoord x) * g = orderedProduct u pos Z z) :
    (x ≫ cellMap i u neg pos) * g =
      mkCellPoint Z (negCoord x) (splitTorus.pointsEquiv I Z (torusCoord x)) z ≫
        cellMap i u neg pos := by
  have ht : torusCoord (mkCellPoint Z (negCoord x)
      (splitTorus.pointsEquiv I Z (torusCoord x)) z) = torusCoord x :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
    posCoord_mkCellPoint, ht, mul_assoc, h]

/-- The family `u` extended by one further parametrization `v`, indexed by `Option J`. -/
def extendFamily (v : Ga R ⟶ G) (u : J → (Ga R ⟶ G)) : Option J → (Ga R ⟶ G) :=
  fun o => o.elim v u

/-- The characters `ch` extended by one further character `χ`, indexed by `Option J`. -/
def extendChar (χ : I → ℤ) (ch : J → I → ℤ) : Option J → I → ℤ :=
  fun o => o.elim χ ch

@[simp] theorem extendFamily_none (v : Ga R ⟶ G) (u : J → (Ga R ⟶ G)) :
    extendFamily v u none = v := rfl

@[simp] theorem extendFamily_some (v : Ga R ⟶ G) (u : J → (Ga R ⟶ G)) (α : J) :
    extendFamily v u (some α) = u α := rfl

theorem orderedProduct_extendFamily_some (v : Ga R ⟶ G) (u : J → (Ga R ⟶ G)) {r : ℕ}
    (e : Fin r → J) (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    orderedProduct (extendFamily v u) (fun k => some (e k)) Z c = orderedProduct u e Z c := by
  simp only [orderedProduct, extendFamily_some]

theorem cellMap_extendFamily_some (v : Ga R ⟶ G) (u : J → (Ga R ⟶ G)) :
    cellMap i (extendFamily v u) (fun k => some (neg k)) (fun k => some (pos k)) =
      cellMap i u neg pos := by
  simp only [cellMap, cellPoint, orderedProduct_extendFamily_some]

/-- **Right translation of the positive cell factor by a further equivariant root point.** Let
`v` be a parametrization on which the torus acts through a character `χ` pairing positively
with `ν`. Over a local test ring, the product of the positive cell factors followed by a point
of `v` is again a product of the positive cell factors. -/
theorem exists_orderedProduct_mul_rootPoint_eq_pos_of_equivariant
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {v : Ga R ⟶ G} {χ : I → ℤ}
    (hv : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      (t ≫ i.hom.hom) * rootPoint v Z c * (t ≫ i.hom.hom)⁻¹ =
        rootPoint v Z (torusChar χ Z t * c))
    (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) (hχ : 0 < coPairing χ ν)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (w : Fin n → Γ((Over.mk s).left, ⊤)) (a : Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u pos (Over.mk s) w * rootPoint v (Over.mk s) a =
        orderedProduct u pos (Over.mk s) z := by
  have hu₂ : TorusEquivariant i (extendChar χ ch) (extendFamily v u) := by
    rintro (_ | α) Z t c
    · exact hv Z t c
    · exact hu α Z t c
  have : IsOpenImmersion
      (cellMap i (extendFamily v u) (fun k => some (neg k)) (fun k => some (pos k))).left := by
    rw [cellMap_extendFamily_some]
    infer_instance
  obtain ⟨z, hz⟩ := exists_orderedProduct_mul_rootPoint_eq_pos (α := none)
    (neg := fun k => some (neg k)) (pos := fun k => some (pos k)) hu₂ ν
    (fun k => hneg k) (fun k => hpos k) hχ s w a
  rw [orderedProduct_extendFamily_some, orderedProduct_extendFamily_some,
    extendFamily_none] at hz
  exact ⟨z, hz⟩

variable {H : GroupScheme (Spec (CommRingCat.of R))}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u' : J → (Ga R ⟶ H)}

/-- **Transfer of cell relations through positive-factor laws.** Under the hypotheses of
`exists_orderedProduct_mul_rootPoint_eq_pos_of_equivariant`, suppose every law
`(∏ₖ u_{pos k}(w k)) · v(c) = ∏ₖ u_{pos k}(z k)` of `G` over the local test ring also holds in
`H` for `u'` and `v'`. Then every relation `Ω(x) · v(c) = Ω(y)` between cell points of `G`
gives `Ω'(x) · v'(c) = Ω'(y)` in `H`. -/
theorem comp_cellMap_mul_rootPoint_transfer [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {v : Ga R ⟶ G} {v' : Ga R ⟶ H} {χ : I → ℤ}
    (hv : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      (t ≫ i.hom.hom) * rootPoint v Z c * (t ≫ i.hom.hom)⁻¹ =
        rootPoint v Z (torusChar χ Z t * c))
    (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) (hχ : 0 < coPairing χ ν)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk s ⟶ cellObj R I m n) (c : Γ((Over.mk s).left, ⊤))
    (hlaw : ∀ w z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u pos (Over.mk s) w * rootPoint v (Over.mk s) c =
          orderedProduct u pos (Over.mk s) z →
        orderedProduct u' pos (Over.mk s) w * rootPoint v' (Over.mk s) c =
          orderedProduct u' pos (Over.mk s) z)
    (hxy : (x ≫ cellMap i u neg pos) * rootPoint v (Over.mk s) c = y ≫ cellMap i u neg pos) :
    (x ≫ cellMap i' u' neg pos) * rootPoint v' (Over.mk s) c = y ≫ cellMap i' u' neg pos := by
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  obtain ⟨z, hz⟩ := exists_orderedProduct_mul_rootPoint_eq_pos_of_equivariant hu hv ν hneg hpos
    hχ s (posCoord x) c
  have hy : y = mkCellPoint (Over.mk s) (negCoord x)
      (splitTorus.pointsEquiv I _ (torusCoord x)) z := by
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [← hxy, comp_cellMap_mul_of_orderedProduct_mul x _ z hz]
  rw [hy]
  exact comp_cellMap_mul_of_orderedProduct_mul x _ z (hlaw _ _ hz)

end PositiveLaw

section WeylFamilies

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Laws of the positive cell factors of the Weyl families: over local test rings with
separably closed residue fields, right multiplication of the positive cell factor by a
simple-root point `u_a(c)` follows the same law in `G` and in `H`. -/
def PositiveLawRelations (b : P.Base) (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G))
    (u' : J → (Ga R ⟶ H)) {n : ℕ} (pos : Fin n → J) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (a : J), a ∈ b.support →
    ∀ (c : Γ((Over.mk s).left, ⊤)) (w z : Fin n → Γ((Over.mk s).left, ⊤)),
    orderedProduct (weylFamily P W u) pos (Over.mk s) w * rootPoint (u a) (Over.mk s) c =
        orderedProduct (weylFamily P W u) pos (Over.mk s) z →
      orderedProduct (weylFamily P W u') pos (Over.mk s) w * rootPoint (u' a) (Over.mk s) c =
        orderedProduct (weylFamily P W u') pos (Over.mk s) z

/-- The positive-factor laws give the simple-root relations of the Weyl families. -/
theorem simpleRootRelations_of_positiveLawRelations (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hL : PositiveLawRelations b W u u' (fun k => (pos k : J))) :
    SimpleRootRelations P
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) b u u' := by
  have hW := isRootParametrization_weylFamily hu hw W
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _ hW neg pos
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  intro A _ _ _ s x y a ha c hxy
  exact comp_cellMap_mul_rootPoint_transfer (ch := fun α => P.root α)
    (fun α Z t c => (hW α).equivariant Z t c) (fun Z t c => (hu a ha).equivariant Z t c) ν
    (fun k => hνneg _ (neg k).2) (fun k => hνpos _ (pos k).2)
    (hνpos _ (RootPairing.Base.isPos_of_mem_support ha)) s x y c
    (fun w z => hL A s a ha c w z) hxy

end WeylFamilies

end LocalSplitCell

open LocalSplitCell in
/-- Big-cell gluing over an arbitrary commutative ring from laws of the positive cell factors.
Let `G` and `H` be reductive with fibrewise maximal coordinate split tori `i`, `i'` carrying the
same fibrewise root datum `P`, and take Weyl-normalized simple-root data `u`, `u'` for a base
`b`. Suppose that, over local test rings with separably closed residue fields, every law
`(∏ₖ u_{pos k}(w k)) · u_a(c) = ∏ₖ u_{pos k}(z k)` of the positive cell factor of the Weyl family
of `G`, with `a` simple, also holds in `H`, and that right translation by the points `u_{-a}(-1)`
transfers relations between big-cell points. Then `G ≅ H` matching the two big-cell maps. -/
def LocalSplitPositiveLawIsomorphismStatement : Prop :=
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
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (a : J), a ∈ b.support →
        ∀ (c : Γ((Over.mk s).left, ⊤)) (w z : Fin n → Γ((Over.mk s).left, ⊤)),
        orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w *
            rootPoint (u a) (Over.mk s) c =
          orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) z →
        orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w *
            rootPoint (u' a) (Over.mk s) c =
          orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) z) →
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

/-- Laws of the positive cell factors and the negative simple relations suffice for big-cell
gluing of the Weyl families. -/
theorem localSplitPositiveLawIsomorphism : LocalSplitPositiveLawIsomorphismStatement.{u} := by
  intro R _ I _ _ J G H _ _ hG hH i i' hmax hmax' P hP hP' b W u u' hu hw hu' hw' m n neg pos
    hL hN
  exact localSplitSimpleRootRelationIsomorphism R I J G H hG hH i i' hmax hmax' P hP hP' b W u u'
    hu hw hu' hw' m n neg pos
    (LocalSplitCell.simpleRootRelations_of_positiveLawRelations hG hmax hP W hu hw neg pos hL) hN

end Langlands.GroupScheme
