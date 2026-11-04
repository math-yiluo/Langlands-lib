import Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement
import Langlands.GroupScheme.AutomorphicAction.SectionCoordinateModel
import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.GeneralLinearAffineCoordinates
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.LinearAlgebra.FiniteFamilyBasis

/-! # Existence of an affine finite-type cocycle model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelProof

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PolynomialSpecPoints
  SectionCoordinateModel _root_.Langlands.GroupScheme.GeneralLinear

instance finite_coordinate (n : Type) [Finite n] : Finite (Coordinate n) :=
  Finite.of_surjective
    (fun p : (n × n) ⊕ (n × n) =>
      Sum.elim (fun q => Coordinate.entry q.1 q.2) (fun q => Coordinate.inverseEntry q.1 q.2) p)
    (by
      rintro (⟨i, j⟩ | ⟨i, j⟩)
      · exact ⟨Sum.inl (i, j), rfl⟩
      · exact ⟨Sum.inr (i, j), rfl⟩)

section Model

variable {S : Scheme.{u}} {H G : GroupScheme S} {a : AutomorphicAction H G}

/-- The conjugation action on a represented family of cocycles that is injective and
closed under conjugation, as the morphism representing conjugation of the universal
family by the first factor. -/
def conjugationHom {Z : Over S} (U : a.Cocycle Z)
    (hconj : ∀ (T : Over S) (g : T ⟶ G.X) (x : T ⟶ Z),
      ∃ x' : T ⟶ Z, Cocycle.restrict x' U = Cocycle.conjugate g (Cocycle.restrict x U)) :
    G.X ⊗ Z ⟶ Z :=
  Classical.choose (hconj (G.X ⊗ Z) (fst G.X Z) (snd G.X Z))

theorem restrict_lift_conjugationHom {Z : Over S} (U : a.Cocycle Z)
    (hconj : ∀ (T : Over S) (g : T ⟶ G.X) (x : T ⟶ Z),
      ∃ x' : T ⟶ Z, Cocycle.restrict x' U = Cocycle.conjugate g (Cocycle.restrict x U))
    {T : Over S} (g : T ⟶ G.X) (x : T ⟶ Z) :
    Cocycle.restrict (lift g x ≫ conjugationHom U hconj) U =
      Cocycle.conjugate g (Cocycle.restrict x U) := by
  have h := Classical.choose_spec (hconj (G.X ⊗ Z) (fst G.X Z) (snd G.X Z))
  rw [Cocycle.restrict_comp, conjugationHom, h, Cocycle.restrict_conjugate, lift_fst,
    ← Cocycle.restrict_comp, lift_snd]

/-- A represented family of cocycles that is injective on every test scheme, closed
under conjugation and contains the trivial cocycle is a cocycle model. -/
def modelOfConjugate {Z : Over S} (U : a.Cocycle Z)
    (hinj : ∀ T : Over S, Function.Injective (fun x : T ⟶ Z => Cocycle.restrict x U))
    (hconj : ∀ (T : Over S) (g : T ⟶ G.X) (x : T ⟶ Z),
      ∃ x' : T ⟶ Z, Cocycle.restrict x' U = Cocycle.conjugate g (Cocycle.restrict x U))
    (x₀ : 𝟙_ (Over S) ⟶ Z) (hx₀ : Cocycle.restrict x₀ U = Cocycle.trivial (𝟙_ (Over S))) :
    a.CocycleModel where
  scheme := Z
  universal := U
  injective := hinj
  action := schemeActionOfPointLaws (conjugationHom U hconj)
    (fun {T} x => hinj T (by
      simp only [restrict_lift_conjugationHom, Cocycle.conjugate_one]))
    (fun {T} h h' x => hinj T (by
      simp only [restrict_lift_conjugationHom, Cocycle.conjugate_mul]))
  equivariant g x := restrict_lift_conjugationHom U hconj g x
  basepoint := x₀
  basepoint_trivial := hx₀

end Model

section Embedding

variable {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a : AutomorphicAction H G) {N : ℕ} (ρ : MatrixRepresentation a.semidirectProduct (Fin N))

set_option backward.isDefEq.respectTransparency.types false in
theorem locallyOfFiniteType_tensor (X Y : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := by
  change LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom)
  have hfst : LocallyOfFiniteType (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFiniteType) _ _ inferInstance
  infer_instance

/-- A morphism to `G × H`, regarded as a point of the semidirect product. -/
abbrev toSemidirect {V : Over (Spec (CommRingCat.of k))} (f : V ⟶ G.X ⊗ H.X) :
    V ⟶ a.semidirectProduct.X :=
  f

/-- The semidirect product embedded into the affine space of matrix coordinates. -/
def embedding : G.X ⊗ H.X ⟶ space (CommRingCat.of k) (Coordinate (Fin N)) :=
  ρ.hom.hom ≫ toSpace (Fin N) (CommRingCat.of k)

/-- The coordinates of a point of the semidirect product in the affine space are the
entries of its matrix and of the inverse matrix. -/
theorem coord_embedding {V : Over (Spec (CommRingCat.of k))} (w : V ⟶ G.X ⊗ H.X)
    (κ : Coordinate (Fin N)) :
    coord (w ≫ embedding a ρ) κ = values (ρ.pointMatrix V (toSemidirect a w)) κ := by
  rw [ρ.pointMatrix_apply, ← toSpace_appTop, Category.assoc]
  rfl

/-- The closed embedding of `G × H` into `H × 𝔸^C` over `H`. -/
def graph : G.X ⊗ H.X ⟶ H.X ⊗ space (CommRingCat.of k) (Coordinate (Fin N)) :=
  lift (snd G.X H.X) (embedding a ρ)

theorem graph_fst : graph a ρ ≫ fst _ _ = snd G.X H.X :=
  lift_fst _ _

theorem isClosedImmersion_graph [IsAffineHom H.X.hom] (hρ : IsClosedSubgroup ρ) :
    IsClosedImmersion (graph a ρ).left := by
  have : IsSeparated H.X.hom := IsSeparated.of_isAffineHom H.X.hom
  have hsep : IsSeparated (snd H.X (space (CommRingCat.of k) (Coordinate (Fin N)))).left := by
    change IsSeparated (pullback.snd H.X.hom (space (CommRingCat.of k) (Coordinate (Fin N))).hom)
    infer_instance
  have hφ : IsClosedImmersion (embedding a ρ).left := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    change IsClosedImmersion (ρ.hom.hom.left ≫ (toSpace (Fin N) (CommRingCat.of k)).left)
    infer_instance
  have hcomp : IsClosedImmersion ((graph a ρ).left ≫
      (snd H.X (space (CommRingCat.of k) (Coordinate (Fin N)))).left) := by
    rw [← Over.comp_left, graph, lift_snd]
    exact hφ
  exact @IsClosedImmersion.of_comp _ _ _ _ _ hcomp hsep

/-- The section of a conjugate cocycle is the conjugate section in the semidirect
product. -/
theorem sec_conjugate {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (c : a.Cocycle T) :
    toSemidirect a (sec (Cocycle.conjugate g c)) =
      ((snd H.X T ≫ g) ≫ a.semidirectInl.hom.hom) * toSemidirect a (sec c) *
        ((snd H.X T ≫ g) ≫ a.semidirectInl.hom.hom)⁻¹ := by
  have hc : ∀ c : a.Cocycle T, toSemidirect a (sec c) ≫ fst G.X H.X =
      c.eval (snd H.X T) (fst H.X T) := fun c => lift_fst _ _
  have hs : ∀ c : a.Cocycle T, toSemidirect a (sec c) ≫ snd G.X H.X = fst H.X T :=
    fun c => lift_snd _ _
  apply (a.semidirectPointsEquiv _).injective
  rw [map_mul, map_mul, map_inv, semidirectInl_points]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      semidirectPointsEquiv_left, semidirectPointsEquiv_right, inv_one, map_one,
      MulAut.one_apply, one_mul, pointsAction_apply]
    rw [hc, hc, hs]
    exact Cocycle.eval_conjugate g c (snd H.X T) (fst H.X T)
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, semidirectPointsEquiv_right, inv_one, one_mul, mul_one]
    rw [hs, hs]

variable {m : ℕ} (e : Fin m → Γ(H.X.left, ⊤)) {Z : Over (Spec (CommRingCat.of k))}
  (i : Z ⟶ space (CommRingCat.of k) (Coordinate (Fin N) × Fin m)) (U : a.Cocycle Z)

/-- Conjugation preserves the cocycles whose sections have coordinates linear in `e`:
the coordinates of the conjugate are obtained by conjugating the coefficient matrices. -/
theorem exists_conjugate
    (hreal : ∀ (T : Over (Spec (CommRingCat.of k)))
        (y : T ⟶ space (CommRingCat.of k) (Coordinate (Fin N) × Fin m)) (c : a.Cocycle T),
        (∃ x : T ⟶ Z, x ≫ i = y ∧ Cocycle.restrict x U = c) ↔
          (H.X ◁ y) ≫ lift (fst _ _) (Φ H.X (Coordinate (Fin N)) e) = sec c ≫ graph a ρ)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ Z) :
    ∃ x' : T ⟶ Z, Cocycle.restrict x' U = Cocycle.conjugate g (Cocycle.restrict x U) := by
  let UT := ρ.pointMatrix T (g ≫ a.semidirectInl.hom.hom)
  let y' : T ⟶ space (CommRingCat.of k) (Coordinate (Fin N) × Fin m) :=
    PolynomialSpecPoints.mk fun p => conjCoords UT (fun κ => coord (x ≫ i) (κ, p.2)) p.1
  have h₀ := (hreal T (x ≫ i) (Cocycle.restrict x U)).mp ⟨x, rfl, rfl⟩
  have h₀snd : (H.X ◁ (x ≫ i)) ≫ Φ H.X (Coordinate (Fin N)) e =
      sec (Cocycle.restrict x U) ≫ embedding a ρ := by
    have := congrArg (· ≫ snd _ _) h₀
    simpa only [Category.assoc, lift_snd, graph] using this
  have hQ : values (ρ.pointMatrix _ (toSemidirect a (sec (Cocycle.restrict x U)))) =
      fun κ => ∑ l, (fst H.X T).left.appTop (e l) *
        (snd H.X T).left.appTop (coord (x ≫ i) (κ, l)) := by
    funext κ
    rw [← coord_embedding, ← h₀snd, coord_whiskerLeft_Φ]
  obtain ⟨x', -, hx'⟩ := (hreal T y' (Cocycle.conjugate g (Cocycle.restrict x U))).mpr (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst, graph, secHom_snd]
    · simp only [Category.assoc, lift_snd, graph]
      apply PolynomialSpecPoints.ext
      intro κ
      rw [coord_whiskerLeft_Φ, coord_embedding, sec_conjugate, map_mul, map_mul, map_inv,
        values_conj, hQ, conjCoords_sum_mul, Category.assoc, ρ.pointMatrix_naturality]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      rw [coord_mk]
      exact (congrFun (conjCoords_map (snd H.X T).left.appTop.hom UT
        (fun κ => coord (x ≫ i) (κ, l))) κ).symm)
  exact ⟨x', hx'⟩

/-- The section of the trivial cocycle is the pullback of the canonical section of `H`. -/
theorem sec_trivial (T : Over (Spec (CommRingCat.of k))) :
    sec (Cocycle.trivial T : a.Cocycle T) = fst H.X T ≫ lift (1 : H.X ⟶ G.X) (𝟙 H.X) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [secHom, lift_fst, Category.assoc, Cocycle.trivial, MonObj.comp_one]
  · simp only [secHom_snd, Category.assoc, lift_snd, Category.comp_id]

/-- The trivial cocycle has constant coordinates, given by the coefficients of the
coordinates of the canonical section along `e`. -/
theorem exists_trivial
    (hreal : ∀ (T : Over (Spec (CommRingCat.of k)))
        (y : T ⟶ space (CommRingCat.of k) (Coordinate (Fin N) × Fin m)) (c : a.Cocycle T),
        (∃ x : T ⟶ Z, x ≫ i = y ∧ Cocycle.restrict x U = c) ↔
          (H.X ◁ y) ≫ lift (fst _ _) (Φ H.X (Coordinate (Fin N)) e) = sec c ≫ graph a ρ)
    (r : Coordinate (Fin N) → Fin m → k)
    (hw : ∀ κ, coord (lift (1 : H.X ⟶ G.X) (𝟙 H.X) ≫ embedding a ρ) κ =
      ∑ l, (H.X.hom.appLE ⊤ ⊤ le_top) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (r κ l)) *
        e l) :
    ∃ x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z,
      Cocycle.restrict x₀ U = Cocycle.trivial (𝟙_ (Over (Spec (CommRingCat.of k)))) := by
  let I := 𝟙_ (Over (Spec (CommRingCat.of k)))
  let y₀ : I ⟶ space (CommRingCat.of k) (Coordinate (Fin N) × Fin m) :=
    PolynomialSpecPoints.mk fun p => I.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (r p.1 p.2))
  have hconst : ∀ q : Γ(Spec (CommRingCat.of k), ⊤),
      (fst H.X I).left.appTop ((H.X.hom.appLE ⊤ ⊤ le_top) q) =
        (snd H.X I).left.appTop (I.hom.appTop q) := by
    intro q
    have h₁ : H.X.hom.appLE ⊤ ⊤ le_top = H.X.hom.appTop := Scheme.Hom.appLE_eq_app _ (U := ⊤)
    rw [h₁]
    change ((fst H.X I).left ≫ H.X.hom).appTop q = ((snd H.X I).left ≫ I.hom).appTop q
    rw [Over.w (fst H.X I), Over.w (snd H.X I)]
  obtain ⟨x₀, -, hx₀⟩ := (hreal I y₀ (Cocycle.trivial I)).mpr (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst, graph, secHom_snd]
    · simp only [Category.assoc, lift_snd, graph]
      apply PolynomialSpecPoints.ext
      intro κ
      rw [coord_whiskerLeft_Φ, sec_trivial, Category.assoc, coord_comp, hw, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, mul_comm, coord_mk, hconst])
  exact ⟨x₀, hx₀⟩

end Embedding

/-- Every action of affine finite-type group schemes over a field has an affine
finite-type cocycle model. -/
theorem affineFiniteTypeCocycleModel : AffineFiniteTypeCocycleModelStatement.{u} := by
  intro k _ H G _ _ _ _ a
  have : LocallyOfFiniteType a.semidirectProduct.X.hom := locallyOfFiniteType_tensor G.X H.X
  obtain ⟨N, ρ, hρ⟩ :=
    affineLinearEmbeddingStatement k a.semidirectProduct inferInstance inferInstance
  let _ := Scheme.TwoAffineOpenCover.algebraOfHom H.X.hom ⊤
  obtain ⟨m, e, r, he, hw⟩ := Langlands.LinearAlgebra.exists_linearIndependent_sum_algebraMap_mul
    (k := k) (fun κ : Coordinate (Fin N) =>
      coord (lift (1 : H.X ⟶ G.X) (𝟙 H.X) ≫ embedding a ρ) κ)
  obtain ⟨Z, i, U, hi, hreal, hinj⟩ := exists_model (a := a) (Coordinate (Fin N)) m
    (graph a ρ) (isClosedImmersion_graph a ρ hρ) (graph_fst a ρ) e he
  obtain ⟨x₀, hx₀⟩ := exists_trivial a ρ e i U hreal r hw
  exact ⟨modelOfConjugate U hinj (exists_conjugate a ρ e i U hreal) x₀ hx₀,
    isAffineHom_of_isClosedImmersion i hi, locallyOfFiniteType_of_isClosedImmersion i hi⟩

end Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelProof
