import Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism
import Mathlib.AlgebraicGeometry.Stalk

/-! # Big-cell gluing from local algebra points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace CellGluing

/-- Local-ring-valued points detect equality of morphisms into an affine scheme. -/
theorem hom_ext_of_localRingPoints {X Y : Scheme.{u}} [IsAffine Y] {f g : X ⟶ Y}
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (x : Spec (CommRingCat.of A) ⟶ X), x ≫ f = x ≫ g) : f = g := by
  apply ext_of_isAffine
  ext a
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x hx
  have he := congrArg (· ≫ Y.toSpecΓ) (h (X.presheaf.stalk x) (X.fromSpecStalk x))
  simp only [Category.assoc, Scheme.toSpecΓ_naturality,
    Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp] at he
  exact congrArg (fun φ : Γ(Y, ⊤) ⟶ X.presheaf.stalk x => φ.hom a)
    (Spec.map_injective he)

/-- For an affine target, cell compatibility can be checked on spectra of
commutative local rings, including rings with nilpotents. -/
theorem cellCompatible_of_localRingPoints
    {S : Scheme.{u}} {G H : GroupScheme S} {C : Over S} [IsAffine H.X.left]
    (j : C ⟶ G.X) (ν : C ⟶ H.X)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (s : Spec (CommRingCat.of A) ⟶ S) (x y c : Over.mk s ⟶ C),
      (x ≫ j) * (y ≫ j) = c ≫ j → (x ≫ ν) * (y ≫ ν) = c ≫ ν) :
    CellCompatible j ν := by
  intro Z x y c hxy
  apply Over.OverMorphism.ext
  apply hom_ext_of_localRingPoints
  intro A _ _ q
  let s := q ≫ Z.hom
  let t : Over.mk s ⟶ Z := Over.homMk q rfl
  have ht := h A s (t ≫ x) (t ≫ y) (t ≫ c) (by
    simpa only [Category.assoc, ← MonObj.comp_mul] using congrArg (t ≫ ·) hxy)
  have ht' : t ≫ ((x ≫ ν) * (y ≫ ν)) = t ≫ (c ≫ ν) := by
    simpa only [Category.assoc, ← MonObj.comp_mul] using ht
  exact congrArg CommaMorphism.left ht'

end CellGluing

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Matching point-group comparisons over all commutative local rings glue to an
isomorphism agreeing with the common big-cell coordinates. -/
theorem exists_iso_of_localRingPoints (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)} {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hF : ∀ (A : Type u) [CommRing A] [IsLocalRing A]
      (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)),
      ∃ Ψ : (Over.mk s ⟶ G.X) ≃* (Over.mk s ⟶ H.X),
        (∀ t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
        ∀ α c, Ψ (rootPoint (u α) _ c) = rootPoint (u' α) _ c) :
    ∃ ψ : G ≅ H, cellMap i u neg pos ≫ ψ.hom.hom.hom = cellMap i' u' neg pos := by
  have := hG.isAffineHom
  have := hH.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have := hG.smooth
  have := hH.smooth
  have := hG.geometricallyIrreducible
  have := hH.geometricallyIrreducible
  have hc : CellGluing.CellCompatible (cellMap i u neg pos) (cellMap i' u' neg pos) := by
    apply CellGluing.cellCompatible_of_localRingPoints
    intro A _ _ s x y c h
    obtain ⟨Ψ, hi, hu⟩ := hF A s
    exact cellRelation_of_map Ψ.toMonoidHom hi hu neg pos x y c h
  have hc' : CellGluing.CellCompatible (cellMap i' u' neg pos) (cellMap i u neg pos) := by
    apply CellGluing.cellCompatible_of_localRingPoints
    intro A _ _ s x y c h
    obtain ⟨Ψ, hi, hu⟩ := hF A s
    refine cellRelation_of_map Ψ.symm.toMonoidHom (fun t => ?_) (fun α c => ?_) neg pos x y c h
    · exact Ψ.symm_apply_eq.mpr (hi t).symm
    · exact Ψ.symm_apply_eq.mpr (hu α c).symm
  exact CellGluing.exists_iso_of_cellCompatible (cellMap i u neg pos)
    (cellMap i' u' neg pos) (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)
    (cellUnit_comp_cellMap i' u' neg pos) hc hc'

/-- The same gluing criterion using only the canonical test objects for
commutative local `R`-algebras. Naturality of the point-group comparisons is not required. -/
theorem exists_iso_of_localAlgebraPoints (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)} {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i u neg pos).left] [IsOpenImmersion (cellMap i' u' neg pos).left]
    (hF : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A],
      ∃ Ψ : (fieldPoint R A ⟶ G.X) ≃* (fieldPoint R A ⟶ H.X),
        (∀ t : fieldPoint R A ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
        ∀ α c, Ψ (rootPoint (u α) _ c) = rootPoint (u' α) _ c) :
    ∃ ψ : G ≅ H, cellMap i u neg pos ≫ ψ.hom.hom.hom = cellMap i' u' neg pos := by
  apply exists_iso_of_localRingPoints (i := i) (i' := i') (u := u) (u' := u') hG hH neg pos
  intro A _ _ s
  let φ := Spec.preimage s
  let : Algebra R A := φ.hom.toAlgebra
  have hs : algebraBaseMap R A = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨Ψ₀, hi₀, hu₀⟩ := hF A
  let e : Over.mk s ≅ fieldPoint R A := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ algebraBaseMap R A = s
    rw [Category.id_comp, Category.id_comp, hs])
  refine ⟨((precompPointsEquiv e G).symm.trans Ψ₀).trans (precompPointsEquiv e H),
    fun t => ?_, fun α c => ?_⟩
  · change e.hom ≫ Ψ₀ (e.inv ≫ t ≫ i.hom.hom) = t ≫ i'.hom.hom
    rw [← Category.assoc, hi₀, ← Category.assoc, Iso.hom_inv_id_assoc]
  · change e.hom ≫ Ψ₀ (e.inv ≫ rootPoint (u α) _ c) = rootPoint (u' α) _ c
    rw [comp_rootPoint, hu₀, ← comp_rootPoint, Iso.hom_inv_id_assoc]


end LocalSplitCell

/-- Big-cell gluing over an arbitrary commutative ring from matching
point-group comparisons on every commutative local algebra. -/
def LocalSplitLocalAlgebraCellIsomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
      (u : J → (LocalSplitCell.Ga R ⟶ G)) (u' : J → (LocalSplitCell.Ga R ⟶ H))
      (m n : ℕ) (neg : Fin m → J) (pos : Fin n → J),
      IsOpenImmersion (LocalSplitCell.cellMap i u neg pos).left →
      IsOpenImmersion (LocalSplitCell.cellMap i' u' neg pos).left →
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A],
        ∃ Ψ : (LocalSplitCell.fieldPoint R A ⟶ G.X) ≃*
          (LocalSplitCell.fieldPoint R A ⟶ H.X),
          (∀ t : LocalSplitCell.fieldPoint R A ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
            Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
          ∀ α c, Ψ (LocalSplitCell.rootPoint (u α) _ c) =
            LocalSplitCell.rootPoint (u' α) _ c) →
      ∃ ψ : G ≅ H, LocalSplitCell.cellMap i u neg pos ≫ ψ.hom.hom.hom =
        LocalSplitCell.cellMap i' u' neg pos

/-- Local-algebra comparisons suffice for big-cell gluing without
reducedness, locality or naturality assumptions. -/
theorem localSplitLocalAlgebraCellIsomorphism :
    LocalSplitLocalAlgebraCellIsomorphismStatement.{u} := by
  intro R _ I _ J G H hG hH i i' u u' m n neg pos hj hν hF
  let := hj
  let := hν
  exact LocalSplitCell.exists_iso_of_localAlgebraPoints hG hH neg pos hF

end Langlands.GroupScheme
