import Langlands.GroupScheme.Torus.TorsionDetermination.Assembly
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Reduction of the torsion-closed immersion lemma to diagonalizable groups over rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorsionDetermination

open RelativeMultiplicativeType

variable {S : Scheme.{u}}

/-- If every torsion-closed immersion into `D` is an isomorphism and `D ≅ G`, then the
identity point of `G` lifts through every torsion-closed immersion into `G`. -/
theorem lifts_id_of_iso {G D : GroupScheme S} (e : D ≅ G) {Z : Scheme.{u}} (j : Z ⟶ G.X.left)
    [IsImmersion j] (hj : IsTorsionClosed G j)
    (hD : ∀ (Z' : Scheme.{u}) (j' : Z' ⟶ D.X.left), IsImmersion j' →
      IsTorsionClosed D j' → IsIso j') :
    PointLifts j (𝟙 G.X) := by
  apply lifts_id_of_pullback_iso j e
  have := hD _ (pullback.snd j e.hom.hom.hom.left) inferInstance
    (IsTorsionClosed.pullback e.hom j hj)
  exact lifts_id_of_isIso _

/-- The split affine case of the torsion-closed immersion lemma: every torsion-closed immersion
into the diagonalizable group `D_{Spec R}(Λ)` of a finitely generated abelian group `Λ` over an
affine scheme is an isomorphism. -/
abbrev SplitAffineCase : Prop :=
  ∀ (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ], AddGroup.FG Λ →
    ∀ (Z : Scheme.{u}) (j : Z ⟶ (diagonalizable (Spec R) Λ).X.left), IsImmersion j →
      IsTorsionClosed (diagonalizable (Spec R) Λ) j → IsIso j

/-- A torsion-closed immersion into a group isomorphic to `D` is an isomorphism once every
torsion-closed immersion into `D` is. -/
theorem isIso_of_iso {G D : GroupScheme S} (e : D ≅ G) {Z : Scheme.{u}} (j : Z ⟶ G.X.left)
    [IsImmersion j] (hj : IsTorsionClosed G j)
    (hD : ∀ (Z' : Scheme.{u}) (j' : Z' ⟶ D.X.left), IsImmersion j' →
      IsTorsionClosed D j' → IsIso j') :
    IsIso j :=
  isIso_of_lifts_id j (lifts_id_of_iso e j hj hD)

/-- The core case of the torsion-closed immersion lemma, in the form proved for the affine
group-algebra model `D(Λ) = Spec R[Λ]` over `Spec R`: a morphism `i : Z ⟶ D(Λ)` over `Spec R`
whose underlying morphism is an immersion, whose lifting points are closed under
multiplication, and through which every torsion point lifts, is an isomorphism on
underlying schemes. -/
abbrev DiagonalizableCoreCase : Prop :=
  ∀ (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] (Z : Over (Spec R))
    (i : Z ⟶ (Diagonalizable.groupScheme R Λ).X), IsImmersion i.left →
    (∀ (T : Over (Spec R)) (x y : T ⟶ (Diagonalizable.groupScheme R Λ).X),
      (∃ a, a ≫ i = x) → (∃ b, b ≫ i = y) → ∃ c, c ≫ i = x * y) →
    (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec R)) (x : T ⟶ (Diagonalizable.groupScheme R Λ).X),
      x ^ n = 1 → ∃ a, a ≫ i = x) →
    IsIso i.left

/-- For a morphism of schemes `j : Z ⟶ X.left`, viewing `Z` over `S` through `j`, a point
lifts through `j` exactly when it factors through the induced morphism over `S`. -/
theorem lifts_iff_exists_overHom {X : Over S} {Z : Scheme.{u}} (j : Z ⟶ X.left) {T : Over S}
    (x : T ⟶ X) : PointLifts j x ↔ ∃ a : T ⟶ Over.mk (j ≫ X.hom), a ≫ Over.homMk j rfl = x := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Over.homMk a ?_, ?_⟩
    · simp only [Over.mk_hom]
      rw [← Category.assoc, ha, Over.w x]
    · ext1
      simpa using ha
  · rintro ⟨a, ha⟩
    exact ⟨a.left, by rw [← ha]; rfl⟩

/-- The core case, restated for torsion-closed immersions into `D(Λ)`. -/
theorem isIso_of_diagonalizableCoreCase (hC : DiagonalizableCoreCase.{u}) (R : CommRingCat.{u})
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] (Z : Scheme.{u})
    (j : Z ⟶ (Diagonalizable.groupScheme R Λ).toGrp.X.left) (hj : IsImmersion j)
    (htc : IsTorsionClosed (Diagonalizable.groupScheme R Λ).toGrp j) : IsIso j :=
  hC R Λ (Over.mk (j ≫ (Diagonalizable.groupScheme R Λ).X.hom)) (Over.homMk j rfl) hj
    (fun _ x y hx hy => (lifts_iff_exists_overHom j _).1
      (htc.mul x y ((lifts_iff_exists_overHom j x).2 hx) ((lifts_iff_exists_overHom j y).2 hy)))
    (fun n hn _ x hx => (lifts_iff_exists_overHom j x).1 (htc.torsion n hn x hx))

/-- The core case for the group-algebra model implies the split affine case. -/
theorem splitAffineCase_of_diagonalizableCoreCase (hC : DiagonalizableCoreCase.{u}) :
    SplitAffineCase.{u} := by
  intro R Λ _ hΛ Z j hj htc
  have : AddGroup.FG Λ := hΛ
  exact isIso_of_iso (Diagonalizable.relativeModelIso R Λ) j htc
    (isIso_of_diagonalizableCoreCase hC R Λ)

/-- **Descent of the torsion-closed immersion lemma.** Let `𝒰` be an fppf cover of `S` such
that over each member the base change of `G` is isomorphic to a group `D i` for which every
torsion-closed immersion is an isomorphism. Then every torsion-closed immersion into `G` is an
isomorphism. -/
theorem isIso_of_cover {G : GroupScheme S}
    (𝒰 : S.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
    (D : ∀ i, GroupScheme (𝒰.X i)) (e : ∀ i, D i ≅ (GroupScheme.baseChange (𝒰.f i)).obj G)
    (hD : ∀ i (Z' : Scheme.{u}) (j' : Z' ⟶ (D i).X.left), IsImmersion j' →
      IsTorsionClosed (D i) j' → IsIso j')
    {Z : Scheme.{u}} (j : Z ⟶ G.X.left) [IsImmersion j] (htc : IsTorsionClosed G j) :
    IsIso j := by
  apply isIso_of_lifts_id
  exact lifts_id_of_cover _ j 𝒰 fun i =>
    lifts_id_of_iso (e i) _ (htc.baseChange (𝒰.f i) _ _) (hD i)

/-- The split affine case implies the split case over an arbitrary base scheme, by Zariski
descent along the affine open cover. -/
theorem diagonalizable_case (hC : SplitAffineCase.{u}) (S : Scheme.{u}) (Λ : Type u)
    [AddCommGroup Λ] (hΛ : AddGroup.FG Λ) (Z : Scheme.{u}) (j : Z ⟶ (diagonalizable S Λ).X.left)
    (hj : IsImmersion j) (htc : IsTorsionClosed (diagonalizable S Λ) j) : IsIso j := by
  let 𝒜 := S.affineOpenCover
  let 𝒰 : S.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) :=
    𝒜.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      fun _ => ⟨inferInstance, inferInstance⟩
  exact isIso_of_cover 𝒰 (fun i => diagonalizable (Spec (𝒜.X i)) Λ)
    (fun i => (diagonalizableBaseChangeIso (S' := Spec (𝒜.X i)) (𝒜.f i) Λ).symm)
    (fun i => hC (𝒜.X i) Λ hΛ) j htc

/-- **Reduction to the split affine case.** If every torsion-closed immersion into a split
diagonalizable group over an affine scheme is an isomorphism, then every torsion-closed
immersion into a group of multiplicative type is an isomorphism. -/
theorem torsionClosedImmersionIsIso_of_splitAffineCase (hC : SplitAffineCase.{u}) :
    TorsionClosedImmersionIsIso.{u} := by
  intro S G hG Z j hj htc
  obtain ⟨𝒰, h𝒰⟩ := hG
  choose Λ _ hΛ e using h𝒰
  exact isIso_of_cover 𝒰 (fun i => diagonalizable (𝒰.X i) (Λ i)) (fun i => (e i).some.symm)
    (fun i => diagonalizable_case hC (𝒰.X i) (Λ i) (hΛ i)) j htc

/-- **The target statement from the core case.** SGA 3 IX 4.8–4.9 follow from the core case
for the affine group-algebra models `D(Λ) = Spec R[Λ]`. -/
theorem statement_of_diagonalizableCoreCase (hC : DiagonalizableCoreCase.{u}) :
    MultiplicativeTypeTorsionDeterminationStatement.{u} :=
  statement_of_torsionClosedImmersionIsIso
    (torsionClosedImmersionIsIso_of_splitAffineCase (splitAffineCase_of_diagonalizableCoreCase hC))

end Langlands.GroupScheme.TorsionDetermination
