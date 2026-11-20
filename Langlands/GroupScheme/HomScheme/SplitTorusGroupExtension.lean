import Langlands.GroupScheme.HomScheme.DiagonalizableTorsionCoordinates
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFlat
import Langlands.GroupScheme.SchematicHomEquality
import Langlands.GroupScheme.HomScheme.AffineTest

/-! # Descent of split-torus homomorphisms from torsion restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

variable {S V : Scheme.{u}} (b : V ⟶ S)
  [IsSchemeTheoreticallyDominant b] [QuasiCompact b]

private theorem pullback_map_injective {X Y : Over S} [Flat X.hom] [IsSeparated Y.hom]
    {g h : X ⟶ Y} (e : (Over.pullback b).map g = (Over.pullback b).map h) : g = h := by
  apply SchematicHomEquality.over_hom_ext g h (pullback.fst X.hom b)
  simpa only [Over.pullback_map_left, pullback.lift_fst] using
    congrArg (fun a => a.left ≫ pullback.fst Y.hom b) e

set_option backward.isDefEq.respectTransparency false in
private theorem isMonHom_of_pullback {H G : GroupScheme S}
    [Flat H.X.hom] [IsSeparated G.X.hom] (g : H.X ⟶ G.X)
    [IsMonHom ((Over.pullback b).map g)] : IsMonHom g where
  one_hom := by
    let : Flat (𝟙_ (Over S)).hom := by
      change Flat (𝟙 S)
      infer_instance
    apply pullback_map_injective b
    rw [Functor.map_comp]
    apply (cancel_epi (Functor.LaxMonoidal.ε (Over.pullback b))).mp
    rw [← Functor.obj.η_def_assoc, ← Functor.obj.η_def]
    exact IsMonHom.one_hom _
  mul_hom := by
    let : Flat (H.X ⊗ H.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    apply pullback_map_injective b
    rw [Functor.map_comp, Functor.map_comp]
    apply (cancel_epi (Functor.LaxMonoidal.μ (Over.pullback b) H.X H.X)).mp
    rw [← Functor.obj.μ_def_assoc, ← Functor.LaxMonoidal.μ_natural_assoc,
      ← Functor.obj.μ_def]
    exact IsMonHom.mul_hom _

set_option backward.isDefEq.respectTransparency false in
/-- A scheme map over the base is a group-scheme homomorphism if it is one after
quasi-compact schematically dominant base change, for flat source and separated target. -/
theorem existsUnique_hom_of_pullback_schemeMap {H G : GroupScheme S}
    [Flat H.X.hom] [IsSeparated G.X.hom]
    (f : (baseChange b).obj H ⟶ (baseChange b).obj G) (g : H.X ⟶ G.X)
    (hg : (Over.pullback b).map g = f.hom.hom) : ∃! h : H ⟶ G, (baseChange b).map h = f := by
  let : IsMonHom ((Over.pullback b).map g) := hg.symm ▸ f.hom.isMonHom_hom
  let : IsMonHom g := isMonHom_of_pullback b g
  refine ⟨Grp.homMk g, Grp.hom_ext _ _ hg, ?_⟩
  intro h hh
  exact SchematicHomEquality.baseChange_hom_ext b (hh.trans (Grp.hom_ext _ _ hg).symm)

namespace Diagonalizable

open TorsionDensity

variable {R K : Type u} [CommRing R] [CommRing K]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In diagonalizable coordinates a base-changed homomorphism projects to the
original homomorphism composed with the coefficient projection. -/
@[reassoc]
theorem baseChangeMap_project {M : Type u} [AddCommGroup M] (φ : R →+* K)
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (g : (groupScheme (CommRingCat.of R) M).toGrp ⟶ G) :
    ((baseChangeIso (Spec.map (CommRingCat.ofHom φ)) M).inv ≫
      (baseChange (Spec.map (CommRingCat.ofHom φ))).map g).hom.hom.left ≫
        pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom φ)) =
      coefficientProjection M φ ≫ g.hom.hom.left := by
  rw [Grp.comp_hom_hom, Over.comp_left, Category.assoc, HomScheme.baseChange_map_left_fst,
    ← Category.assoc, baseChangeIso_inv_fst]

/-- Write the split-torus torsion inclusion in diagonalizable coordinates on its source. -/
abbrev splitTorsionRestriction (A : CommRingCat.{u}) (L : Type u) [Fintype L] (n : ℕ) :=
  restrictMap A (QuotientAddGroup.mk' (multiples (L → ℤ) n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Given compatible lifts on an unbounded set of torsion orders, an actual
split-torus homomorphism over injectively extended coefficients descends to
an affine group scheme over the original ring. -/
theorem existsUnique_baseChange_hom_of_torsion_lifts (L : Type u) [Fintype L]
    (φ : R →+* K) (hφ : Function.Injective φ)
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (f : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj
      (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp ⟶
        (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)
    (P : ℕ → Prop) (hP : ∀ m : ℕ, ∃ n, P n ∧ m < n)
    (ht : ∀ n, P n →
      ∃ g : (groupScheme (CommRingCat.of R) ((L → ℤ) ⧸ multiples (L → ℤ) n)).toGrp ⟶ G,
        (baseChange (Spec.map (CommRingCat.ofHom φ))).map g =
        (baseChange (Spec.map (CommRingCat.ofHom φ))).map
          (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f) :
    ∃! g : (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp ⟶ G,
      (baseChange (Spec.map (CommRingCat.ofHom φ))).map g = f := by
  let A := CommRingCat.of R
  let B := CommRingCat.of K
  let b := Spec.map (CommRingCat.ofHom φ)
  let H := (groupScheme A (L → ℤ)).toGrp
  let e := baseChangeIso b (L → ℤ)
  let f' := (e.inv ≫ f).hom.hom.left ≫ pullback.fst G.X.hom b
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have htor (n : ℕ) (hn : P n) :
      ∃ g : Spec (CommRingCat.of (AddMonoidAlgebra R ((L → ℤ) ⧸ multiples (L → ℤ) n))) ⟶
          G.X.left,
        coefficientProjection _ φ ≫ g = torsionProjection L K n ≫ f' := by
    obtain ⟨g, hg⟩ := ht n hn
    let d := baseChangeIso b ((L → ℤ) ⧸ multiples (L → ℤ) n)
    have hcomp : d.inv ≫ (baseChange b).map (splitTorsionRestriction A L n) =
        splitTorsionRestriction B L n ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, baseChangeIso_restrictMap, Iso.inv_hom_id_assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine ⟨g.hom.hom.left, ?_⟩
    rw [← baseChangeMap_project φ g, hg, ← Category.assoc, hcomp, Category.assoc,
      Grp.comp_hom_hom, Over.comp_left, Category.assoc, splitTorsionRestriction, restrictMap_left]
    rfl
  obtain ⟨g, hg, _⟩ := existsUnique_hom_of_torsion_coefficients L φ hφ f' P hP htor
  have hb : IsSchemeTheoreticallyDominant b := isSchemeTheoreticallyDominant_specMap hφ
  have hc : IsSchemeTheoreticallyDominant (coefficientProjection (L → ℤ) φ) :=
    isSchemeTheoreticallyDominant_specMap (AddMonoidAlgebra.map_injective _ hφ)
  let g' : H.X ⟶ G.X := Over.homMk g (by
    apply ext_of_isSchemeTheoreticallyDominant (terminal.from (Spec A))
      (terminal.hom_ext _ _) (coefficientProjection (L → ℤ) φ)
    rw [← Category.assoc, hg]
    dsimp only [f']
    have hw := Over.w (e.inv ≫ f).hom.hom
    change (e.inv ≫ f).hom.hom.left ≫ pullback.snd G.X.hom b = (groupScheme B (L → ℤ)).X.hom at hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact (Over.w (coefficientProjectionOver (L → ℤ) φ)).symm)
  apply existsUnique_hom_of_pullback_schemeMap b f g'
  let f₀ : (Over.pullback b).obj H.X ⟶ (Over.pullback b).obj G.X := f.hom.hom
  change (Over.pullback b).map g' = f₀
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hproj : ((Over.pullback b).map g').left ≫ pullback.fst G.X.hom b =
        pullback.fst H.X.hom b ≫ g'.left := pullback.lift_fst _ _ _
    rw [hproj]
    apply (cancel_epi e.inv.hom.hom.left).mp
    rw [← Category.assoc, baseChangeIso_inv_fst]
    simp only [f', Grp.comp_hom_hom, Over.comp_left, Category.assoc] at hg
    exact hg
  · exact (Over.w ((Over.pullback b).map g')).trans (Over.w f₀).symm

end Diagonalizable

end Langlands.GroupScheme
