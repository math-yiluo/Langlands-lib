import Langlands.GroupScheme.Rational.PointedFamilyScalarExtension
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Actual affine-line sources after field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

variable {B B' : Scheme.{u}}

/-- The actual affine-line comparison preserves its zero section. -/
theorem zeroSection_baseChange (b : B' ⟶ B) :
    Functor.LaxMonoidal.ε (Over.pullback b) ≫ (Over.pullback b).map (zeroSection B) =
      zeroSection B' ≫ (baseChangeIso b).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
      pullback.lift_fst]
    rw [show (baseChangeIso b).hom.left ≫ pullback.fst (scheme B).hom b =
        AffineSpace.map PUnit.{u + 1} b from
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) b).isoPullback_hom_fst]
    change (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
        pullback.fst (𝟙 B) b ≫
          AffineSpace.homOfVector (𝟙 B) (fun _ : PUnit.{u + 1} => 0) =
      AffineSpace.homOfVector (𝟙 B') (fun _ : PUnit.{u + 1} => 0) ≫
        AffineSpace.map PUnit.{u + 1} b
    apply AffineSpace.hom_ext
    · simp [Category.assoc, Over.ε_pullback_left,
        AffineSpace.homOfVector_over, AffineSpace.map_over]
    · intro i
      cases i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        map_zero]
  · exact (Over.w _).trans (Over.w _).symm

end AffineLine

namespace PointedCommutatorFamily

variable {B B' : Scheme.{u}}

/-- Change only the initial source, retaining all group parameters. -/
def sourceCongr (G : GroupScheme B) {V V' : Over B} (e : V ≅ V') :
    (n : ℕ) → source G V n ≅ source G V' n
  | 0 => e
  | n + 1 => sourceCongr G e n ⊗ᵢ Iso.refl G.X

/-- Initial-source transport preserves the entire basepoint section. -/
theorem basepointSection_sourceCongr (G : GroupScheme B)
    {V V' : Over B} (e : V ≅ V') (v₀ : 𝟙_ (Over B) ⟶ V) (n : ℕ) :
    basepointSection (G := G) v₀ n ≫ (sourceCongr G e n).hom =
      basepointSection (G := G) (v₀ ≫ e.hom) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (basepointSection v₀ n ⊗ₘ 𝟙 G.X) ≫
      ((sourceCongr G e n).hom ⊗ₘ 𝟙 G.X) = _
    rw [tensorHom_comp_tensorHom, Category.id_comp, ih]
    rfl

/-- Compare the nested sources built from the actual extended affine line
with pullback of the original nested source. -/
def affineLineSourceBaseChangeIso (b : B' ⟶ B) (G : GroupScheme B) (n : ℕ) :
    source ((GroupScheme.baseChange b).obj G) (AffineLine.scheme B') n ≅
      (Over.pullback b).obj (source G (AffineLine.scheme B) n) :=
  sourceCongr ((GroupScheme.baseChange b).obj G) (AffineLine.baseChangeIso b) n ≪≫
    (sourceBaseChangeIso b G (AffineLine.scheme B) n).symm

/-- The actual affine-line source comparison transports the whole zero
section, including all group parameters. -/
theorem basepointSection_affineLineBaseChange (b : B' ⟶ B)
    (G : GroupScheme B) (n : ℕ) :
    basepointSection (G := (GroupScheme.baseChange b).obj G)
        (AffineLine.zeroSection B') n ≫ (affineLineSourceBaseChangeIso b G n).hom =
      (parametersBaseChangeIso b G n).inv ≫
        (Over.pullback b).map
          (basepointSection (G := G) (AffineLine.zeroSection B) n) := by
  apply (cancel_mono (sourceBaseChangeIso b G (AffineLine.scheme B) n).hom).mp
  change (basepointSection (G := (GroupScheme.baseChange b).obj G)
      (AffineLine.zeroSection B') n ≫
        (sourceCongr ((GroupScheme.baseChange b).obj G) (AffineLine.baseChangeIso b) n).hom ≫
          (sourceBaseChangeIso b G (AffineLine.scheme B) n).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [basepointSection_sourceCongr, ← AffineLine.zeroSection_baseChange,
    basepointSection_baseChange, Iso.inv_hom_id_assoc]

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed K]
    {G W : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))
local notation "A_K" => AffineLine.scheme (Spec (CommRingCat.of K))
local notation "z_K" => AffineLine.zeroSection (Spec (CommRingCat.of K))

/-- Smooth pointed families are trivial if their target becomes affine-line
rigid after a separably closed field extension. The algebraic rational-point
proposition remains an explicit premise. -/
theorem family_eq_one_of_sepClosed_extension_of_rationalPointStatement
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    [Smooth G.X.hom] [IsSeparated W.X.hom]
    (hW : HasConstantAffineLineMaps ((GroupScheme.baseChange b).obj W))
    (n : ℕ) (f : source G A n ⟶ W.X)
    (h₀ : basepointSection (G := G) z n ≫ f = 1) : f = 1 := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc k K
  have : Surjective b := hb₁
  have : Flat b := hb₂
  have : QuasiCompact b := hb₃
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsSeparated ((GroupScheme.baseChange b).obj W).X.hom := by
    change IsSeparated (pullback.snd W.X.hom b)
    infer_instance
  let e := affineLineSourceBaseChangeIso b G n
  let f_K : source ((GroupScheme.baseChange b).obj G) A_K n ⟶
      ((GroupScheme.baseChange b).obj W).X := e.hom ≫ (Over.pullback b).map f
  have h₀_K : basepointSection (G := (GroupScheme.baseChange b).obj G) z_K n ≫ f_K = 1 := by
    dsimp only [f_K, e]
    rw [← Category.assoc, basepointSection_affineLineBaseChange, Category.assoc,
      ← (Over.pullback b).map_comp, h₀, Functor.map_one, MonObj.comp_one]
  have h_K : f_K = 1 :=
    family_eq_one_of_smooth_of_rationalPointStatement hP hW n f_K h₀_K
  apply (Over.pullback b).map_injective
  rw [Functor.map_one]
  apply (cancel_epi e.hom).mp
  simpa only [MonObj.comp_one] using h_K

end Field

end PointedCommutatorFamily

end Langlands.GroupScheme
