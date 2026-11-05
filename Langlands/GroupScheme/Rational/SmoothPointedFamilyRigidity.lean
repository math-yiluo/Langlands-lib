import Langlands.GroupScheme.Rational.PointedFamilyFieldExtension
import Langlands.GroupScheme.Rational.VectorFactorPointedFamilies
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity

/-! # Unconditional smooth pointed-family rigidity and field descent -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace PointedCommutatorFamily

section SepClosed

variable {k : Type u} [Field k] [IsSepClosed k]
    {G W : GroupScheme (Spec (CommRingCat.of k))}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

/-- A smooth pointed family into a separated affine-line rigid group over a
separably closed field is trivial on its entire parameter source. -/
theorem family_eq_one_of_smooth
    [Smooth G.X.hom] [IsSeparated W.X.hom]
    (hW : HasConstantAffineLineMaps W) (n : ℕ)
    (f : source G A n ⟶ W.X)
    (h₀ : basepointSection (G := G) z n ≫ f = 1) : f = 1 := by
  have : Smooth (A).hom := by dsimp [AffineLine.scheme]; infer_instance
  have : Smooth (source G A n).hom := source_smooth G A n
  have : IsReduced (source G A n).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (source G A n).hom
  exact family_eq_one_of_basepointSection hW n
    (hasDenseRationalPoints_of_smooth_of_isSepClosed k _) f h₀

end SepClosed

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed K]
    {G W : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))
local notation "A_K" => AffineLine.scheme (Spec (CommRingCat.of K))
local notation "z_K" => AffineLine.zeroSection (Spec (CommRingCat.of K))

/-- A smooth pointed family is trivial if its separated target becomes
affine-line rigid over a separably closed field extension. -/
theorem family_eq_one_of_sepClosed_extension
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
  have h_K : f_K = 1 := family_eq_one_of_smooth hW n f_K h₀_K
  apply (Over.pullback b).map_injective
  rw [Functor.map_one]
  apply (cancel_epi e.hom).mp
  simpa only [MonObj.comp_one] using h_K

end FieldExtension

end PointedCommutatorFamily

namespace VectorFactorPointedFamilies

variable {k : Type u} [Field k]
    {G U V W : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}

/-- A nontrivial smooth pointed family forces a positive vector factor if its
complement becomes affine-line rigid over the separable closure. -/
theorem vector_dimension_pos_of_smooth
    [Smooth G.X.hom] [IsSeparated W.X.hom]
    (e : U ≅ V ⊗ W) (hV : RelativeRoot.IsVectorGroupOfDimension V d)
    (hW : HasConstantAffineLineMaps
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj W))
    (n : ℕ) (f : PointedCommutatorFamily.source G
      (AffineLine.scheme (Spec (CommRingCat.of k))) n ⟶ U.X)
    (hf : f ≠ 1)
    (h₀ : PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫ f = 1) : 0 < d := by
  have hs : PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫
        (f ≫ e.hom.hom.hom ≫ snd V.X W.X) = 1 := by
    change PointedCommutatorFamily.basepointSection (G := G)
      (AffineLine.zeroSection _) n ≫ f ≫ (e.hom ≫ snd V W).hom.hom = 1
    rw [← Category.assoc, h₀, MonObj.one_comp]
  have hw : f ≫ e.hom.hom.hom ≫ snd V.X W.X = 1 :=
    PointedCommutatorFamily.family_eq_one_of_sepClosed_extension
      (K := SeparableClosure k) hW n _ hs
  by_contra hd
  have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
  subst d
  have hv : f ≫ e.hom.hom.hom ≫ fst V.X W.X = 1 :=
    hV.eq_one_of_dim_zero _
  apply hf
  apply (cancel_mono e.hom.hom.hom).mp
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, MonObj.one_comp] using hv
  · simpa only [Category.assoc, MonObj.one_comp] using hw

end VectorFactorPointedFamilies

end Langlands.GroupScheme
