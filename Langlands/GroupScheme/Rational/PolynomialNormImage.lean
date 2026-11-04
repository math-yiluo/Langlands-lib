import Langlands.GroupScheme.Rational.PolynomialNormTangent
import Langlands.GroupScheme.Rational.SplitUnipotentSurjectiveImage
import Langlands.GroupScheme.Rational.VectorGroupSplit
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Nontrivial central split images of Galois norms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Centrality descends through a flat surjective precomposition. -/
theorem IsCentral.of_flat_surjective_precomp {B : Scheme.{u}}
    {A H G : GroupScheme B} (p : A ⟶ H) [Flat p.hom.hom.left]
    [Surjective p.hom.hom.left] {i : H ⟶ G} (hc : IsCentral (p ≫ i)) :
    IsCentral i := by
  intro T x
  let V : Over B := Over.mk (pullback.fst x.left p.hom.hom.left ≫ T.hom)
  let v : V ⟶ T := Over.homMk (pullback.fst x.left p.hom.hom.left) rfl
  let y : V ⟶ A.X := Over.homMk (pullback.snd x.left p.hom.hom.left) (by
    rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have hvf : Flat v.left := by
    change Flat (pullback.fst x.left p.hom.hom.left)
    infer_instance
  have hvs : Surjective v.left := by
    change Surjective (pullback.fst x.left p.hom.hom.left)
    infer_instance
  let : Flat v.left := hvf
  let : Surjective v.left := hvs
  apply mem_center_of_flat_surjective v
  have he : v ≫ x = y ≫ p.hom.hom :=
    Over.OverMorphism.ext pullback.condition
  rw [← Category.assoc, he, Category.assoc]
  exact hc V y

namespace PolynomialPoint

variable {k : Type u} [Field k]
    {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual smooth connected central split image, with its quotient map and
nonzero tangent retained. -/
structure CentralSplitImage (q : A ⟶ G) where
  groupScheme : GroupScheme (Spec (CommRingCat.of k))
  inclusion : groupScheme ⟶ G
  projection : A ⟶ groupScheme
  factor : projection ≫ inclusion = q
  closed : IsClosedSubgroup inclusion
  affine : IsAffineHom groupScheme.X.hom
  smooth : Smooth groupScheme.X.hom
  connected : ConnectedSpace groupScheme.X.left
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  quasiCompact : QuasiCompact projection.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.hom.hom.left
  central : IsCentral inclusion
  split : RelativeRoot.IsSplitUnipotent groupScheme
  tangent : lieKernel groupScheme k
  tangent_ne_one : tangent ≠ 1
  range_ne_bot : SubgroupFunctor.range inclusion ≠ ⊥

/-- A nonzero differential of a central homomorphism from a split unipotent
source gives a nontrivial smooth connected central split image. -/
def centralSplitImageOfNonzeroDifferential
    [Smooth A.X.hom] [ConnectedSpace A.X.left] [IsAffineHom A.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (q : A ⟶ G) (hsplit : RelativeRoot.IsSplitUnipotent A)
    (hcentral : IsCentral q) (hne : Lie.targetMapLinear q k ≠ 0) :
    CentralSplitImage q := by
  classical
  apply Classical.choice
  obtain ⟨D, i, p, hi, hp, hf, hs, hqc, hlfp, hsm, hc, ha⟩ :=
    HomImage.exists_image q
  let : IsAffineHom D.X.hom := ha
  let : Smooth D.X.hom := hsm
  let : ConnectedSpace D.X.left := hc
  let : Flat p.hom.hom.left := hf
  let : Surjective p.hom.hom.left := hs
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hcent : IsCentral i := IsCentral.of_flat_surjective_precomp p (hp ▸ hcentral)
  have hDs : RelativeRoot.IsSplitUnipotent D :=
    hsplit.of_surjective_to_smooth_affine p
  have hex : ∃ x : Additive (lieKernel A k), Lie.targetMapLinear q k x ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  let y : lieKernel D k := Lie.targetMap p k x.toMul
  have hy : y ≠ 1 := by
    intro h
    apply hx
    apply Additive.toMul.injective
    have hcomp : Lie.targetMap i k y = Lie.targetMap q k x.toMul := by
      apply Subtype.ext
      change (x.toMul.val ≫ p.hom.hom) ≫ i.hom.hom = x.toMul.val ≫ q.hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hp]
    change Lie.targetMap q k x.toMul = 1
    rw [← hcomp, h, map_one]
  have hnt : SubgroupFunctor.range i ≠ ⊥ := by
    intro h
    have hm : y.val ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier _ :=
      SubgroupFunctor.mem_range.mpr ⟨y.val, rfl⟩
    rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
    apply hy
    apply Subtype.ext
    apply (cancel_mono i.hom.hom).mp
    exact hm.trans (MonObj.one_comp _).symm
  exact ⟨⟨D, i, p, hp, hi, ha, hsm, hc, hf, hs, hqc, hlfp, hcent, hDs, y, hy, hnt⟩⟩

/-- The image retained above has positive actual Lie dimension. -/
theorem CentralSplitImage.dimension_pos {q : A ⟶ G} (d : CentralSplitImage q) :
    letI := d.affine
    0 < Lie.dimension d.groupScheme := by
  let := d.affine
  let := d.smooth
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  exact ⟨Additive.ofMul d.tangent, fun h => d.tangent_ne_one (congrArg Additive.toMul h)⟩

variable (k) (L : Type u) [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [FiniteDimensional k L] [IsGalois k L] {n : ℕ}

local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- A central positive-dimensional vector subgroup over a finite Galois
extension supplies an actual nontrivial smooth connected central split subgroup
over the base field. -/
def centralSplitImageOfCentralHom
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) [Mono f.hom.hom]
    (hf : IsCentral f) (hn : 0 < n) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    CentralSplitImage (nonzeroNormOfCentralHom k L G f hf hn).val := by
  let hV : RelativeRoot.IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of k) n) n :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) n, VectorGroup.isNaturalVectorCoordinates⟩
  letI := hV.isAffineHom
  letI := hV.smooth
  letI := hV.connectedSpace
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let q := nonzeroNormOfCentralHom k L G f hf hn
  exact centralSplitImageOfNonzeroDifferential q.val hV.isSplitUnipotent q.property.1
    q.property.2

end PolynomialPoint
end Langlands.GroupScheme
