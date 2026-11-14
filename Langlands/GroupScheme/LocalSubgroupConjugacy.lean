import Langlands.GroupScheme.SubgroupConjugatingPoint
import Langlands.GroupScheme.LocalCosetDescent
import Langlands.GroupScheme.CocharacterTransport

/-! # Local conjugacy from subgroup-valued differences -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G B B' : GroupScheme S}

namespace SubgroupFunctor

/-- Membership in a conjugated represented subgroup is conjugated membership. -/
theorem conj_mem_range_innerIso_iff (i : B ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) (V : Over S) (x : V ⟶ G.X) :
    G.constantPoint g V * x * (G.constantPoint g V)⁻¹ ∈
        (range (i ≫ (G.innerIso g).hom)).carrier V ↔
      x ∈ (range i).carrier V := by
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at hy
    exact mul_left_cancel (mul_right_cancel hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]⟩

/-- For a base point, the all-test conjugacy relation is exactly equality of
the represented subgroup ranges after the actual inner automorphism. -/
theorem isConjugatingPoint_iff_range_innerIso (i : B ⟶ G) (j : B' ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    IsConjugatingPoint (range i) (range j) g ↔
      range (i ≫ (G.innerIso g).hom) = range j := by
  constructor
  · intro hg
    ext V x
    let c := G.constantPoint g V
    let z := c⁻¹ * x * c
    have he : c * z * c⁻¹ = x := by dsimp [z]; group
    have hi := conj_mem_range_innerIso_iff i g V z
    change c * z * c⁻¹ ∈ _ ↔ _ at hi
    rw [he] at hi
    have hj := hg V (Over.homMk V.hom (by simp)) z
    rw [comp_eq_constantPoint] at hj
    change _ ↔ c * z * c⁻¹ ∈ _ at hj
    rw [he] at hj
    exact hi.trans hj
  · intro hr V a x
    rw [comp_eq_constantPoint, ← hr]
    exact (conj_mem_range_innerIso_iff i g V x).symm

variable {F F' : SubgroupFunctor G}

/-- Conjugacy after base change tests every refinement over the original base. -/
theorem IsConjugatingPoint.of_baseChange (b : S' ⟶ S)
    {U : Over S'} {g : U ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hg : IsConjugatingPoint (F.baseChange b) (F'.baseChange b) g) :
    IsConjugatingPoint F F' (baseChangePointsEquiv b G U g) := by
  intro V a x
  let W : Over S' := Over.mk (a.left ≫ U.hom)
  let e : (Over.map b).obj W ≅ V := Over.isoMk (Iso.refl _) (by
    change (𝟙 V.left) ≫ V.hom = (a.left ≫ U.hom) ≫ b
    have hw : a.left ≫ (U.hom ≫ b) = V.hom := a.w
    simpa only [Category.id_comp, Category.assoc] using hw.symm)
  let a' : W ⟶ U := Over.homMk a.left rfl
  let y := (baseChangePointsEquiv b G W).symm (e.hom ≫ x)
  have ha : (Over.map b).map a' = e.hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = (𝟙 V.left) ≫ a.left
    simp only [Category.id_comp]
  have h : e.hom ≫ x ∈ F.carrier _ ↔
      e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g) * x *
        (a ≫ baseChangePointsEquiv b G U g)⁻¹) ∈ F'.carrier _ := by
    simpa only [mem_baseChange, map_mul, map_inv, baseChangePointsEquiv_naturality,
      y, MulEquiv.apply_symm_apply, ha, MonObj.comp_mul, GrpObj.comp_inv,
      Category.assoc] using hg W a' y
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using
      F'.comp_mem e.inv (h.mp (F.comp_mem e.hom hx))
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using
      F.comp_mem e.inv (h.mpr (F'.comp_mem e.hom hx))

/-- Arbitrary base change preserves and reflects the all-test relation. -/
theorem isConjugatingPoint_baseChange_iff (b : S' ⟶ S)
    {U : Over S'} (g : U ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsConjugatingPoint (F.baseChange b) (F'.baseChange b) g ↔
      IsConjugatingPoint F F' (baseChangePointsEquiv b G U g) := by
  constructor
  · exact IsConjugatingPoint.of_baseChange b
  · intro hg
    exact hg.baseChange b (𝟙 _) g (by simp)

/-- For a rational point of the pulled-back group, the relation corresponds
to the same point on the new base considered as an original test scheme. -/
theorem isConjugatingPoint_baseChangeBasePointsEquiv_iff (b : S' ⟶ S)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsConjugatingPoint (F.baseChange b) (F'.baseChange b) g ↔
      IsConjugatingPoint F F' (baseChangeBasePointsEquiv b G g) := by
  let e : Over.mk b ≅ (Over.map b).obj (Over.mk (𝟙 S')) :=
    Over.isoMk (Iso.refl _) (by simp)
  have he : baseChangeBasePointsEquiv b G g =
      e.hom ≫ baseChangePointsEquiv b G (Over.mk (𝟙 S')) g := rfl
  rw [he]
  constructor
  · intro hg
    exact (hg.of_baseChange b).restrict e.hom
  · intro hg
    apply (isConjugatingPoint_baseChange_iff b g).mpr
    simpa only [Iso.inv_hom_id_assoc] using hg.restrict e.inv

/-- A point on any test scheme conjugates the original ranges if and only if
its actual rational pullback point conjugates the pulled-back ranges. -/
theorem isConjugatingPoint_iff_baseChange_range (i : B ⟶ G) (j : B' ⟶ G)
    {U : Over S} (g : U ⟶ G.X) :
    IsConjugatingPoint (range i) (range j) g ↔
      range ((GroupScheme.baseChange U.hom).map i ≫
        (((GroupScheme.baseChange U.hom).obj G).innerIso
          ((baseChangeBasePointsEquiv U.hom G).symm g)).hom) =
      range ((GroupScheme.baseChange U.hom).map j) := by
  rw [← isConjugatingPoint_iff_range_innerIso, range_baseChangeHom,
    range_baseChangeHom, isConjugatingPoint_baseChangeBasePointsEquiv_iff,
    MulEquiv.apply_symm_apply]

/-- The inverse-coboundary differences of conjugating points lift to a
self-normalizing source subgroup. -/
theorem IsConjugatingPoint.coboundary_inv_lifts (i : B ⟶ G) (j : B' ⟶ G)
    {U : Over S} {g : U ⟶ G.X}
    (hg : IsConjugatingPoint (range i) (range j) g)
    (hself : (range i).normalizer = range i) :
    ∀ {Z : Over S} (a b : Z ⟶ U),
      ∃ h : Z ⟶ B.X, h ≫ i.hom.hom = (Cocycle.coboundary g⁻¹).toFun a b := by
  intro Z a b
  have hh := (hg.restrict a).inv_mul_mem_normalizer (hg.restrict b)
  rw [hself] at hh
  simpa only [mem_range, Cocycle.coboundary, GrpObj.comp_inv, inv_inv] using hh

end SubgroupFunctor

/-- Every base point has an open neighbourhood on which an actual rational
group point conjugates the first represented subgroup onto the second. -/
def HasZariskiLocalSubgroupConjugacy (i : B ⟶ G) (j : B' ⟶ G) : Prop :=
  ∀ y : S, ∃ W : S.Opens, y ∈ W ∧
    ∃ g : Over.mk (𝟙 W.toScheme) ⟶ ((GroupScheme.baseChange W.ι).obj G).X,
      SubgroupFunctor.range ((GroupScheme.baseChange W.ι).map i ≫
        (((GroupScheme.baseChange W.ι).obj G).innerIso g).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange W.ι).map j)

namespace LocalSubgroupConjugacy

open SubgroupFunctor

/-- Local coset representatives of a supplied conjugating point conjugate
the represented subgroups, by right correction and fpqc descent. -/
theorem hasZariskiLocalSubgroupConjugacy_of_cosetRepresentatives
    (i : B ⟶ G) (j : B' ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    {U : Over S} [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]
    (g : U ⟶ G.X) (hg : IsConjugatingPoint (range i) (range j) g)
    (hcoset : HasLocalCosetRepresentatives i g) :
    HasZariskiLocalSubgroupConjugacy i j := by
  intro y
  obtain ⟨W, hy, s, f, hfac⟩ := hcoset y
  let UW : Over S := Over.mk ((U.hom ⁻¹ᵁ W).ι ≫ U.hom)
  let r : UW ⟶ U := Over.homMk (U.hom ⁻¹ᵁ W).ι
  let p : UW ⟶ Over.mk W.ι :=
    Over.homMk (U.hom ∣_ W) (morphismRestrict_ι U.hom W)
  have hnorm : f ≫ i.hom.hom ∈ (range i).normalizer.carrier UW :=
    le_def.mp (le_normalizer (range i)) UW ⟨f, rfl⟩
  have hcorrect := (hg.restrict r).mul_of_mem_normalizer hnorm
  have hps : IsConjugatingPoint (range i) (range j) (p ≫ s) := by
    rw [← hfac]
    exact hcorrect
  have : QuasiCompact p.left := by
    change QuasiCompact (U.hom ∣_ W)
    infer_instance
  have : Flat p.left := by
    change Flat (U.hom ∣_ W)
    infer_instance
  have : Surjective p.left := by
    change Surjective (U.hom ∣_ W)
    infer_instance
  have hs : IsConjugatingPoint (range i) (range j) s :=
    IsConjugatingPoint.of_cover (hasFpqcMembershipDescent_range i)
      (hasFpqcMembershipDescent_range j) p hps
  exact ⟨W, hy, _, (isConjugatingPoint_iff_baseChange_range i j s).mp hs⟩

variable {R : CommRingCat.{u}} {K T : GroupScheme (Spec R)}
  {G B B' : GroupScheme (Spec R)}

/-- A supplied affine faithfully flat conjugating cover becomes Zariski-local
conjugacy when the source subgroup is self-normalizing and has a split-torus
quotient with a finite affine-vector-series kernel. -/
theorem hasZariskiLocalSubgroupConjugacy_of_vectorSeries
    (i : B ⟶ G) (i' : B' ⟶ G) [Mono i.hom.hom] [Mono i'.hom.hom]
    (j : K ⟶ B) (q : B ⟶ T) [Mono j.hom.hom]
    (hjq : range (kernelι q) = range j)
    [IsAffine B.X.left] [IsAffine T.X.left] [IsAffineHom K.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {n : ℕ} (hK : HasAffineVectorSeries n K) (hT : IsSplitTorus T)
    (hself : (range i).normalizer = range i)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (g : U ⟶ G.X) (hg : IsConjugatingPoint (range i) (range i') g) :
    HasZariskiLocalSubgroupConjugacy i i' :=
  hasZariskiLocalSubgroupConjugacy_of_cosetRepresentatives i i' g hg
    (LocalCosetDescent.hasLocalCosetRepresentatives_of_vectorSeries i j q hjq hK hT U g
      (hg.coboundary_inv_lifts i i' hself))

end LocalSubgroupConjugacy

end Langlands.GroupScheme
