import Langlands.GroupScheme.Rational.OrthogonalOrbitDescent
import Langlands.GroupScheme.Rational.CorootRationalGaloisTransport
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Galois.Local.SeparableInertiaDefinitions
import Mathlib.FieldTheory.Galois.Infinite

/-! # Fixed-point descent and unit cocharacter points over a Galois extension

Two auxiliary facts used in the descent of zero-value root jumps from `K = F^ur` to `F`.

* A rational point of `G_K` that is fixed by every `σ ∈ Aut(K/k)` and lies in the base change
  of a root group `U_a` is the extension of a rational point of `U_a`, for every Galois
  extension `K/k`, finite or not.
* For a cocharacter `ν` of a torus `S` over `k` and a unit `c ∈ Kˣ` of valuation one, the
  point `ν_K(c)` of `S_K` lies in the common kernel of the character valuations, and its
  image in `G(K)` is the `k`-scheme point `ν(c) : Spec K → G` obtained by evaluating `ν`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GaloisPoint

open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- A coefficient point fixed by every coefficient automorphism comes from the base field,
as soon as every automorphism-fixed element of `L` lies in `k`. -/
theorem mem_range_extend_of_fixedField
    (hfix : ∀ x : L, (∀ σ : L ≃ₐ[k] L, σ x = x) → x ∈ Set.range (algebraMap k L))
    {x : G.affinePoints (CommAlgCat.of k L)} (hx : x ∈ fixedSubgroup k L G) :
    x ∈ Set.range (extend k L G) := by
  have hc : ∀ a, coordinates k G L x a ∈ Set.range (algebraMap k L) := fun a =>
    hfix _ fun σ => by
      simpa only [coordinates_conjugate] using
        congrArg (fun z => coordinates k G L z a) (hx σ)
  choose d hd using hc
  let φ : AffineCoordinateRing k G.X →ₐ[k] k :=
    { toFun := d
      map_one' := (algebraMap k L).injective (by simp only [hd, map_one])
      map_mul' := fun a b => (algebraMap k L).injective (by simp only [map_mul, hd])
      map_zero' := (algebraMap k L).injective (by simp only [hd, map_zero])
      map_add' := fun a b => (algebraMap k L).injective (by simp only [map_add, hd])
      commutes' := fun r => (algebraMap k L).injective (by
        change algebraMap k L (d (algebraMap k _ r)) = algebraMap k L r
        rw [hd, (coordinates k G L x).commutes]) }
  refine ⟨(coordinates k G k).symm φ, ?_⟩
  apply (coordinates k G L).injective
  ext a
  rw [coordinates_extend, Equiv.apply_symm_apply]
  exact hd a

/-- Over a Galois extension, finite or infinite, a coefficient point fixed by every
coefficient automorphism comes from the base field. -/
theorem mem_range_extend_of_isGalois [IsGalois k L]
    {x : G.affinePoints (CommAlgCat.of k L)} (hx : x ∈ fixedSubgroup k L G) :
    x ∈ Set.range (extend k L G) :=
  mem_range_extend_of_fixedField k L G
    (fun y hy => (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr hy) hx

end GaloisPoint

namespace GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Over a Galois extension `K/k`, finite or infinite, a rational point of `G_K` fixed by
every coefficient automorphism is the extension of a rational point of `G`. -/
theorem exists_rationalExtend_eq_of_fixed_of_isGalois {g : rationalPoints (baseChanged k K G)}
    (hg : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ g = g) :
    ∃ g₀ : rationalPoints G, rationalExtend k K G g₀ = g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hx : baseChangeCoeffEquiv k K G g ∈ GaloisPoint.fixedSubgroup k K G := fun σ => by
    rw [← baseChangeCoeffEquiv_rationalConjugate, hg σ]
  obtain ⟨y, hy⟩ := GaloisPoint.mem_range_extend_of_isGalois k K G hx
  refine ⟨(rationalCoeffEquiv k G).symm y, ?_⟩
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalExtend, MulEquiv.apply_symm_apply, hy]

/-- Over a Galois extension `K/k`, finite or infinite, a rational point of `G_K` fixed by
every coefficient automorphism and lying in the base change of the root group `U_a` of a
nonzero character `a` of a split torus is the extension of a rational point of `U_a`. -/
theorem exists_mem_rootGroupPoints_of_fixed_of_isGalois [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0)
    {g : rationalPoints (baseChanged k K G)}
    (hg : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ g = g)
    (hmem : g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (characterLattice.baseChange (algebraBaseMap k K) S a)) :
    ∃ g₀ ∈ Langlands.Geometry.Building.rootGroupPoints i a, rationalExtend k K G g₀ = g := by
  obtain ⟨g₀, rfl⟩ := exists_rationalExtend_eq_of_fixed_of_isGalois k K hg
  exact ⟨g₀, (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff i hS a ha
    g₀).mp hmem, rfl⟩

end GaloisPointComparison

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

section UnitCocharacterPoints

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A cocharacter of a torus over `K`, evaluated at a unit of valuation one, lies in the
common kernel of the character valuations. -/
theorem cocharacterPoints_mem_characterValuationKernel_of_eq_one
    (A : CommGroupScheme (Spec (CommRingCat.of K))) (v : Valuation K Γ₀) {c : Kˣ}
    (hc : v (c : K) = 1) (ν : cocharacterLattice A) :
    CocharacterUniformizer.cocharacterPoints K A ν c ∈ characterValuationKernel v A.toGrp := by
  rw [mem_characterValuationKernel]
  intro χ
  have h := CocharacterUniformizer.rationalCharacterEval_cocharacterPoints K A
    (rationalCharacters.equivCharacterLattice A χ) ν c
  rw [AddEquiv.symm_apply_apply] at h
  rw [h, Units.val_zpow_eq_zpow_val, map_zpow₀, hc, one_zpow]

end UnitCocharacterPoints

section BaseChangeCocharacterPoints

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S

/-- The base-changed cocharacter `ν_K` evaluated at a unit `c ∈ Kˣ` is, as a `k`-scheme
point `Spec K → S`, the cocharacter `ν` evaluated at `c`. -/
theorem baseChangeCoeffEquiv_cocharacterPoints_baseChange (ν : cocharacterLattice S) (c : Kˣ) :
    baseChangeCoeffEquiv k K S.toGrp
        (CocharacterUniformizer.cocharacterPoints K S_K (cocharacterLattice.baseChange b S ν) c) =
      ((Gm.affinePointsEquiv _).symm c :
          Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) ≫
        (CommGroupScheme.groupHom ν).hom.hom := by
  have h := cocharacterLattice.baseChange_points b S ν (Over.mk (𝟙 _))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm c)
  change (baseChangePointsEquiv b S.toGrp (Over.mk (𝟙 _))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm c ≫
        (CommGroupScheme.groupHom (cocharacterLattice.baseChange b S ν)).hom.hom)) = _
  rw [h]
  congr 1
  apply (Gm.pointsEquiv _ _).injective
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  have key : ∀ {R : CommRingCat.{u}} {T : Scheme.{u}} (f : Spec R ⟶ T) (c : Rˣ),
      ((Gm.pointsEquiv T (Over.mk f) ((Gm.affinePointsEquiv f).symm c)).val : Γ(Spec R, ⊤)) =
        (Scheme.ΓSpecIso R).inv (c : R) := by
    intro R T f c
    have h := Gm.affinePointsEquiv_val f ((Gm.affinePointsEquiv f).symm c)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h, Iso.hom_inv_id_apply]
  exact (key (R := CommRingCat.of K) _ c).trans (key (R := CommRingCat.of K) _ c).symm

/-- **Unit torus points with prescribed image.** For a cocharacter `ν` of a torus `S` over
`k`, a map `iS : S → G` and a unit `c ∈ Kˣ` of valuation one, there is a point `t` of `S_K`
in the common kernel of the character valuations whose image in `G(K)`, read as a `k`-scheme
point `Spec K → G`, is `iS(ν(c))`. -/
theorem exists_mem_characterValuationKernel_baseChangeCoeffEquiv_eq
    (iS : S.toGrp ⟶ G) (ν : cocharacterLattice S) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) {c : Kˣ} (hc : v (c : K) = 1) :
    ∃ t ∈ characterValuationKernel v (S_K).toGrp,
      baseChangeCoeffEquiv k K G
          (rationalPoints.map ((GroupScheme.baseChange b).map iS) t) =
        ((Gm.affinePointsEquiv _).symm c :
            Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) ≫
          (CommGroupScheme.groupHom ν ≫ iS).hom.hom := by
  refine ⟨CocharacterUniformizer.cocharacterPoints K S_K (cocharacterLattice.baseChange b S ν) c,
    cocharacterPoints_mem_characterValuationKernel_of_eq_one _ v hc _, ?_⟩
  change baseChangeBasePointsEquiv (baseMap k K) G
      (CocharacterUniformizer.cocharacterPoints K S_K (cocharacterLattice.baseChange b S ν) c ≫
        ((GroupScheme.baseChange b).map iS).hom.hom) = _
  rw [baseChangeBasePointsEquiv_comp]
  change baseChangeCoeffEquiv k K S.toGrp
      (CocharacterUniformizer.cocharacterPoints K S_K (cocharacterLattice.baseChange b S ν) c) ≫
    iS.hom.hom = _
  rw [baseChangeCoeffEquiv_cocharacterPoints_baseChange]
  rfl

end BaseChangeCocharacterPoints

namespace MaximalUnramified

open Langlands.LocalGalois.Separable

/-- **Fixed-point descent of root-group points from `F^ur` to `F`.** A rational point of
`G_K`, `K = F^ur`, fixed by every `σ ∈ Aut(K/F)` and lying in the base change of the root
group `U_a` of a nonzero character `a` of a split torus, is the extension of a rational point
of `U_a`. -/
theorem exists_mem_rootGroupPoints_of_galoisFixed (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))} (i : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0)
    {g : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hg : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      rationalConjugate F (inertiaFixedField F) G σ g = g)
    (hmem : g ∈ rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i)
      (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a)) :
    ∃ g₀ ∈ rootGroupPoints i a, rationalExtend F (inertiaFixedField F) G g₀ = g :=
  exists_mem_rootGroupPoints_of_fixed_of_isGalois F (inertiaFixedField F) i hS a ha hg hmem

end MaximalUnramified

end Langlands.Geometry.Building
