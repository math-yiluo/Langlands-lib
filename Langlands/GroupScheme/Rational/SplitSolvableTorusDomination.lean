import Langlands.GroupScheme.Rational.SplitSolvablePicardSection
import Langlands.GroupScheme.Rational.SplitTorusDominationOperations
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Torus.SplitTorusQuotientFactor
import Langlands.GroupScheme.AffinePointFaithfullyFlatDescent
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Split-torus domination of split-solvable groups

An affine group over a field with a split-solvable series admits a pointed dominant morphism
of schemes from a split torus. The length-zero case is the trivial group; a `𝔾ₘ` quotient is
its own split torus; `𝔾ₐ = Spec k[t]` is dominated by `𝔾ₘ = Spec k[t, t⁻¹]` through the
injective inclusion `k[t] → k[t, t⁻¹]`; and in a series step `N → H → V` the multiplication
map `N × V → H`, `(n, v) ↦ n · σ(v)`, built from a scheme section `σ` of the quotient map,
has a right inverse, so it carries a domination of `N × V` to one of `H`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace HasPointedSplitTorusDomination

variable {H : GroupScheme (Spec (CommRingCat.of k))}

/-- A morphism of schemes over the base with a right inverse is dominant. -/
theorem isDominant_of_comp_eq_id {X Y : Over (Spec (CommRingCat.of k))} (m : X ⟶ Y)
    (r : Y ⟶ X) (hr : r ≫ m = 𝟙 Y) : IsDominant m.left := by
  have : IsDominant (r.left ≫ m.left) := by
    rw [← Over.comp_left, hr, Over.id_left]
    infer_instance
  exact IsDominant.of_comp r.left m.left

/-- Any dominant morphism of schemes from a split torus to `H`, not necessarily pointed, gives
a pointed split-torus domination: right translation by the inverse of the image of the
identity is an automorphism of the scheme of `H`. -/
theorem of_dominant {P : GroupScheme (Spec (CommRingCat.of k))} (hP : IsSplitTorus P)
    (p : P.X ⟶ H.X) (hd : IsDominant p.left) : HasPointedSplitTorusDomination H := by
  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p
  let ρ : H.X ⟶ H.X := 𝟙 H.X * (toUnit H.X ≫ c⁻¹)
  let ρ' : H.X ⟶ H.X := 𝟙 H.X * (toUnit H.X ≫ c)
  have hρ'ρ : ρ' ≫ ρ = 𝟙 H.X := by
    have h1 : ρ' ≫ toUnit H.X = toUnit H.X := toUnit_unique _ _
    change ρ' ≫ (𝟙 H.X * (toUnit H.X ≫ c⁻¹)) = 𝟙 H.X
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, h1, GrpObj.comp_inv]
    change 𝟙 H.X * (toUnit H.X ≫ c) * (toUnit H.X ≫ c)⁻¹ = 𝟙 H.X
    group
  have : IsDominant ρ.left := isDominant_of_comp_eq_id ρ ρ' hρ'ρ
  refine ⟨P, p ≫ ρ, hP, ?_, ?_⟩
  · change IsDominant (p.left ≫ ρ.left)
    infer_instance
  · have h1 : c ≫ toUnit H.X = 𝟙 _ := toUnit_unique _ _
    change ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p) ≫ ρ = 1
    change c ≫ (𝟙 H.X * (toUnit H.X ≫ c⁻¹)) = 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, h1, Category.id_comp,
      mul_inv_cancel]

/-- The trivial group has a pointed split-torus domination, by the constant map from the
trivial split torus. -/
theorem of_range_id_eq_bot (h : SubgroupFunctor.range (𝟙 H) = ⊥) :
    HasPointedSplitTorusDomination H := by
  have h1 : (1 : H.X ⟶ H.X) = 𝟙 H.X := by
    have hm : 𝟙 H.X ∈ (SubgroupFunctor.range (𝟙 H)).carrier H.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    rw [h] at hm
    exact hm.symm
  let P := splitTorus (Spec (CommRingCat.of k)) PEmpty.{u + 1}
  refine of_dominant (isSplitTorus_splitTorus PEmpty) (1 : P.X ⟶ H.X) ?_
  apply isDominant_of_comp_eq_id _ (1 : H.X ⟶ P.X)
  rw [MonObj.comp_one, h1]

/-- A group isomorphic to `𝔾ₘ` is dominated by itself. -/
theorem of_iso_gm {V : GroupScheme (Spec (CommRingCat.of k))}
    (e : V ≅ (Gm (Spec (CommRingCat.of k))).toGrp) : HasPointedSplitTorusDomination V :=
  ⟨V, 𝟙 V.X, IsSplitTorus.of_iso e isSplitTorus_gm, by
    rw [Over.id_left]
    infer_instance, Category.comp_id _⟩

/-- The additive embedding of the exponent monoid of `k[t]` into that of `k[t, t⁻¹]`. -/
def gaExponentHom : (Fin 1 →₀ ℕ) →+ (PUnit.{u + 1} → ℤ) where
  toFun d := fun _ => (d 0 : ℤ)
  map_zero' := by
    funext
    simp
  map_add' a b := by
    funext
    simp

theorem gaExponentHom_injective : Function.Injective (gaExponentHom.{u}) := by
  intro a b h
  have h0 := congrFun h PUnit.unit
  simp only [gaExponentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Nat.cast_inj] at h0
  refine Finsupp.ext fun i => ?_
  rw [Subsingleton.elim i 0]
  exact h0

/-- The inclusion `k[t] → k[t, t⁻¹]` of the coordinate algebra of the one-dimensional vector
group into the coordinate algebra of the rank-one diagonalizable group. -/
def gaLaurentInclusion (R : CommRingCat.{u}) :
    VectorGroup.coordinateAlgebra R 1 ⟶ Diagonalizable.algebra R (PUnit.{u + 1} → ℤ) :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R R gaExponentHom.{u})

theorem gaLaurentInclusion_injective (R : CommRingCat.{u}) :
    Function.Injective (gaLaurentInclusion R).hom := by
  intro x y h
  exact AddMonoidAlgebra.mapDomain_injective gaExponentHom_injective h

/-- The rank-one diagonalizable group is a split torus. -/
theorem isSplitTorus_diagonalizable_punit :
    IsSplitTorus (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u + 1} → ℤ)).toGrp :=
  IsSplitTorus.of_iso (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl _))
    (isSplitTorus_splitTorus PUnit)

/-- A one-dimensional vector group over a field has a pointed split-torus domination. -/
theorem of_isVectorGroup {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : RelativeRoot.IsVectorGroupOfDimension V 1) : HasPointedSplitTorusDomination V := by
  obtain ⟨e, he⟩ := hV
  let f := RelativeRoot.vectorCoordinatesIso e he
  let R := CommRingCat.of k
  let p₀ : (Diagonalizable.groupScheme R (PUnit.{u + 1} → ℤ)).toGrp.X ⟶
      (VectorGroup.groupScheme R 1).X :=
    (algSpec R).map (gaLaurentInclusion R).op
  have hp₀ : IsDominant p₀.left := by
    rw [algSpec_map_left]
    exact SplitTorusQuotientFactor.isDominant_spec_map_of_injective _
      (gaLaurentInclusion_injective R)
  have : IsIso f.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso f)).inv)
  refine of_dominant isSplitTorus_diagonalizable_punit (p₀ ≫ f.inv.hom.hom) ?_
  change IsDominant (p₀.left ≫ f.inv.hom.hom.left)
  infer_instance

/-- An elementary split-solvable quotient has a pointed split-torus domination. -/
theorem of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : SplitSolvable.IsElementaryQuotient V) : HasPointedSplitTorusDomination V := by
  rcases hV with hV | ⟨⟨e⟩⟩
  · exact of_isVectorGroup hV
  · exact of_iso_gm e

end HasPointedSplitTorusDomination

namespace SplitSolvablePicard

/-- An elementary split-solvable quotient is smooth over the field. -/
theorem smooth_of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : SplitSolvable.IsElementaryQuotient V) : Smooth V.X.hom := by
  rcases hV with hV | ⟨⟨e⟩⟩
  · exact hV.smooth
  · exact (IsSplitTorus.of_iso e isSplitTorus_gm).smooth

end SplitSolvablePicard

open SplitSolvablePicard in
/-- Every affine group over a field with a split-solvable series has a pointed split-torus
domination. -/
theorem hasPointedSplitTorusDomination_of_hasSeries :
    ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))), SplitSolvable.HasSeries n H →
      IsAffineHom H.X.hom → HasPointedSplitTorusDomination H
  | 0, _, h, _ => HasPointedSplitTorusDomination.of_range_id_eq_bot h
  | n + 1, H, ⟨N, V, j, q, hj, hNs, _, _, hq, hV, hN⟩, _ => by
    have : IsClosedImmersion j.hom.hom.left := hj
    have hNa : IsAffineHom N.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hNd := hasPointedSplitTorusDomination_of_hasSeries n N hN hNa
    have hVd := HasPointedSplitTorusDomination.of_elementary hV
    obtain ⟨σ, hσ⟩ := exists_section_of_hasSeries j q hj hq hV hN
    have : Smooth N.X.hom := hNs
    have : Smooth V.X.hom := smooth_of_elementary hV
    have : IsAffineHom V.X.hom := isAffineHom_of_elementary hV
    have : IsReduced N.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ N.X.hom
    have : IsReduced V.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ V.X.hom
    obtain ⟨P, p, hP, hd, -⟩ := hNd.tensor hVd
    let m : (N ⊗ V).X ⟶ H.X := (fst N.X V.X ≫ j.hom.hom) * (snd N.X V.X ≫ σ)
    obtain ⟨n₀, hn₀⟩ := SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hq.2.2.2
      (𝟙 H.X * (q.hom.hom ≫ σ)⁻¹) (by
        rw [MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc, hσ,
          Category.comp_id, mul_inv_cancel])
    let r : H.X ⟶ (N ⊗ V).X := lift n₀ q.hom.hom
    have hr : r ≫ m = 𝟙 H.X := by
      change r ≫ ((fst N.X V.X ≫ j.hom.hom) * (snd N.X V.X ≫ σ)) = 𝟙 H.X
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, hn₀,
        mul_assoc, inv_mul_cancel, mul_one]
    have : IsDominant p.left := hd
    have : IsDominant m.left := HasPointedSplitTorusDomination.isDominant_of_comp_eq_id m r hr
    refine HasPointedSplitTorusDomination.of_dominant hP (p ≫ m) ?_
    change IsDominant (p.left ≫ m.left)
    infer_instance

/-- A split solvable group has a pointed split-torus domination. -/
theorem IsSplitSolvableGroupScheme.hasPointedSplitTorusDomination
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitSolvableGroupScheme G) :
    HasPointedSplitTorusDomination G := by
  obtain ⟨n, hn⟩ := hG.hasSeries
  exact hasPointedSplitTorusDomination_of_hasSeries n G hn hG.isAffineHom

end Langlands.GroupScheme
