import Langlands.GroupScheme.IntegralModel.SplitTorusUnitPoints
import Langlands.GroupScheme.Torus.RingRepresentationWeightsBaseChange
import Langlands.Geometry.Building.KPWeilRestrictionUnitKernel
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Closed split tori of integral models from bounded points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SplitTorusClosure

open GaloisPointComparison Langlands.Geometry.Building

section Coordinates

variable {S : Scheme.{u}} {I : Type u} [Finite I]

/-- Affine split coordinates depend only on the underlying scheme morphism of a point. -/
theorem affinePointsEquiv_eq_of_left_eq {A : CommRingCat.{u}} {f₁ f₂ : Spec A ⟶ S}
    (x : Over.mk f₁ ⟶ (splitTorus S I).X) (y : Over.mk f₂ ⟶ (splitTorus S I).X)
    (h : (x.left : Spec A ⟶ (splitTorus S I).X.left) = y.left) :
    splitTorus.affinePointsEquiv I f₁ x = splitTorus.affinePointsEquiv I f₂ y := by
  funext i
  apply Units.ext
  rw [affinePointsEquiv_val, affinePointsEquiv_val, pointsEquiv_eq_of_left_eq x y h]

end Coordinates

section UnitPoints

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (I : Type u)

/-- In the base-coefficient convention, the `k`-point of `𝔾_m^I` with coordinates `t` is the
rational point with coordinates `t`. -/
theorem rationalCoeffEquiv_symm_algebraPointsEquiv_symm [Finite I] (t : I → kˣ) :
    (rationalCoeffEquiv k (splitTorus (Spec (CommRingCat.of k)) I)).symm
        ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).symm t) =
      (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of k)))).symm t := by
  apply (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of k)))).injective
  rw [MulEquiv.apply_symm_apply]
  conv_rhs => rw [← (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).apply_symm_apply t]
  apply affinePointsEquiv_eq_of_left_eq
  have h := rationalCoeffEquiv_left k (splitTorus (Spec (CommRingCat.of k)) I)
    ((rationalCoeffEquiv k _).symm
      ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).symm t))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The `L`-point of `𝔾_m^I` over `k` with coordinates `t`, read as a rational point of the
base change to `L`, is the inverse split base-change image of the rational point of `𝔾_m^I`
over `L` with coordinates `t`. -/
theorem baseChangeCoeffEquiv_symm_algebraPointsEquiv_symm [Finite I] (t : I → Lˣ) :
    (baseChangeCoeffEquiv k L (splitTorus (Spec (CommRingCat.of k)) I)).symm
        ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I L).symm t) =
      rationalPoints.map (splitTorus.baseChangeIso (baseMap k L) I).inv
        ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm t) := by
  apply (baseChangeCoeffEquiv k L _).injective
  rw [MulEquiv.apply_symm_apply]
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I L).injective
  rw [MulEquiv.apply_symm_apply]
  have h := splitTorus.affinePointsEquiv_baseChangeIso_inv I (baseMap k L)
    (𝟙 (Spec (CommRingCat.of L)))
    ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm t)
  rw [MulEquiv.apply_symm_apply] at h
  refine h.symm.trans ?_
  apply affinePointsEquiv_eq_of_left_eq
  rw [baseChangeCoeffEquiv_left, GroupScheme.baseChangePointsEquiv_left]
  rfl

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A `k`-point of `𝔾_m^I` whose coordinates have valuation one lies in the character
valuation kernel. -/
theorem rationalCoeffEquiv_symm_mem_characterValuationKernel [Fintype I] (v : Valuation k Γ₀)
    (t : I → kˣ) (ht : ∀ i, v (t i : k) = 1) :
    (rationalCoeffEquiv k (splitTorus (Spec (CommRingCat.of k)) I)).symm
        ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).symm t) ∈
      characterValuationKernel v (splitTorus (Spec (CommRingCat.of k)) I) := by
  rw [rationalCoeffEquiv_symm_algebraPointsEquiv_symm, mem_split_characterValuationKernel]
  intro i
  rw [MulEquiv.apply_symm_apply]
  exact ht i

/-- An `L`-point of `𝔾_m^I` over `k` whose coordinates have valuation one lies, as a rational
point of the base change to `L`, in the character valuation kernel. -/
theorem baseChangeCoeffEquiv_symm_mem_characterValuationKernel [Fintype I]
    (v : Valuation L Γ₀) (t : I → Lˣ) (ht : ∀ i, v (t i : L) = 1) :
    (baseChangeCoeffEquiv k L (splitTorus (Spec (CommRingCat.of k)) I)).symm
        ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I L).symm t) ∈
      characterValuationKernel v (baseChanged k L (splitTorus (Spec (CommRingCat.of k)) I)) := by
  rw [baseChangeCoeffEquiv_symm_algebraPointsEquiv_symm]
  apply map_characterValuationKernel_le v
  refine ⟨_, ?_, rfl⟩
  change _ ∈ characterValuationKernel v (splitTorus (Spec (CommRingCat.of L)) I)
  rw [mem_split_characterValuationKernel]
  intro i
  rw [MulEquiv.apply_symm_apply]
  exact ht i

end UnitPoints

section CommIso

variable {S : Scheme.{u}} {T T' : CommGroupScheme S}

/-- An isomorphism of the underlying group schemes of two commutative group schemes, as an
isomorphism of commutative group schemes. -/
def commIsoOfGroupIso (e : T.toGrp ≅ T'.toGrp) : T ≅ T' where
  hom := Additive.ofMul e.hom
  inv := Additive.ofMul e.inv
  hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
  inv_hom_id := congrArg Additive.ofMul e.inv_hom_id

@[simp] theorem groupHom_commIsoOfGroupIso_hom (e : T.toGrp ≅ T'.toGrp) :
    CommGroupScheme.groupHom (commIsoOfGroupIso e).hom = e.hom :=
  rfl

end CommIso

section Closure

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

omit [IsDomain R] [IsNoetherianRing R] in
/-- `D_R(ℤ^I)` is a split torus. -/
theorem isSplitTorus_torus (I : Type u) [Fintype I] [DecidableEq I] :
    IsSplitTorus (torus R I).toGrp :=
  IsSplitTorus.of_iso (splitIsoR R I) (isSplitTorus_splitTorus I)

omit [IsNoetherianRing R] in
/-- For the identity extension of coefficients, integral points of the base change are the
integral points of the model. -/
theorem mem_baseChange_self_coefficientIntegralPoints_iff
    (p : G.affinePoints (CommAlgCat.of K K)) :
    p ∈ (M.baseChange R K).coefficientIntegralPoints K K ↔
      (rationalCoeffEquiv K G).symm p ∈ M.integralPoints := by
  rw [M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates R K,
    M.mem_integralPoints_iff_genericCoordinates, MulEquiv.apply_symm_apply]

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **A closed split torus of the model from bounded points over a valuation ring.** Let `A`
be a valuation ring with infinite residue field and fraction field `L`, over `R`, with
`K ∩ A = R` inside `L`. Let `v` be a valuation of `L` that is one on the units of `A`. If
`iT : T → G` is a split closed subtorus of the generic fibre and the image of the character
valuation kernel of `T_L` lies in the integral points of the base change of `M` to `A`, then
`iT` extends to a closed split torus of `M`. -/
theorem exists_isSplitTorus_genericTorusMap_eq_of_baseChange
    (A L : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [Infinite (IsLocalRing.ResidueField A)]
    (v : Valuation L Γ₀) (hv : ∀ a : Aˣ, v (algebraMap A L (a : A)) = 1)
    (hint : ∀ x : K, algebraMap K L x ∈ Set.range (algebraMap A L) →
      x ∈ Set.range (algebraMap R K))
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (iT : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hiT : IsClosedSubgroup iT)
    (hb : (characterValuationKernel v (baseChanged K L T.toGrp)).map
        (rationalPoints.map ((GroupScheme.baseChange (baseMap K L)).map iT)) ≤
      (M.baseChange A L).integralPoints) :
    ∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of R))) (j : 𝒮.toGrp ⟶ M.group)
      (e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮 ≅ T),
      IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup j ∧
        M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iT := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  classical
  obtain ⟨j, hj, hgen⟩ := exists_isClosedSubgroup_genericTorusMap_eq M A L e iT hiT
    (fun t => by
      rw [mem_coefficientIntegralPoints_iff]
      apply hb
      refine ⟨rationalPoints.map ((GroupScheme.baseChange (baseMap K L)).map e.inv)
        ((baseChangeCoeffEquiv K L _).symm
          ((splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I L).symm
            (fun i => Units.map (algebraMap A L : A →* L) (t i)))), ?_, ?_⟩
      · exact map_characterValuationKernel_le v _
          ⟨_, baseChangeCoeffEquiv_symm_mem_characterValuationKernel K L I v _
            (fun i => hv (t i)), rfl⟩
      · apply (baseChangeCoeffEquiv K L G).injective
        rw [MulEquiv.apply_symm_apply]
        change baseChangeCoeffEquiv K L G
          (rationalPoints.map ((GroupScheme.baseChange (baseMap K L)).map iT)
            (rationalPoints.map ((GroupScheme.baseChange (baseMap K L)).map e.inv) _)) = _
        rw [baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_map, MulEquiv.apply_symm_apply,
          affinePointsTarget_apply, affinePointsTarget_apply, Category.assoc])
    hint
  exact ⟨torus R I, j, commIsoOfGroupIso (genericSplitIso R K I ≪≫ e.symm),
    isSplitTorus_torus I, hj, hgen⟩

/-- **A closed split torus of the model from bounded points.** Let `R` be a noetherian
valuation ring with infinite residue field and fraction field `K`, and `v` a valuation of `K`
that is one on the units of `R`. If `iT : T → G` is a split closed subtorus and the image of
the character valuation kernel of `T` lies in the integral points of `M`, then `iT` extends to
a closed split torus of `M`. -/
theorem exists_isSplitTorus_genericTorusMap_eq_of_bounded
    [ValuationRing R] [Infinite (IsLocalRing.ResidueField R)]
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (iT : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hiT : IsClosedSubgroup iT)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      M.integralPoints) :
    ∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of R))) (j : 𝒮.toGrp ⟶ M.group)
      (e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮 ≅ T),
      IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup j ∧
        M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iT := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  classical
  obtain ⟨j, hj, hgen⟩ := exists_isClosedSubgroup_genericTorusMap_eq M R K e iT hiT
    (fun t => by
      rw [mem_baseChange_self_coefficientIntegralPoints_iff]
      apply hb
      refine ⟨rationalPoints.map e.inv
        ((rationalCoeffEquiv K _).symm
          ((splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I K).symm
            (fun i => Units.map (algebraMap R K : R →* K) (t i)))), ?_, ?_⟩
      · exact map_characterValuationKernel_le v _
          ⟨_, rationalCoeffEquiv_symm_mem_characterValuationKernel K I v _
            (fun i => hv (t i)), rfl⟩
      · apply (rationalCoeffEquiv K G).injective
        rw [MulEquiv.apply_symm_apply]
        change rationalCoeffEquiv K G
          (rationalPoints.map iT (rationalPoints.map e.inv _)) = _
        rw [rationalCoeffEquiv_map, rationalCoeffEquiv_map, MulEquiv.apply_symm_apply,
          affinePointsTarget_apply, affinePointsTarget_apply, Category.assoc])
    (fun x hx => hx)
  exact ⟨torus R I, j, commIsoOfGroupIso (genericSplitIso R K I ≪≫ e.symm),
    isSplitTorus_torus I, hj, hgen⟩

end Closure

end Langlands.GroupScheme.IntegralModel.SplitTorusClosure
