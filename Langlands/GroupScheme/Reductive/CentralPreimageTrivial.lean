import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.IdentityComponentRationalQuotient
import Langlands.GroupScheme.ImageGenerationCommutator
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Adjoint.CenterQuotientCommutator
import Langlands.GroupScheme.HomogeneousClosedImmersion
import Langlands.GroupScheme.Rational.CharacteristicZeroPointFactors
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Unipotent.TorusHom
import Langlands.GroupScheme.Rational.PositiveCharacteristicTorusPower
import Langlands.GroupScheme.Rational.UnipotentTorsionCenter
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Absolute.CharacterCocharacter
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Central subgroups and finiteness of rational points -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralQuotient

section Finite

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A smooth connected affine group over an algebraically closed field with finitely many
rational points is trivial: its closed points are finite, so the Jacobson space is discrete
and, being connected, a single point. -/
theorem id_eq_one_of_finite_rationalPoints (Z : GroupScheme (Spec (CommRingCat.of K)))
    [Smooth Z.X.hom] [IsAffineHom Z.X.hom] [ConnectedSpace Z.X.left]
    [Finite (rationalPoints Z)] : 𝟙 Z.X = (1 : Z.X ⟶ Z.X) := by
  have : JacobsonSpace Z.X.left := LocallyOfFiniteType.jacobsonSpace Z.X.hom
  have hfin : (closedPoints Z.X.left).Finite := by
    refine (Set.finite_range fun x : rationalPoints Z =>
      x.left (IsLocalRing.closedPoint K)).subset ?_
    intro c hc
    exact ⟨Over.homMk (pointOfClosedPoint Z.X.hom c hc) (by simp), by simp⟩
  have : DiscreteTopology Z.X.left := JacobsonSpace.discreteTopology hfin
  have hsub : Subsingleton Z.X.left :=
    Set.subsingleton_univ_iff.mp (isPreconnected_univ.subsingleton)
  have : IsReduced Z.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K
      Z.X.left Z.X.hom
  refine hom_ext_rationalPoints fun z => ?_
  rw [Category.comp_id, MonObj.comp_one]
  exact rationalPoint_ext (Subsingleton.elim _ _)

end Finite

section Index

/-- A homomorphism whose restriction to a subgroup of finite index has finite image has
finite image. -/
theorem finite_range_of_finite_map {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (Γ : Subgroup G) [Γ.FiniteIndex] (hΓ : Finite (Γ.map φ)) : Finite φ.range := by
  let ψ : G →* φ.range := φ.rangeRestrict
  have hψ : Function.Surjective ψ := φ.rangeRestrict_surjective
  have hidx : (Γ.map ψ).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd Γ hψ)
  have hfin : Finite (Γ.map ψ) := by
    let e : Γ.map ψ → Γ.map φ := fun y => ⟨(y : φ.range), by
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact Subgroup.mem_map.mpr ⟨x, hx, by rw [← hxy]; rfl⟩⟩
    refine Finite.of_injective e ?_
    intro y y' h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ.map φ => (z : H)) h))
  have hcard := Subgroup.card_mul_index (Γ.map ψ)
  have hpos : Nat.card (Γ.map ψ) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  exact Nat.finite_of_card_ne_zero (by rw [← hcard]; exact mul_ne_zero hpos hidx)

end Index

section Points

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Lemma F.** For an affine group `S` locally of finite type over an algebraically closed
field, the rational points of the identity component of the reduced subgroup `S_red`, pushed into
`S(K)`, form a subgroup of finite index. -/
theorem finiteIndex_map_rationalIdentitySubgroup (S : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom S.X.hom] [LocallyOfFiniteType S.X.hom] :
    letI : Smooth (reducedSubgroup S).X.hom := ReducedSubgroup.smooth_reducedSubgroup S
    letI : IsAffineHom (reducedSubgroup S).X.hom := ReducedSubgroup.isAffineHom_reducedSubgroup S
    ((IdentityComponent.rationalIdentitySubgroup (reducedSubgroup S)).map
      (rationalPoints.map (reducedSubgroupι S))).FiniteIndex := by
  have : Smooth (reducedSubgroup S).X.hom := ReducedSubgroup.smooth_reducedSubgroup S
  have : IsAffineHom (reducedSubgroup S).X.hom := ReducedSubgroup.isAffineHom_reducedSubgroup S
  have h1 : (IdentityComponent.rationalIdentitySubgroup (reducedSubgroup S)).FiniteIndex := by
    have : Finite (_ ⧸ IdentityComponent.rationalIdentitySubgroup (reducedSubgroup S)) :=
      IdentityComponent.finite_rationalComponentQuotient (reducedSubgroup S)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsurj : Function.Surjective (rationalPoints.map (reducedSubgroupι S)) := by
    intro x
    have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of K)))).left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
    exact ⟨ReducedSubgroup.liftOver x, ReducedSubgroup.liftOver_fac x⟩
  exact ⟨ne_zero_of_dvd_ne_zero h1.index_ne_zero (Subgroup.index_map_dvd _ hsurj)⟩

/-- **Lemma C.** Over an algebraically closed field, a homomorphism of smooth groups with
affine target whose rational points all land in the centre is central: its commutator
morphism is trivial on rational points of the reduced product, hence trivial. -/
theorem isCentral_of_rationalPoints {M G : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth M.X.hom] [Smooth G.X.hom] [IsAffineHom G.X.hom] (m : M ⟶ G)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ M.X,
      x ≫ m.hom.hom ∈ (center G).carrier _) : IsCentral m := by
  have : Smooth (M.X ⊗ G.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IsReduced (M.X ⊗ G.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K
      (M.X ⊗ G.X).left (M.X ⊗ G.X).hom
  have hc : commutatorMap m (𝟙 G) = 1 := by
    refine hom_ext_rationalPoints fun z => ?_
    rw [MonObj.comp_one, commutatorMap_points, Grp.id_hom_hom, Category.comp_id]
    have hz := commute_of_mem_center (h (z ≫ fst M.X G.X)) (z ≫ snd M.X G.X)
    rw [hz.eq, mul_inv_cancel_right, mul_inv_cancel]
  intro T x T' a g
  have h1 := commutatorMap_lift m (𝟙 G) (a ≫ x) g
  rw [hc, MonObj.comp_one, Grp.id_hom_hom, Category.comp_id, Category.assoc] at h1
  have h2 := mul_inv_eq_one.mp h1.symm
  exact mul_inv_eq_iff_eq_mul.mp h2

end Points

section CharZero

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] [CharZero K]

/-- **Lemma D, characteristic zero.** A central smooth connected closed subgroup `M` of a smooth
affine group with trivial unipotent radical is killed on rational points by every homomorphism
to an affine unipotent group: each rational point of `M` is a torus point times a point of an
additive line, the line is central unipotent hence trivial, and the torus maps trivially. -/
theorem map_eq_one_of_isCentral_charZero {M G Z : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m)
    [IsAffineHom Z.X.hom] (hZ : IsUnipotent Z) (p : M ⟶ Z) (x : rationalPoints M) :
    rationalPoints.map p x = 1 := by
  have : Smooth hm.commGroupScheme.X.hom := inferInstanceAs (Smooth M.X.hom)
  have : IsAffineHom hm.commGroupScheme.X.hom := inferInstanceAs (IsAffineHom M.X.hom)
  have : ConnectedSpace hm.commGroupScheme.X.left := inferInstanceAs (ConnectedSpace M.X.left)
  obtain ⟨T, i, t, φ, hT, -, hx⟩ := characteristicZeroPointFactors K hm.commGroupScheme x
  have hV : RelativeRoot.IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of K) 1) 1 :=
    ⟨VectorGroup.coordinates (CommRingCat.of K) 1, VectorGroup.isNaturalVectorCoordinates⟩
  let := hV.isAffineHom
  let := hV.smooth
  let := hV.connectedSpace
  have hφm : (φ ≫ m).hom.hom = 1 :=
    CenterQuotient.hom_eq_one_of_isCentral hG (φ ≫ m) (VectorGroup.isUnipotent K 1) (hm.comp φ)
  have hφ : φ.hom.hom = 1 := by
    apply (cancel_mono m.hom.hom).1
    rw [← Grp.comp_hom_hom, hφm, MonObj.one_comp]
  have hip : i ≫ p = 0 := hT.hom_eq_zero_of_isUnipotent hZ (i ≫ p)
  change rationalPoints.map p x = 1
  rw [hx, map_mul, rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
    rationalPoints.map_apply, hφ, MonObj.comp_one, MonObj.one_comp, mul_one, Category.assoc,
    ← Grp.comp_hom_hom, hip]
  exact MonObj.comp_one _

end CharZero

section Torsion

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A smooth connected group `E` with a closed embedding into `M`, all of whose points are
killed by `n ≠ 0` in `M`, embeds trivially, when `M` is a central closed subgroup of a smooth
affine group with trivial unipotent radical: every point of `𝔾_m` is an `n`-th power, so `E`
has no cocharacters, hence is unipotent; being central, it is trivial. -/
theorem hom_eq_one_of_pow_eq_one {M G E : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [IsAffineHom M.X.hom] (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m)
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    (j : E ⟶ M) [Mono j.hom.hom] (n : ℕ) (hn : n ≠ 0)
    (hjn : ∀ (T : Over (Spec (CommRingCat.of K))) (y : T ⟶ E.X), (y ≫ j.hom.hom) ^ n = 1) :
    j.hom.hom = 1 := by
  have hjc : IsCentral (j ≫ m) := hm.comp j
  have : Mono (j ≫ m).hom.hom := by
    change Mono (j.hom.hom ≫ m.hom.hom)
    infer_instance
  have : IsCommMonObj E.X := hjc.isCommMonObj
  have hgm : ∀ φ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ E, φ = 0 := by
    intro φ
    have hT : IsTorus (Gm (Spec (CommRingCat.of K))).toGrp := isSplitTorus_gm.isTorus
    have : Smooth (Gm (Spec (CommRingCat.of K))).toGrp.X.hom := hT.smooth
    have : IsReduced (Gm (Spec (CommRingCat.of K))).toGrp.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _
        (Gm (Spec (CommRingCat.of K))).toGrp.X.hom
    have hsurj := (hT.flat_and_surjective_multiplication (n := (n : ℤ))
      (by exact_mod_cast hn)).2
    have hφj : (φ ≫ j).hom.hom = 1 := by
      refine hom_ext_rationalPoints fun g => ?_
      obtain ⟨h, hh⟩ := HomogeneousClosedImmersion.exists_rational_lift
        (multiplication (Gm (Spec (CommRingCat.of K))).toGrp (n : ℤ)).hom.hom g
        (hsurj.surj _)
      rw [PowerImage.points_multiplication_nat] at hh
      rw [MonObj.comp_one, ← hh, MonObj.pow_comp, Grp.comp_hom_hom, ← Category.assoc]
      exact hjn _ _
    have hφ : φ.hom.hom = 1 := by
      apply (cancel_mono j.hom.hom).1
      rw [← Grp.comp_hom_hom, hφj, MonObj.one_comp]
    exact Grp.hom_ext _ _ (hφ.trans rfl)
  have hu : IsUnipotent E :=
    AbsoluteNoCocharacter.isUnipotent_of_gm_hom_eq_zero (isSolvableGroupScheme_of_isCommMonObj E)
      hgm
  have hjm : (j ≫ m).hom.hom = 1 := CenterQuotient.hom_eq_one_of_isCentral hG (j ≫ m) hu hjc
  apply (cancel_mono m.hom.hom).1
  rw [← Grp.comp_hom_hom, hjm, MonObj.one_comp]

/-- An affine group `E` of finite type with a closed embedding into `M`, all of whose points are
killed by `n ≠ 0` in `M`, has finitely many rational points, when `M` is a central closed
subgroup of a smooth affine group with trivial unipotent radical: the identity component of the
reduced subgroup of `E` embeds trivially and its rational points have finite index. -/
theorem finite_rationalPoints_of_pow_eq_one {M G E : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [IsAffineHom M.X.hom] (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m)
    [IsAffineHom E.X.hom] [LocallyOfFiniteType E.X.hom]
    (e : E ⟶ M) [Mono e.hom.hom] (n : ℕ) (hn : n ≠ 0)
    (hen : ∀ (T : Over (Spec (CommRingCat.of K))) (y : T ⟶ E.X), (y ≫ e.hom.hom) ^ n = 1) :
    Finite (rationalPoints E) := by
  have : Smooth (reducedSubgroup E).X.hom := ReducedSubgroup.smooth_reducedSubgroup E
  have : IsAffineHom (reducedSubgroup E).X.hom := ReducedSubgroup.isAffineHom_reducedSubgroup E
  have : Mono (reducedSubgroupι E).hom.hom := inferInstanceAs (Mono (ReducedSubgroup.redOverι E))
  have : Mono (identityComponentι (reducedSubgroup E) ≫ reducedSubgroupι E ≫ e).hom.hom := by
    change Mono ((identityComponentι (reducedSubgroup E)).hom.hom ≫
      (reducedSubgroupι E).hom.hom ≫ e.hom.hom)
    infer_instance
  have hj := hom_eq_one_of_pow_eq_one hG m hm
    (identityComponentι (reducedSubgroup E) ≫ reducedSubgroupι E ≫ e) n hn (fun T y => by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        hen T (y ≫ (identityComponentι (reducedSubgroup E)).hom.hom ≫
          (reducedSubgroupι E).hom.hom))
  have hbot : (IdentityComponent.rationalIdentitySubgroup (reducedSubgroup E)).map
      (rationalPoints.map (reducedSubgroupι E)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := (IdentityComponent.mem_rationalIdentitySubgroup (reducedSubgroup E) x).1 hx
    rw [Subgroup.mem_bot, rationalPoints.map_apply]
    apply (cancel_mono e.hom.hom).1
    have h := congrArg (fun z => y ≫ z) hj
    simp only [Grp.comp_hom_hom, MonObj.comp_one] at h
    rw [MonObj.one_comp, Category.assoc, Category.assoc, h]
  have hfi := finiteIndex_map_rationalIdentitySubgroup E
  rw [hbot] at hfi
  have h := hfi.index_ne_zero
  rw [Subgroup.index_bot] at h
  exact Nat.finite_of_card_ne_zero h

/-- **Torsion lemma.** Let `M` be a commutative affine group of finite type with a central
closed embedding into a smooth affine group with trivial unipotent radical. Then for `n ≠ 0`
only finitely many rational points of `M` are killed by `n`: they are the rational points of the
kernel of multiplication by `n`. -/
theorem finite_torsion_of_isCentral {M G : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom] [IsCommMonObj M.X]
    (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m) (n : ℕ) (hn : n ≠ 0) :
    {x : rationalPoints M | x ^ n = 1}.Finite := by
  have : IsAffineHom (kernel (multiplication M (n : ℤ))).X.hom := by
    rw [← (kernelι (multiplication M (n : ℤ))).hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType (kernel (multiplication M (n : ℤ))).X.hom := by
    rw [← (kernelι (multiplication M (n : ℤ))).hom.hom.w]
    infer_instance
  have : Finite (rationalPoints (kernel (multiplication M (n : ℤ)))) :=
    finite_rationalPoints_of_pow_eq_one hG m hm (kernelι (multiplication M (n : ℤ))) n hn
      (fun T y => by
        have hy : y ≫ (kernelι (multiplication M (n : ℤ))).hom.hom ∈
            (SubgroupFunctor.range (kernelι (multiplication M (n : ℤ)))).carrier T :=
          SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
        rwa [mem_range_kernelι_iff, PowerImage.points_multiplication_nat] at hy)
  refine (Set.finite_range (rationalPoints.map (kernelι (multiplication M (n : ℤ))))).subset ?_
  intro x hx
  have hx' : x ∈ (SubgroupFunctor.range (kernelι (multiplication M (n : ℤ)))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [mem_range_kernelι_iff, PowerImage.points_multiplication_nat]
    exact hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx'
  exact ⟨y, hy⟩

end Torsion

section CharP

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Lemma D, positive characteristic.** For a central smooth connected closed subgroup `M`
of a smooth affine group with trivial unipotent radical, every homomorphism to an affine
unipotent group has finite image on rational points: a uniform `p`-power `n` sends `M(K)` into
its central maximal torus, whose rational points are `n`-divisible, so each value is the value
of an `n`-torsion point. -/
theorem finite_range_of_isCentral_charP {M G Z : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m)
    [IsAffineHom Z.X.hom] (hZ : IsUnipotent Z) (π : M ⟶ Z)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (Set.range (rationalPoints.map π)).Finite := by
  have : IsCommMonObj M.X := hm.isCommMonObj
  let D := (isNilpotentGroupScheme_of_isCommMonObj M).centralTorusQuotient
  let : Smooth D.quotient.X.hom := D.smooth_quotient
  let : IsAffineHom D.quotient.X.hom := D.affine_quotient
  let : ConnectedSpace D.quotient.X.left := D.connected_quotient
  have hu : IsUnipotent D.quotient :=
    D.nilpotent_quotient.isUnipotent_of_no_torus D.no_tori
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hu
  have hn : p ^ r ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hT : IsTorus D.torus.toGrp := D.maximal_torus.1
  have : Smooth D.torus.toGrp.X.hom := hT.smooth
  have hsurj := (hT.flat_and_surjective_multiplication (n := ((p ^ r : ℕ) : ℤ))
    (by exact_mod_cast hn)).2
  have hiπ : D.inclusion ≫ π = 0 := hT.hom_eq_zero_of_isUnipotent hZ (D.inclusion ≫ π)
  refine ((finite_torsion_of_isCentral hG m hm (p ^ r) hn).image
    (rationalPoints.map π)).subset ?_
  rintro _ ⟨x, rfl⟩
  have hmem : x ^ (p ^ r) ∈ (SubgroupFunctor.range D.inclusion).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [← D.fppf_quotient.2.2.2, mem_range_kernelι_iff, MonObj.pow_comp]
    exact hr _ (x ≫ D.projection.hom.hom)
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.1 hmem
  obtain ⟨s, hs⟩ := HomogeneousClosedImmersion.exists_rational_lift
    (multiplication D.torus.toGrp ((p ^ r : ℕ) : ℤ)).hom.hom t (hsurj.surj _)
  rw [PowerImage.points_multiplication_nat] at hs
  have h1 : rationalPoints.map π (rationalPoints.map D.inclusion s) = 1 := by
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      hiπ]
    exact MonObj.comp_one s
  refine ⟨x * (rationalPoints.map D.inclusion s)⁻¹, ?_, ?_⟩
  · show (x * (rationalPoints.map D.inclusion s)⁻¹) ^ (p ^ r) = 1
    rw [mul_pow, inv_pow, ← map_pow, rationalPoints.map_apply, hs, ht, mul_inv_cancel]
  · rw [map_mul, map_inv, h1, inv_one, mul_one]

end CharP

section LemmaD

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Lemma D.** A central smooth connected closed subgroup `M` of a smooth affine group with
trivial unipotent radical has finite image on rational points under every homomorphism to an
affine unipotent group. -/
theorem finite_range_of_isCentral {M G Z : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    (m : M ⟶ G) [Mono m.hom.hom] (hm : IsCentral m)
    [IsAffineHom Z.X.hom] (hZ : IsUnipotent Z) (π : M ⟶ Z) :
    (Set.range (rationalPoints.map π)).Finite := by
  rcases CharP.exists' K with h0 | ⟨p, hp, hc⟩
  · refine (Set.finite_singleton 1).subset ?_
    rintro _ ⟨x, rfl⟩
    exact map_eq_one_of_isCentral_charZero hG m hm hZ π x
  · exact finite_range_of_isCentral_charP hG m hm hZ π p

end LemmaD

end Langlands.GroupScheme.CentralQuotient
