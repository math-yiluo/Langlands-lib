import Langlands.Cohomology.Tate.TateComparisonProof
import Langlands.Cohomology.Tate.TateTheoremStatement
import Langlands.Cohomology.Tate.CupLawsProof
import Langlands.Cohomology.Tate.PositiveRestriction
import Langlands.Cohomology.Tate.ZeroProof
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Tate's cup-product theorem

The degree-two class is shifted down twice to an invariant vector `α` of `shiftUp (shiftUp A)`.
The boundary law of the tensor cup turns `a ∪ -` into the map induced by `k ↦ k • α` on the
trivial integral coefficient. On every Sylow subgroup this map is surjective in degree `-1`,
bijective in degree `0` and injective in degree `1`, so the comparison theorem applies.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

namespace TateTheorem

section General

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- An isomorphism of modules is bijective. -/
lemma bijective_hom {X Y : ModuleCat.{u} R} (e : X ≅ Y) : Function.Bijective e.hom :=
  e.toLinearEquiv.bijective

omit [Fintype G] in
/-- The scalar pairing is the right unitor of the tensor product. -/
lemma scalarPairing_lift (A : Rep.{u} R G) :
    TensorProduct.lift (scalarPairing A).bilinear = (TensorProduct.rid R A).toLinearMap :=
  TensorProduct.ext' fun a r => by
    rw [TensorProduct.lift.tmul]
    rfl

instance scalarPairing_tensorHom_isIso (A : Rep.{u} R G) :
    IsIso (scalarPairing A).tensorHom := by
  have hbij : Function.Bijective (scalarPairing A).tensorHom.hom := by
    change Function.Bijective (TensorProduct.lift (scalarPairing A).bilinear)
    rw [scalarPairing_lift]
    exact (TensorProduct.rid R A).bijective
  have : Mono (scalarPairing A).tensorHom := (Rep.mono_iff_injective _).mpr hbij.1
  have : Epi (scalarPairing A).tensorHom := (Rep.epi_iff_surjective _).mpr hbij.2
  exact isIso_of_mono_of_epi _

/-- Cup product with a shifted class is bijective once cup product with the class before
the shift is bijective. -/
lemma tensorCup_shiftUp_bijective (A B : Rep.{u} R G) (p q : ℤ)
    (x : tateCohomology (shiftUp A) p)
    (h : Function.Bijective (tensorCup (shiftUp A) B p q x)) :
    Function.Bijective (tensorCup A B (p + 1) q ((shiftUpIso A p).hom x)) := by
  have hB := scalarSplit_tensorRight_shortExact (shiftUpSequence A)
    (shiftUpSequence_scalarSplitting A) B
  have key : ⇑(tensorCup A B (p + 1) q ((shiftUpIso A p).hom x)) =
      (tateDegreeIso (A ⊗ B) (show (p + q) + 1 = (p + 1) + q by omega)).hom ∘
        (tensorShiftUpLeftIso A B (p + q)).hom ∘ tensorCup (shiftUp A) B p q x :=
    funext fun b => (cupLaws.{u} R G).2.2.2.1 (shiftUpSequence A)
      (shiftUpSequence_shortExact A) B hB p q x b
  rw [key]
  exact (bijective_hom _).comp ((bijective_hom _).comp h)

/-- Cup product with the class of an invariant vector is bijective once the induced
coefficient map is bijective. -/
lemma tensorCup_zeroClass_bijective (A B : Rep.{u} R G) (q : ℤ) (a : A.ρ.invariants)
    (h : Function.Bijective ((tateCohomologyFunctor q).map (tensorInvariantLeft A B a))) :
    Function.Bijective (tensorCup A B 0 q (zeroClass A a)) := by
  have key : ⇑(tensorCup A B 0 q (zeroClass A a)) =
      (tateDegreeIso (A ⊗ B) (show q = 0 + q by omega)).hom ∘
        (tateCohomologyFunctor q).map (tensorInvariantLeft A B a) :=
    funext fun b => tensorCup_invariantLeft A B q a b
  rw [key]
  exact (bijective_hom _).comp h

/-- Composing with an isomorphism of coefficients does not change bijectivity. -/
lemma map_bijective_of_comp {X Y Z : Rep.{u} R G} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] (n : ℤ)
    (h : Function.Bijective ((tateCohomologyFunctor n).map (f ≫ g))) :
    Function.Bijective ((tateCohomologyFunctor n).map f) := by
  have key : ⇑((tateCohomologyFunctor n).map (f ≫ g)) =
      ⇑((tateCohomologyFunctor n).map g) ∘ ⇑((tateCohomologyFunctor n).map f) := by
    rw [Functor.map_comp]
    rfl
  rw [key] at h
  exact (Function.Bijective.of_comp_iff'
    (bijective_hom ((tateCohomologyFunctor n).mapIso (asIso g))) _).mp h

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- Restriction in degree two of a twice shifted class, through the restricted shifts. -/
lemma restriction_two_shiftUp (A : Rep.{u} R G) (z : tateCohomology (shiftUp (shiftUp A)) 0) :
    restriction H A 2 ((shiftUpIso A 1).hom ((shiftUpIso (shiftUp A) 0).hom z)) =
      (restrictedShiftUpIso H A 1).hom ((restrictedShiftUpIso H (shiftUp A) 0).hom
        (restrictionZero H (shiftUp (shiftUp A)) z)) := by
  change (restrictedShiftUpIso H A 1).hom ((restrictedShiftUpIso H (shiftUp A) 0).hom
    (restrictionZero H (shiftUp (shiftUp A)) ((shiftUpIso (shiftUp A) 0).inv
      ((shiftUpIso A 1).inv ((shiftUpIso A 1).hom ((shiftUpIso (shiftUp A) 0).hom z)))))) = _
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]

/-- Restriction in degree two is the restriction of ordinary cohomology. -/
lemma restriction_two_apply (A : Rep.{u} R G) (x : tateCohomology A 2) :
    restriction H A 2 x =
      ((TateCohomology.isoGroupCohomology 2).app (Rep.res H.subtype A)).inv
        (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 2
          (((TateCohomology.isoGroupCohomology 2).app A).hom x)) :=
  ConcreteCategory.congr_hom (restriction_groupCohomology H A 2) x

end General

section Integral

/-- A finite group has no nonzero homomorphisms to the integers. -/
lemma integral_addMonoidHom_subsingleton (P : Type u) [Group P] [Fintype P] :
    Subsingleton (Additive P →+ IntegralScalar.{u}) := by
  have := PGroupVanishing.integralScalar_isAddTorsionFree.{u}
  have h0 : ∀ f : Additive P →+ IntegralScalar.{u}, f = 0 := by
    intro f
    refine AddMonoidHom.ext fun x => ?_
    rw [AddMonoidHom.zero_apply]
    have hn : Fintype.card (Additive P) • f x =
        Fintype.card (Additive P) • (0 : IntegralScalar.{u}) := by
      rw [← map_nsmul, card_nsmul_eq_zero, map_zero, smul_zero]
    exact nsmul_right_injective Fintype.card_ne_zero hn
  exact ⟨fun f g => (h0 f).trans (h0 g).symm⟩

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
/-- Every degree-zero class of the trivial integral coefficient is a multiple of the class
of `1`. -/
lemma zeroClass_trivial_multiple {P : Type u} [Group P] [Fintype P] (φ : P →* G)
    (h1 : (1 : IntegralScalar.{u}) ∈
      (Rep.res φ (Rep.trivial IntegralScalar.{u} G IntegralScalar.{u})).ρ.invariants)
    (v : tateCohomology (Rep.res φ (Rep.trivial IntegralScalar.{u} G IntegralScalar.{u})) 0) :
    ∃ k : ℤ, v = k • zeroClass _ ⟨1, h1⟩ := by
  obtain ⟨b, rfl⟩ := zeroClass_surjective _ v
  refine ⟨ULift.down (b : IntegralScalar.{u}), ?_⟩
  rw [← map_zsmul]
  congr 1
  apply Subtype.ext
  apply ULift.ext
  change (b : IntegralScalar.{u}).down = (b : IntegralScalar.{u}).down * 1
  rw [mul_one]

/-- A degree-zero map from a cyclic group of order `|P|` onto a group of order `|P|`
generated by the image of a generator is bijective. -/
lemma bijective_zero_of_generator {P : Type u} [Group P] [Fintype P]
    {T X : Rep.{u} IntegralScalar.{u} P} (f : T ⟶ X) {M : Type u} [AddCommGroup M]
    (Ψ : tateCohomology X 0 →+ M) (hΨ : Function.Injective Ψ) (z : tateCohomology T 0)
    (hz : ∀ v : tateCohomology T 0, ∃ k : ℤ, v = k • z)
    (hgen : AddSubgroup.zmultiples (Ψ ((tateCohomologyFunctor 0).map f z)) = ⊤)
    (hcard : Nat.card M = Nat.card P) :
    Function.Bijective ((tateCohomologyFunctor 0).map f) := by
  have horder : addOrderOf (Ψ ((tateCohomologyFunctor 0).map f z)) = Fintype.card P := by
    rw [← Nat.card_zmultiples, hgen, AddSubgroup.card_top, hcard, Nat.card_eq_fintype_card]
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    obtain ⟨k, rfl⟩ := hz v
    have hk : k • Ψ ((tateCohomologyFunctor 0).map f z) = 0 := by
      have : Ψ ((tateCohomologyFunctor 0).map f (k • z)) = 0 := by rw [hv, map_zero]
      rwa [map_zsmul, map_zsmul] at this
    obtain ⟨j, rfl⟩ := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk
    rw [horder, mul_comm, mul_smul, natCast_zsmul, PGroupVanishing.card_smul_eq_zero,
      smul_zero]
  · intro w
    have hw : Ψ w ∈ AddSubgroup.zmultiples (Ψ ((tateCohomologyFunctor 0).map f z)) := by
      rw [hgen]
      exact AddSubgroup.mem_top _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
    refine ⟨k • z, hΨ ?_⟩
    rw [map_zsmul, map_zsmul, hk]

end Integral

end TateTheorem

open TateTheorem in
/-- Serre, *Local Fields*, IX §8, Theorem 14 (the case `B = ℤ`, i.e. Theorem 13 with
`q = 2`): cup product with a degree-two class satisfying Tate's conditions on every Sylow
subgroup is bijective in every integer Tate degree. -/
theorem tateCupIsomorphism : TateCupIsomorphism.{u} := by
  intro G _ _ A a ha n
  obtain ⟨aT, rfl⟩ : ∃ aT : tateCohomology A 2,
      ((TateCohomology.isoGroupCohomology 2).app A).hom aT = a :=
    ⟨_, Iso.inv_hom_id_apply _ _⟩
  obtain ⟨a₁, rfl⟩ : ∃ a₁ : tateCohomology (shiftUp A) 1, (shiftUpIso A 1).hom a₁ = aT :=
    ⟨_, Iso.inv_hom_id_apply _ _⟩
  obtain ⟨y, rfl⟩ : ∃ y : tateCohomology (shiftUp (shiftUp A)) 0,
      (shiftUpIso (shiftUp A) 0).hom y = a₁ :=
    ⟨_, Iso.inv_hom_id_apply _ _⟩
  obtain ⟨α, rfl⟩ := zeroClass_surjective _ y
  let B : Rep.{u} IntegralScalar.{u} G := Rep.trivial IntegralScalar.{u} G IntegralScalar.{u}
  let μ : B ⟶ shiftUp (shiftUp A) ⊗ B := tensorInvariantLeft (shiftUp (shiftUp A)) B α
  let μ' : B ⟶ shiftUp (shiftUp A) := μ ≫ (scalarPairing (shiftUp (shiftUp A))).tensorHom
  have hμ' : ∀ k : ℤ, Function.Bijective ((tateCohomologyFunctor k).map μ') := by
    refine tateComparison G B (shiftUp (shiftUp A)) μ' fun p hp P _ => ?_
    obtain ⟨hH1, hcard, hgen⟩ := ha p hp P
    let _ : Fintype (G ⧸ P.1) := Fintype.ofFinite _
    refine ⟨-1, ?_, ?_, ?_⟩
    · -- Degree `-1`: the target is `H¹(P, A)`, which vanishes.
      have hsub : Subsingleton
          (tateCohomology (Rep.res P.1.subtype (shiftUp (shiftUp A))) (-1)) :=
        @Equiv.subsingleton _ _ (restrictedShiftUpIso P.1 (shiftUp A) (-1) ≪≫
          tateDegreeIso _ (show (-1 : ℤ) + 1 = 0 by norm_num) ≪≫
          restrictedShiftUpIso P.1 A 0 ≪≫
          (TateCohomology.isoGroupCohomology 1).app (Rep.res P.1.subtype A)).toLinearEquiv.toEquiv
          hH1
      intro w
      exact ⟨0, @Subsingleton.elim _ hsub _ _⟩
    · -- Degree `0`: `ℤ/|P|` maps onto the cyclic group `H²(P, A)` of order `|P|`.
      rw [show (-1 : ℤ) + 1 = 0 by norm_num]
      let Ψ : tateCohomology (Rep.res P.1.subtype (shiftUp (shiftUp A))) 0 ≃ₗ[IntegralScalar.{u}]
          groupCohomology (Rep.res P.1.subtype A) 2 :=
        ((restrictedShiftUpIso P.1 (shiftUp A) 0).toLinearEquiv.trans
          (restrictedShiftUpIso P.1 A 1).toLinearEquiv).trans
          ((TateCohomology.isoGroupCohomology 2).app (Rep.res P.1.subtype A)).toLinearEquiv
      have h1 : (1 : IntegralScalar.{u}) ∈ (Rep.res P.1.subtype B).ρ.invariants :=
        (Representation.mem_invariants _ _).mpr fun _ => rfl
      have hf0 : (tateCohomologyFunctor 0).map ((Rep.resFunctor P.1.subtype).map μ')
          (zeroClass (Rep.res P.1.subtype B) ⟨1, h1⟩) =
            restrictionZero P.1 (shiftUp (shiftUp A)) (zeroClass _ α) := by
        rw [restrictionZero_zeroClass, zeroClass_naturality]
        congr 1
        apply Subtype.ext
        change TensorProduct.lift (scalarPairing (shiftUp (shiftUp A))).bilinear
          ((α : shiftUp (shiftUp A)) ⊗ₜ[IntegralScalar.{u}] (1 : IntegralScalar.{u})) = _
        rw [scalarPairing_lift, LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul]
        rfl
      have hz₁ : Ψ ((tateCohomologyFunctor 0).map ((Rep.resFunctor P.1.subtype).map μ')
          (zeroClass (Rep.res P.1.subtype B) ⟨1, h1⟩)) =
            groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) 2
              (((TateCohomology.isoGroupCohomology 2).app A).hom
                ((shiftUpIso A 1).hom ((shiftUpIso (shiftUp A) 0).hom (zeroClass _ α)))) := by
        rw [hf0]
        change ((TateCohomology.isoGroupCohomology 2).app (Rep.res P.1.subtype A)).hom
          ((restrictedShiftUpIso P.1 A 1).hom ((restrictedShiftUpIso P.1 (shiftUp A) 0).hom
            (restrictionZero P.1 (shiftUp (shiftUp A)) (zeroClass _ α)))) = _
        rw [← restriction_two_shiftUp, restriction_two_apply]
        exact Iso.inv_hom_id_apply _ _
      refine bijective_zero_of_generator ((Rep.resFunctor P.1.subtype).map μ')
        Ψ.toLinearMap.toAddMonoidHom Ψ.injective (zeroClass (Rep.res P.1.subtype B) ⟨1, h1⟩)
        (zeroClass_trivial_multiple P.1.subtype h1) ?_ hcard
      change AddSubgroup.zmultiples (Ψ _) = ⊤
      rw [hz₁]
      exact hgen
    · -- Degree `1`: the source `Hom(P, ℤ)` vanishes.
      rw [show (-1 : ℤ) + 2 = 1 by norm_num]
      have : (Rep.res P.1.subtype B).IsTrivial := ⟨fun _ => rfl⟩
      have hsub : Subsingleton (tateCohomology (Rep.res P.1.subtype B) 1) :=
        @Equiv.subsingleton _ _ ((TateCohomology.isoGroupCohomology 1).app
          (Rep.res P.1.subtype B) ≪≫
            groupCohomology.H1IsoOfIsTrivial (Rep.res P.1.subtype B)).toLinearEquiv.toEquiv
          (integral_addMonoidHom_subsingleton P.1)
      intro v w _
      exact @Subsingleton.elim _ hsub _ _
  have h0 : Function.Bijective (tensorCup (shiftUp (shiftUp A)) B 0 n (zeroClass _ α)) :=
    tensorCup_zeroClass_bijective _ B n α (map_bijective_of_comp μ _ n (hμ' n))
  have h1 := tensorCup_shiftUp_bijective (shiftUp A) B 0 n _ h0
  have h2 := tensorCup_shiftUp_bijective A B 1 n _ h1
  have key : ⇑(integralH2Cup A n (((TateCohomology.isoGroupCohomology 2).app A).hom
      ((shiftUpIso A 1).hom ((shiftUpIso (shiftUp A) 0).hom (zeroClass _ α))))) =
      (tateDegreeIso A (add_comm 2 n)).hom ∘
        (tateCohomologyFunctor (2 + n)).map (scalarPairing A).tensorHom ∘
          tensorCup A B 2 n (((TateCohomology.isoGroupCohomology 2).app A).inv
            (((TateCohomology.isoGroupCohomology 2).app A).hom
              ((shiftUpIso A 1).hom ((shiftUpIso (shiftUp A) 0).hom (zeroClass _ α))))) :=
    rfl
  rw [key, Iso.hom_inv_id_apply]
  exact (bijective_hom _).comp
    ((bijective_hom ((tateCohomologyFunctor (2 + n)).mapIso
      (asIso (scalarPairing A).tensorHom))).comp h2)

end Langlands.Tate
