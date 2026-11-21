import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.CharacterRestrictionRealDual
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # Existence of the group data of the system `Ξ_main` (Bernstein–Lapid §7.2)

For a connected reductive group `G` over a number field `F`, a maximal split torus
`iT : T → G` and a generic cocharacter `ν`, this module constructs group data `u`, `t`, `z`
of `Ξ_main` in the sense of `IsLocalFinitenessGroupData`:

* `u α` is the closed dynamic unipotent subgroup scheme of a standard cocharacter of
  `Δ₀ \ {α}`, which represents the standard unipotent radical of the maximal parabolic `P_α`;
* `t α` is the positive real point of `T(𝔸)` with logarithm the fundamental coweight `ϖ^∨_α`;
* the `z j` are positive real points of the split component `A_G`, pushed into `T`, whose
  logarithms form a basis of `𝔞_G`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

section Positive

variable {F : Type u} [Field F] [NumberField F] {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The normalized logarithm of the idele norm of the positive scalar idele of `x > 0` is
`[F : ℚ] log x`. -/
theorem log_absoluteValue_positiveRealIdele (x : ℝ≥0ˣ) :
    Real.log ((IdeleAbsoluteValue.full F (PositiveRealIdeles.full F x) : ℝ≥0) : ℝ) =
      (Module.finrank ℚ F : ℝ) * Real.log ((x : ℝ≥0) : ℝ) := by
  rw [PositiveRealIdeles.absoluteValue_full]
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow]

/-- At a point of the positive real subgroup `A_T` of `T(𝔸)`, every character takes the value
of a positive scalar idele `x`, and its normalized logarithm is `[F : ℚ] log x`. -/
theorem exists_positiveReal_characterValue {g : AdelicGroupPoints F T.toGrp}
    (hg : g ∈ PositiveRealTorus.intrinsicSubgroup F T) (χ : characterLattice T) :
    ∃ x : ℝ≥0ˣ, PositiveRealIdeles.full F x = Lie.characterValue χ g ∧
      characterLog F T.toGrp g χ = (Module.finrank ℚ F : ℝ) * Real.log ((x : ℝ≥0) : ℝ) := by
  obtain ⟨x, hx⟩ := (PositiveRealTorus.mem_intrinsicSubgroup_iff F T g).1 hg χ
  refine ⟨x, hx, ?_⟩
  rw [PositiveRealTorus.characterLog_eq_log_characterValue, ← hx,
    log_absoluteValue_positiveRealIdele]

/-- A character with vanishing logarithm at a point of `A_T` takes the value `1` there. -/
theorem characterValue_eq_one_of_characterLog_eq_zero {g : AdelicGroupPoints F T.toGrp}
    (hg : g ∈ PositiveRealTorus.intrinsicSubgroup F T) {χ : characterLattice T}
    (h : characterLog F T.toGrp g χ = 0) : Lie.characterValue χ g = 1 := by
  obtain ⟨x, hx, hlog⟩ := exists_positiveReal_characterValue hg χ
  have hl : Real.log ((x : ℝ≥0) : ℝ) = 0 := by
    rw [h] at hlog
    rcases mul_eq_zero.1 hlog.symm with h0 | h0
    · exact absurd h0 (PositiveRealTorus.degree_pos F).ne'
    · exact h0
  have hx1 : x = 1 := by
    apply Units.ext
    apply NNReal.eq
    exact Real.eq_one_of_pos_of_log_eq_zero
      (by exact_mod_cast pos_iff_ne_zero.mpr x.ne_zero) hl
  rw [← hx, hx1, map_one]

/-- A character with positive logarithm at a point of `A_T` takes there the value of the
positive scalar idele of a real `x > 1`. -/
theorem exists_one_lt_of_characterLog_pos {g : AdelicGroupPoints F T.toGrp}
    (hg : g ∈ PositiveRealTorus.intrinsicSubgroup F T) {χ : characterLattice T}
    (h : 0 < characterLog F T.toGrp g χ) :
    ∃ x : ℝ≥0ˣ, 1 < (x : ℝ≥0) ∧ PositiveRealIdeles.full F x = Lie.characterValue χ g := by
  obtain ⟨x, hx, hlog⟩ := exists_positiveReal_characterValue hg χ
  refine ⟨x, ?_, hx⟩
  have hl : 0 < Real.log ((x : ℝ≥0) : ℝ) := by
    rw [hlog] at h
    exact pos_of_mul_pos_right h (PositiveRealTorus.degree_pos F).le
  have hx1 : (1 : ℝ) < ((x : ℝ≥0) : ℝ) := by
    by_contra hle
    exact absurd hl (not_lt.2 (Real.log_nonpos (x : ℝ≥0).2 (not_lt.1 hle)))
  exact_mod_cast hx1

/-- The real character functional `χ ↦ ⟨χ, v⟩` of a real cocharacter `v ∈ 𝔞_T = X_*(T) ⊗ ℝ`. -/
def cocharacterDual (v : V T) : RealCharacterDual F T.toGrp :=
  (((pair T).flip v).toAddMonoidHom.comp
    (TensorProduct.mk ℤ ℝ (characterLattice T) 1).toAddMonoidHom : characterLattice T →+ ℝ)

omit [NumberField F] in
theorem cocharacterDual_apply (v : V T) (χ : characterLattice T) :
    cocharacterDual (F := F) v χ = pair T ((1 : ℝ) ⊗ₜ[ℤ] χ) v := rfl

end Positive

section GroupData

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

omit [NumberField F] in
/-- The unipotent radicals `U_α` of the maximal standard parabolics `P_α`: for every simple
root `α`, a closed subgroup scheme of `G` whose functor of points is
`standardUnipotent iT ν (Δ₀ \ {α})`. It is the dynamic unipotent subgroup of a standard
cocharacter of `Δ₀ \ {α}`. -/
theorem exists_closed_standardUnipotent_maximal [IsAffine G.X.left] (hG : IsConnectedReductive G)
    {iT : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus iT) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter iT ν) :
    ∃ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
      (_ : ∀ α, IsAffine (Ua α).X.left) (u : ∀ α, Ua α ⟶ G)
      (_ : ∀ α, IsClosedImmersion (u α).hom.hom.left),
      ∀ α, SubgroupFunctor.range (u α) =
        standardUnipotent iT ν (simpleRelativeRoots iT ν \ {α.1}) := by
  have := hi.isSplitSubtorus.mono
  have hstd := fun α : simpleRelativeRoots iT ν =>
    standardCocharacter F G hG T iT hi ν hν (simpleRelativeRoots iT ν \ {α.1}) Set.sdiff_subset
  choose ζ hζ using fun α => (hstd α).1
  refine ⟨fun α => Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom (ζ α) ≫ iT),
    fun α => ?_, fun α => Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom (ζ α) ≫ iT),
    fun α => Dynamic.Affine.isClosedSubgroup_unipotentHom _, fun α => ?_⟩
  · have : IsClosedImmersion
        (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom (ζ α) ≫ iT)).hom.hom.left :=
      Dynamic.Affine.isClosedSubgroup_unipotentHom _
    exact isAffine_of_isAffineHom
      (f := (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom (ζ α) ≫ iT)).hom.hom.left)
  · rw [(Dynamic.Affine.isRepresentedBy_unipotentHom _).2]
    exact ((hstd α).2 (ζ α) (hζ α)).2.2.symm

/-- The points `t α = exp ϖ^∨_α` of `A_T`: `t α` lies in the positive real subgroup of
`T(𝔸)`, every other simple root is trivial on `t α`, `α(t α)` is the positive scalar idele of a
real `x > 1`, and `H_G(iT(t α)) = 0`. -/
theorem exists_fundamentalCoweightPoints (hG : IsConnectedReductive G)
    {iT : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus iT) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter iT ν) :
    ∃ t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp,
      (∀ α, t α ∈ PositiveRealTorus.intrinsicSubgroup F T) ∧
      (∀ α β : simpleRelativeRoots iT ν, β ≠ α → Lie.characterValue β.1 (t α) = 1) ∧
      (∀ α : simpleRelativeRoots iT ν, ∃ x : NNRealˣ, 1 < (x : NNReal) ∧
        PositiveRealIdeles.full F x = Lie.characterValue α.1 (t α)) ∧
      ∀ α, characterLog F G (map F T.toGrp G iT (t α)) = 0 := by
  classical
  have := hi.isSplitSubtorus.mono
  obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG T iT hi
  obtain ⟨-, -, ⟨b, hb⟩, -, -⟩ := relativeFundamentalWeight F G hG T iT hi ν hν D
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.isSplitSubtorus.1
  let _ : Fintype I := Fintype.ofFinite I
  let ℓ : simpleRelativeRoots iT ν → RealCharacterDual F T.toGrp :=
    fun α => cocharacterDual (b α : V T)
  let p : simpleRelativeRoots iT ν → PositiveRealTorus.intrinsicSubgroup F T :=
    fun α => PositiveRealTorus.positiveExp F T I e (ℓ α)
  have hlog : ∀ α, characterLog F T.toGrp (p α).val = ℓ α := fun α =>
    PositiveRealTorus.characterLog_full_logParameters F T I e (ℓ α)
  refine ⟨fun α => (p α).val, fun α => (p α).property, ?_, ?_, ?_⟩
  · intro α β hβ
    apply characterValue_eq_one_of_characterLog_eq_zero (p α).property
    rw [hlog, cocharacterDual_apply, ← eval_eq_pair]
    exact (hb α).2.2 β hβ
  · intro α
    apply exists_one_lt_of_characterLog_pos (p α).property
    rw [hlog, cocharacterDual_apply, ← eval_eq_pair, (hb α).2.1]
    exact one_pos
  · intro α
    rw [characterLog_map, hlog]
    apply AddMonoidHom.ext
    intro χ
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict iT χ) (b α : V T) = 0
    exact (mem_cocharacterAnnihilator _ _).1 (hb α).1 _
      (LinearMap.mem_range.2 ⟨(1 : ℝ) ⊗ₜ[ℤ] χ, rfl⟩)

/-- The points `z j` of `A_G ⊆ T`: there are finitely many points `z j` of the positive real
subgroup of `T(𝔸)`, on which every simple root is trivial, whose logarithms `H_G(iT(z j))`
form a basis of `𝔞_G`. They are the images in `T` of positive real points of the split
component `A_G`. -/
theorem exists_centralSplitPoints (hG : IsConnectedReductive G)
    {iT : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus iT) (ν : cocharacterLattice T) :
    ∃ (r : ℕ) (z : Fin r → AdelicGroupPoints F T.toGrp),
      (∀ j, z j ∈ PositiveRealTorus.intrinsicSubgroup F T) ∧
      (∀ j (β : simpleRelativeRoots iT ν), Lie.characterValue β.1 (z j) = 1) ∧
      LinearIndependent ℝ (fun j => characterLog F G (map F T.toGrp G iT (z j))) ∧
      Submodule.span ℝ (Set.range fun j => characterLog F G (map F T.toGrp G iT (z j))) = ⊤ := by
  classical
  have := hi.isSplitSubtorus.mono
  obtain ⟨A, a, ha⟩ := (splitComponentStatement F G hG).1
  obtain ⟨hinj, hfin⟩ := characterRestriction F G hG A a ha
  have := hfin
  obtain ⟨f, hf, -, -, -, -, hker⟩ :=
    (relativeSplitCentralDirections F G hG T iT hi).2.2.2.2.2.2 A a ha
  obtain ⟨I, hI, ⟨e⟩⟩ := ha.1.isSplitSubtorus.1
  let _ : Fintype I := Fintype.ofFinite I
  let Φ : RealCharacterDual F A.toGrp ≃L[ℝ] RealCharacterDual F G :=
    realCharacterDualRestrictionEquiv F G A.toGrp a hinj
  have : FiniteDimensional ℝ (RealCharacterDual F G) :=
    LinearEquiv.finiteDimensional
      (Φ.toLinearEquiv.symm.trans (PositiveRealTorus.dualCoordinatesEquiv F A I e)).symm
  let bG := Module.finBasis ℝ (RealCharacterDual F G)
  let z' : Fin (Module.finrank ℝ (RealCharacterDual F G)) →
      PositiveRealTorus.intrinsicSubgroup F A :=
    fun j => PositiveRealTorus.positiveExp F A I e (Φ.symm (bG j))
  have hlog' : ∀ j, characterLog F A.toGrp (z' j).val = Φ.symm (bG j) := fun j =>
    PositiveRealTorus.characterLog_full_logParameters F A I e _
  let z : Fin (Module.finrank ℝ (RealCharacterDual F G)) → AdelicGroupPoints F T.toGrp :=
    fun j => map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) (z' j).val
  have hz : ∀ j, characterLog F G (map F T.toGrp G iT (z j)) = bG j := by
    intro j
    have hcomp : map F T.toGrp G iT (z j) = map F A.toGrp G a (z' j).val := by
      rw [← hf]
      simp only [z, map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
        Category.assoc]
    rw [hcomp, characterLog_map, hlog']
    exact Φ.apply_symm_apply (bG j)
  refine ⟨Module.finrank ℝ (RealCharacterDual F G), z, fun j => ?_, fun j β => ?_, ?_⟩
  · exact PositiveRealTorus.map_intrinsicSubgroup_le F A T f ⟨(z' j).val, (z' j).property, rfl⟩
  · change Lie.characterValue β.1 ((z' j).val ≫ (CommGroupScheme.groupHom f).hom.hom) = 1
    rw [← Lie.characterValue_comp]
    apply characterValue_eq_one_of_characterLog_eq_zero (z' j).property
    rw [hlog']
    have hβ : (1 : ℝ) ⊗ₜ[ℤ] β.1 ∈
        LinearMap.ker (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)) := by
      rw [hker]
      exact Submodule.subset_span ⟨β.1, simpleRelativeRoots_subset_relativeRoots iT ν β.2, rfl⟩
    have h0 : (1 : ℝ) ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) β.1 = 0 :=
      LinearMap.mem_ker.1 hβ
    let l : rationalCharacters A.toGrp →+ ℝ := Φ.symm (bG j)
    have h1 := congrArg (LinearMap.liftBaseChange ℝ l.toIntLinearMap) h0
    rw [LinearMap.liftBaseChange_tmul, map_zero, one_smul] at h1
    exact h1
  · have hfun : (fun j => characterLog F G (map F T.toGrp G iT (z j))) = ⇑bG := funext hz
    rw [hfun]
    exact ⟨bG.linearIndependent, bG.span_eq⟩

end GroupData

section Datum

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A choice of group data of the system `Ξ_main` (Bernstein–Lapid §7.2) for a maximal split
torus `iT : T → G` and a generic cocharacter `ν`: closed subgroup schemes `u α : U_α → G`
(affine) representing the unipotent radicals of the maximal standard parabolics, points
`t α ∈ A_T`, a number `r` and points `z j ∈ A_T` (`j < r`), satisfying
`IsLocalFinitenessGroupData`. -/
structure LocalFinitenessGroupDatum (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T) where
  /-- The unipotent radical `U_α` of the maximal standard parabolic `P_α`. -/
  Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F))
  /-- Each `U_α` is affine. -/
  isAffine : ∀ α, IsAffine (Ua α).X.left
  /-- The inclusion `U_α → G`. -/
  u : ∀ α, Ua α ⟶ G
  /-- The inclusion `U_α → G` is a closed immersion. -/
  isClosedImmersion : ∀ α, IsClosedImmersion (u α).hom.hom.left
  /-- The points `t α ∈ A_T` with `a_α = iT(t α)`. -/
  t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp
  /-- The dimension of `𝔞_G`. -/
  r : ℕ
  /-- The points `z j ∈ A_T` with `iT(z j) ∈ A_G`. -/
  z : Fin r → AdelicGroupPoints F T.toGrp
  /-- The defining properties of the data of `Ξ_main`. -/
  isLocalFinitenessGroupData : IsLocalFinitenessGroupData iT ν u t z

/-- Group data of `Ξ_main` exist for every maximal split torus of a connected reductive group
over a number field and every generic cocharacter. -/
theorem LocalFinitenessGroupDatum.nonempty [IsAffine G.X.left] (hG : IsConnectedReductive G)
    {iT : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus iT) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter iT ν) : Nonempty (LocalFinitenessGroupDatum iT ν) := by
  obtain ⟨Ua, hUa, u, hu, hrange⟩ := exists_closed_standardUnipotent_maximal hG hi hν
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := exists_fundamentalCoweightPoints hG hi hν
  obtain ⟨r, z, hz₁, hz₂, hz₃, hz₄⟩ := exists_centralSplitPoints hG hi ν
  exact ⟨⟨Ua, hUa, u, hu, t, r, z,
    ⟨hrange, ht₁, ht₂, ht₃, ht₄, hz₁, hz₂, hz₃, hz₄⟩⟩⟩

/-- Group data of `Ξ_main` exist (Bernstein–Lapid §7.2), in the existential form used by
`EisensteinSystemDominationStatement`. -/
theorem exists_isLocalFinitenessGroupData [IsAffine G.X.left] (hG : IsConnectedReductive G)
    {iT : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus iT) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter iT ν) :
    ∃ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
      (_ : ∀ α, IsAffine (Ua α).X.left) (u : ∀ α, Ua α ⟶ G)
      (_ : ∀ α, IsClosedImmersion (u α).hom.hom.left)
      (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) (r : ℕ)
      (z : Fin r → AdelicGroupPoints F T.toGrp),
      IsLocalFinitenessGroupData iT ν u t z := by
  obtain ⟨d⟩ := LocalFinitenessGroupDatum.nonempty hG hi hν
  exact ⟨d.Ua, d.isAffine, d.u, d.isClosedImmersion, d.t, d.r, d.z,
    d.isLocalFinitenessGroupData⟩

end Datum

end Langlands.Global
