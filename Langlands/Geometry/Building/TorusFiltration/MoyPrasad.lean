import Langlands.Geometry.Building.TorusFiltration.Lie

/-! # The Moy–Prasad isomorphism of KP Proposition B.10.16 for tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Geometry.Building

/-! ### Integer and fractional parts of a depth -/

/-- The integer part `n = ⌊r⌋` of a depth `r ≥ 1`, as a positive congruence level. -/
def torusMoyPrasadLevel (r : ℝ≥0) (hr : 1 ≤ r) : ℕ+ :=
  ⟨⌊r⌋₊, Nat.floor_pos.mpr hr⟩

/-- The fractional part `r₀ = r - ⌊r⌋` of a depth `r`, which lies in `[0, 1)`. -/
def torusMoyPrasadBase (r : ℝ≥0) : ℝ≥0 :=
  r - (⌊r⌋₊ : ℝ≥0)

theorem torusMoyPrasadBase_add_level (r : ℝ≥0) (hr : 1 ≤ r) :
    torusMoyPrasadBase r + ((torusMoyPrasadLevel r hr : ℕ) : ℝ≥0) = r :=
  tsub_add_cancel_of_le (Nat.floor_le zero_le)

theorem torusMoyPrasadBase_add_two_mul_level (r : ℝ≥0) (hr : 1 ≤ r) :
    torusMoyPrasadBase r + (((2 * torusMoyPrasadLevel r hr : ℕ+) : ℕ) : ℝ≥0) =
      r + (⌊r⌋₊ : ℝ≥0) := by
  rw [PNat.mul_coe, PNat.val_ofNat, Nat.cast_mul, Nat.cast_two, two_mul, ← add_assoc,
    torusMoyPrasadBase_add_level]
  rfl

private theorem le_two_mul_pnat (n : ℕ+) : n ≤ 2 * n := by
  rw [← PNat.coe_le_coe, PNat.mul_coe, PNat.val_ofNat]
  omega

private theorem two_mul_pnat_coe_le (n : ℕ+) : ((2 * n : ℕ+) : ℕ) ≤ 2 * (n : ℕ) := by
  rw [PNat.mul_coe, PNat.val_ofNat]

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Model" => IntegralModel O K T.toGrp

private local instance moyPrasadIntegersDVR : IsDiscreteValuationRing O :=
  (fixedFieldIntegers_strictHenselian F).1

/-! ### The quotients -/

/-- The point quotient `T(K)_r / T(K)_s`, a commutative group. -/
abbrev minimalCongruentQuotient (r s : ℝ≥0) :=
  minimalCongruentPoints F T hT r ⧸
    (minimalCongruentPoints F T hT s).subgroupOf (minimalCongruentPoints F T hT r)

/-- The Lie quotient `t(K)_r / t(K)_s`, an `O`-module. -/
abbrev minimalCongruentLieQuotient (r s : ℝ≥0) :=
  minimalCongruentLie F T hT r ⧸
    (minimalCongruentLie F T hT s).comap (minimalCongruentLie F T hT r).subtype

/-! ### The congruence subgroups and Lie lattices of the model at the fractional depth -/

/-- The level-`⌊r⌋` congruence subgroup of `𝒯_{r₀}` is `T(K)_r`. -/
theorem congruenceSubgroupAt_torusMoyPrasadLevel (r : ℝ≥0) (hr : 1 ≤ r) :
    (minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.congruenceSubgroupAt
      (torusMoyPrasadLevel r hr) = minimalCongruentPoints F T hT r := by
  have h := congruenceSubgroupAt_eq_minimalCongruentPoints F T hT (torusMoyPrasadBase r)
    (torusMoyPrasadLevel r hr) (minimalCongruentModel F T hT _).property.1
    (minimalCongruentModel F T hT _).property.2.2
  rwa [torusMoyPrasadBase_add_level] at h

/-- The level-`⌊r⌋` Lie lattice `𝔪^⌊r⌋ • Lie(𝒯_{r₀})` is `t(K)_r`, given KP Lemma
A.5.13(4) (the argument `h𝔩`). -/
theorem lieLatticeAt_torusMoyPrasadLevel
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r : ℝ≥0) (hr : 1 ≤ r) :
    (minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.lieLatticeAt
      (torusMoyPrasadLevel r hr) = minimalCongruentLie F T hT r := by
  have h := smul_lieLattice_eq_minimalCongruentLie F T hT h𝔩 (torusMoyPrasadBase r)
    (torusMoyPrasadLevel r hr : ℕ) (minimalCongruentModel F T hT _).property.1
    (minimalCongruentModel F T hT _).property.2.2
  rwa [torusMoyPrasadBase_add_level] at h

/-- The level-`2⌊r⌋` Lie lattice of `𝒯_{r₀}` is `t(K)_{r₀ + 2⌊r⌋}`, hence lies in `t(K)_s`
for `s ≤ r + ⌊r⌋`, given KP Lemma A.5.13(4) (the argument `h𝔩`). -/
theorem lieLatticeAt_two_mul_torusMoyPrasadLevel_le
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hs : s ≤ r + ⌊r⌋₊) :
    (minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.lieLatticeAt
      (2 * torusMoyPrasadLevel r hr) ≤ minimalCongruentLie F T hT s := by
  have h := smul_lieLattice_eq_minimalCongruentLie F T hT h𝔩 (torusMoyPrasadBase r)
    ((2 * torusMoyPrasadLevel r hr : ℕ+) : ℕ) (minimalCongruentModel F T hT _).property.1
    (minimalCongruentModel F T hT _).property.2.2
  rw [torusMoyPrasadBase_add_two_mul_level] at h
  exact h.le.trans (minimalCongruentLie_antitone F T hT hs)

/-! ### The construction -/

attribute [local irreducible] IntegralModel.congruenceLieHom minimalCongruentModel

/-- The map from the Lie-lattice quotient of `𝒯_{r₀}` between the levels `⌊r⌋` and `2⌊r⌋`
to `t(K)_r / t(K)_s`, the identity on representatives: the level-`⌊r⌋` Lie lattice is
`t(K)_r` and the level-`2⌊r⌋` one lies in `t(K)_s`, given KP Lemma A.5.13(4) (the argument
`h𝔩`). -/
def minimalCongruentMoyPrasadLieMap
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hs : s ≤ r + ⌊r⌋₊) :
    (minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.congruenceLieQuotient
        (torusMoyPrasadLevel r hr) (2 * torusMoyPrasadLevel r hr) →ₗ[O]
      minimalCongruentLieQuotient F T hT r s :=
  Submodule.mapQ _ _
    (LinearMap.codRestrict _ (Submodule.subtype _)
      (fun X => (lieLatticeAt_torusMoyPrasadLevel F T hT h𝔩 r hr).le X.property))
    (fun _ hX => lieLatticeAt_two_mul_torusMoyPrasadLevel_le F T hT h𝔩 r s hr hs hX)

/-- The homomorphism `T(K)_r → t(K)_r / t(K)_s`: the congruence–Lie homomorphism of the
model `𝒯_{r₀}` at levels `⌊r⌋ ≤ 2⌊r⌋` (KP Proposition A.5.19(3)), through the
identifications of its level-`⌊r⌋` congruence subgroup with `T(K)_r` and of its Lie
lattices with the Lie filtration. -/
def minimalCongruentMoyPrasadHom
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hs : s ≤ r + ⌊r⌋₊) :
    minimalCongruentPoints F T hT r →* Multiplicative (minimalCongruentLieQuotient F T hT r s) :=
  (minimalCongruentMoyPrasadLieMap F T hT h𝔩 r s hr hs).toAddMonoidHom.toMultiplicative.comp
    (((minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.congruenceLieHom
        (minimalCongruentModel F T hT (torusMoyPrasadBase r)).property.1
        (le_two_mul_pnat (torusMoyPrasadLevel r hr))
        (two_mul_pnat_coe_le (torusMoyPrasadLevel r hr))).comp
      (MulEquiv.subgroupCongr (congruenceSubgroupAt_torusMoyPrasadLevel F T hT r hr).symm).toMonoidHom)

/-- The value of `minimalCongruentMoyPrasadHom` at a point of `T(K)_r`. -/
theorem minimalCongruentMoyPrasadHom_apply
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hs : s ≤ r + ⌊r⌋₊) (g : minimalCongruentPoints F T hT r) :
    minimalCongruentMoyPrasadHom F T hT h𝔩 r s hr hs g =
      Multiplicative.ofAdd (minimalCongruentMoyPrasadLieMap F T hT h𝔩 r s hr hs
        (Multiplicative.toAdd
          ((minimalCongruentModel F T hT (torusMoyPrasadBase r)).val.congruenceLieHom
            (minimalCongruentModel F T hT (torusMoyPrasadBase r)).property.1
            (le_two_mul_pnat (torusMoyPrasadLevel r hr))
            (two_mul_pnat_coe_le (torusMoyPrasadLevel r hr))
            (MulEquiv.subgroupCongr
              (congruenceSubgroupAt_torusMoyPrasadLevel F T hT r hr).symm g)))) :=
  rfl

omit [IsAffine T.X.left] in
private theorem identity_map_integralPoints_le {M N : Model}
    (h : N.integralPoints ≤ M.integralPoints) :
    N.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ M.integralPoints := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h hx

private theorem identity_hom_lieLattice_le {M N : Model} (φ : N.Hom M (𝟙 T.toGrp)) :
    N.lieLattice ≤ M.lieLattice := fun X hX => by
  have h := φ.map_lieLattice_le (Submodule.mem_map_of_mem (f := GenericLie.map O (𝟙 T.toGrp)) hX)
  rwa [GenericLie.map_id] at h

/- The differential of a model homomorphism extending the identity sends the class of `Y` to
the class of `Y`. -/
private theorem congruenceLieQuotientMap_mk_of_identity {M N : Model}
    (φ : N.Hom M (𝟙 T.toGrp)) (n m : ℕ+) (Y : N.lieLatticeAt n)
    (hY : (Y : GenericLie O T.toGrp) ∈ M.lieLatticeAt n) :
    φ.congruenceLieQuotientMap n m (Submodule.Quotient.mk Y) =
      Submodule.Quotient.mk (⟨Y.val, hY⟩ : M.lieLatticeAt n) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  exact GenericLie.map_id O Y.val

/- A point of the level-`n` congruence subgroup of `M` lying in that of `N` comes from `N`
under a model homomorphism `N → M` extending the identity. -/
omit [IsAffine T.X.left] in
private theorem exists_congruenceSubgroupMap_eq_of_identity {M N : Model}
    (φ : N.Hom M (𝟙 T.toGrp)) (n : ℕ+) (g : M.congruenceSubgroupAt n)
    (hg : g.val ∈ N.congruenceSubgroupAt n) :
    ∃ g' : N.congruenceSubgroupAt n, φ.congruenceSubgroupMap n g' = g :=
  ⟨⟨g.val, hg⟩, Subtype.ext (by
    change g.val ≫ (𝟙 T.toGrp : T.toGrp ⟶ T.toGrp).hom.hom = g.val
    simp only [Grp.id_hom_hom, Category.comp_id])⟩

/- Every class in the image of the differential of a model homomorphism `N → M` extending the
identity is the class of an element of the level-`n` Lie lattice of `N`. -/
private theorem exists_congruenceLieQuotientMap_eq_mk {M N : Model}
    (φ : N.Hom M (𝟙 T.toGrp)) (n m : ℕ+) (q : N.congruenceLieQuotient n m) :
    ∃ X : M.lieLatticeAt n, (X : GenericLie O T.toGrp) ∈ N.lieLatticeAt n ∧
      φ.congruenceLieQuotientMap n m q = Submodule.Quotient.mk X := by
  obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hYM : (Y : GenericLie O T.toGrp) ∈ M.lieLatticeAt n :=
    Submodule.smul_mono le_rfl (identity_hom_lieLattice_le F T φ) Y.property
  exact ⟨⟨Y.val, hYM⟩, Y.property, congruenceLieQuotientMap_mk_of_identity F T φ n m Y hYM⟩

attribute [local irreducible] IntegralModel.Hom.congruenceLieQuotientMap

set_option maxHeartbeats 400000 in
/- If `φ : N → M` extends the identity, the congruence–Lie image in `M` of a point of the
level-`n` congruence subgroup of `N` is the class of an element of the level-`n` Lie lattice
of `N`, by the functoriality of the congruence–Lie homomorphism. -/
private theorem exists_congruenceLieHom_eq_of_hom
    (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u}) {M N : Model}
    (hM : M.IsSmooth) (hN : N.IsSmooth) (φ : N.Hom M (𝟙 T.toGrp)) (n : ℕ+)
    (g : M.congruenceSubgroupAt n) (hg : g.val ∈ N.congruenceSubgroupAt n) :
    ∃ X : M.lieLatticeAt n, (X : GenericLie O T.toGrp) ∈ N.lieLatticeAt n ∧
      M.congruenceLieHom hM (le_two_mul_pnat n) (two_mul_pnat_coe_le n) g =
        Multiplicative.ofAdd (Submodule.Quotient.mk X : M.congruenceLieQuotient n (2 * n)) := by
  obtain ⟨g', rfl⟩ := exists_congruenceSubgroupMap_eq_of_identity F T φ n g hg
  obtain ⟨X, hXN, hX⟩ := exists_congruenceLieQuotientMap_eq_mk F T φ n (2 * n)
    (Multiplicative.toAdd (N.congruenceLieHom hN (le_two_mul_pnat n) (two_mul_pnat_coe_le n) g'))
  exact ⟨X, hXN, (DFunLike.congr_fun (hF O K T.toGrp T.toGrp N M hN hM (𝟙 _) φ n (2 * n)
    (le_two_mul_pnat n) (two_mul_pnat_coe_le n)) g').trans (congrArg Multiplicative.ofAdd hX)⟩

/-- `T(K)_s` lies in the kernel of the homomorphism to `t(K)_r / t(K)_s`, for
`r ≤ s ≤ r + ⌊r⌋`. Write `s = s₀ + ⌊r⌋` with `r₀ ≤ s₀`. The identity of `T` extends to a
model homomorphism `𝒯_{s₀} → 𝒯_{r₀}` (KP Corollary 2.10.10), whose source has level-`⌊r⌋`
congruence subgroup `T(K)_s`; by the functoriality of the congruence–Lie homomorphism (the
argument `hF`, KP Proposition A.5.19(3)) the image of a point of `T(K)_s` is the class of an
element of the level-`⌊r⌋` Lie lattice of `𝒯_{s₀}`, which is `t(K)_s`. -/
theorem minimalCongruentMoyPrasadHom_deeper_le_ker
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
    (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊) :
    (minimalCongruentPoints F T hT s).subgroupOf (minimalCongruentPoints F T hT r) ≤
      (minimalCongruentMoyPrasadHom F T hT h𝔩 r s hr hs).ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  let n := torusMoyPrasadLevel r hr
  let s₀ := s - ((n : ℕ) : ℝ≥0)
  have hnr : ((n : ℕ) : ℝ≥0) ≤ r := Nat.floor_le zero_le
  have hs₀ : s₀ + ((n : ℕ) : ℝ≥0) = s := tsub_add_cancel_of_le (hnr.trans hrs)
  have hrs₀ : torusMoyPrasadBase r ≤ s₀ := by
    refine le_of_add_le_add_right (a := ((n : ℕ) : ℝ≥0)) ?_
    rw [torusMoyPrasadBase_add_level, hs₀]
    exact hrs
  let M := minimalCongruentModel F T hT (torusMoyPrasadBase r)
  let N := minimalCongruentModel F T hT s₀
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le (M := M.val) (n := 𝟙 T.toGrp)
    IntegralModel.smoothHomExtension F N.property.1 rfl (identity_map_integralPoints_le F T (by
      rw [N.property.2.2, M.property.2.2]
      exact minimalCongruentPoints_antitone F T hT hrs₀))
  have hNn : N.val.congruenceSubgroupAt n = minimalCongruentPoints F T hT s := by
    have h := congruenceSubgroupAt_eq_minimalCongruentPoints F T hT s₀ n N.property.1
      N.property.2.2
    rwa [hs₀] at h
  have hNl : N.val.lieLatticeAt n = minimalCongruentLie F T hT s := by
    have h := smul_lieLattice_eq_minimalCongruentLie F T hT h𝔩 s₀ (n : ℕ) N.property.1
      N.property.2.2
    rwa [hs₀] at h
  let e := MulEquiv.subgroupCongr (congruenceSubgroupAt_torusMoyPrasadLevel F T hT r hr).symm
  obtain ⟨X, hXN, hX⟩ := exists_congruenceLieHom_eq_of_hom F T hF M.property.1 N.property.1 φ n
    (e g) (by rw [hNn]; exact hg)
  refine MonoidHom.mem_ker.mpr ?_
  rw [minimalCongruentMoyPrasadHom_apply]
  refine (congrArg Multiplicative.ofAdd ?_).trans ofAdd_zero
  refine (congrArg (minimalCongruentMoyPrasadLieMap F T hT h𝔩 r s hr hs) (congrArg
    Multiplicative.toAdd hX)).trans ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
  change (X : GenericLie O T.toGrp) ∈ minimalCongruentLie F T hT s
  rw [← hNl]
  exact hXN

/-- The Moy–Prasad homomorphism `T(K)_r / T(K)_s → t(K)_r / t(K)_s` of KP Proposition
B.10.16, for `1 ≤ r ≤ s ≤ r + ⌊r⌋`: the quotient of `minimalCongruentMoyPrasadHom`. It is
built from KP Lemma A.5.13(4) (the argument `h𝔩`) and the functoriality in KP Proposition
A.5.19(3) (the argument `hF`). -/
def minimalCongruentMoyPrasad
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
    (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊) :
    minimalCongruentQuotient F T hT r s →*
      Multiplicative (minimalCongruentLieQuotient F T hT r s) :=
  QuotientGroup.lift _ (minimalCongruentMoyPrasadHom F T hT h𝔩 r s hr hs)
    (minimalCongruentMoyPrasadHom_deeper_le_ker F T hT h𝔩 hF r s hr hrs hs)

/-- The value of `minimalCongruentMoyPrasad` on the class of a point of `T(K)_r`. -/
@[simp] theorem minimalCongruentMoyPrasad_mk
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
    (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u}) (r s : ℝ≥0) (hr : 1 ≤ r)
    (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊) (g : minimalCongruentPoints F T hT r) :
    minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs (QuotientGroup.mk g) =
      minimalCongruentMoyPrasadHom F T hT h𝔩 r s hr hs g :=
  rfl

/-! ### Maps induced by homomorphisms of tori -/

variable {T}
variable {U : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffine U.X.left]
  (hU : IsTorus U.toGrp)

/-- A homomorphism of tori `f : T → U` maps `T(K)_r` into `U(K)_r` (KP Proposition
B.10.10, `minimalCongruentFunctoriality`). -/
def minimalCongruentPointsMap (f : T ⟶ U) (r : ℝ≥0) :
    minimalCongruentPoints F T hT r →* minimalCongruentPoints F U hU r :=
  ((rationalPoints.map (CommGroupScheme.groupHom f)).comp
      (minimalCongruentPoints F T hT r).subtype).codRestrict _
    (fun g => minimalCongruentFunctoriality F T U hT hU f r (Subgroup.mem_map_of_mem _ g.property))

/-- The map `T(K)_r / T(K)_s → U(K)_r / U(K)_s` induced by a homomorphism of tori. -/
def minimalCongruentQuotientMap (f : T ⟶ U) (r s : ℝ≥0) :
    minimalCongruentQuotient F T hT r s →* minimalCongruentQuotient F U hU r s :=
  QuotientGroup.map _ _ (minimalCongruentPointsMap F hT hU f r) (fun g hg => by
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact minimalCongruentFunctoriality F T U hT hU f s (Subgroup.mem_map_of_mem _ hg))

/-- The map `t(K)_r / t(K)_s → u(K)_r / u(K)_s` induced by the differential
`GenericLie.map O f` of a homomorphism of tori (`map_minimalCongruentLie_le`). -/
def minimalCongruentLieQuotientMap (f : T ⟶ U) (r s : ℝ≥0) :
    minimalCongruentLieQuotient F T hT r s →ₗ[O] minimalCongruentLieQuotient F U hU r s :=
  Submodule.mapQ _ _
    (LinearMap.codRestrict _ ((GenericLie.map O (CommGroupScheme.groupHom f)).comp
        (minimalCongruentLie F T hT r).subtype)
      (fun X => map_minimalCongruentLie_le F T hT hU f r (Submodule.mem_map_of_mem X.property)))
    (fun _ hX => map_minimalCongruentLie_le F T hT hU f s (Submodule.mem_map_of_mem hX))

end Langlands.Geometry.Building
