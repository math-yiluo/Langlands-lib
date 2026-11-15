import Langlands.Geometry.Building.RootGroupLinearization
import Langlands.Geometry.Building.UnramifiedFixedPointRootDescent
import Langlands.Geometry.Building.RootValuationFieldDescent
import Langlands.GroupScheme.Rational.RootDoubleCommutatorBilinear
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Semilinear coordinates on rational root-group points: the proof

For a field extension `K/k`, a smooth affine `k`-group `G`, a split `k`-torus `S → G` with
opposite factor pairs and a relative root `α`, this module proves
`RootGroupLinearization iS α v`: the group `U_{α_K}(K)` carries `Aut(K/k)`-equivariant
coordinates `q` with kernel `U_{2α_K}(K)`, the group `U_{2α_K}(K)` carries injective
equivariant coordinates `e`, and a unit `c` of valuation one is realized by a point `ν(c)` of
`S_K` in the common kernel of the character valuations that scales `q` by `c^d` and `e` by
`c^2`.

All coordinates are read at the `k`-scheme `Spec K`. A `K`-point of `G_K` is a `k`-scheme
point `Spec K → G` (`baseChangeCoeffEquiv`); it lies in `U_{a_K}(K)` exactly when it lifts
through a representative `U → G` of the root functor of `a` over `k`; and the coordinates
are the weight vector coordinates over `k` of the lift (or of its image in `U_a / U_{2a}`),
evaluated at `Spec K`. Naturality of these coordinates gives Galois equivariance, and their
weight property together with `characterValue_cocharacter` gives the torus scaling.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace RootGroupLinearizationProof

section Sections

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The `k`-scheme `Spec K`, the test scheme of `K`-coefficient points. -/
abbrev specTest : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k K))

/-- The `k`-automorphism of `Spec K` induced by `σ ∈ Aut(K/k)`. -/
abbrev specAut (σ : K ≃ₐ[k] K) : specTest k K ⟶ specTest k K :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op

/-- Global sections of `Spec K`, read in `K`. -/
def sectionValue : Γ((specTest k K).left, ⊤) ≃+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv

theorem sectionValue_apply (f : Γ((specTest k K).left, ⊤)) :
    sectionValue k K f = (Scheme.ΓSpecIso (CommRingCat.of K)).hom f :=
  rfl

/-- The coefficient action on points is precomposition with `Spec σ`. -/
theorem conjugate_eq (G : GroupScheme (Spec (CommRingCat.of k))) (σ : K ≃ₐ[k] K)
    (y : G.affinePoints (CommAlgCat.of k K)) :
    GaloisPoint.conjugate k K G σ y = specAut k K σ ≫ y :=
  rfl

/-- Pulling back sections along `Spec σ` is `σ` on `K`. -/
theorem sectionValue_specAut (σ : K ≃ₐ[k] K) (f : Γ((specTest k K).left, ⊤)) :
    sectionValue k K ((specAut k K σ).left.appTop f) = σ (sectionValue k K f) := by
  have h := congrArg (fun φ => φ.hom f)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (σ : K →+* K)))
  exact h

/-- A unit fixed by `σ` gives a `K`-point of `𝔾_m` fixed by `Spec σ`. -/
theorem specAut_comp_gm_symm (σ : K ≃ₐ[k] K) (c : Kˣ) (hc : σ (c : K) = c) :
    specAut k K σ ≫ ((Gm.affinePointsEquiv _).symm c :
        Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) =
      ((Gm.affinePointsEquiv _).symm c :
        Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) := by
  have key : sectionValue k K (Gm.pointsEquiv _ (specTest k K)
      ((Gm.affinePointsEquiv (specTest k K).hom).symm c)).val = c :=
    congrArg Units.val ((Gm.affinePointsEquiv (specTest k K).hom).apply_symm_apply c)
  apply (Gm.pointsEquiv _ (specTest k K)).injective
  apply Units.ext
  rw [Gm.pointsEquiv_naturality, Units.coe_map]
  apply (sectionValue k K).injective
  change sectionValue k K ((specAut k K σ).left.appTop _) = _
  rw [sectionValue_specAut]
  exact (congrArg σ key).trans (hc.trans key.symm)

end Sections

section Coordinates

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
  (e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- The coordinates in `K^n` of a `K`-point of a group with vector coordinates. -/
def pointCoords (v : specTest k K ⟶ V.X) : Fin n → K :=
  fun l => sectionValue k K ((e (specTest k K) v).toAdd l)

theorem pointCoords_mul (v w : specTest k K ⟶ V.X) :
    pointCoords e (v * w) = pointCoords e v + pointCoords e w := by
  funext l
  simp only [pointCoords, map_mul, toAdd_mul, Pi.add_apply, map_add]

theorem pointCoords_eq_zero_iff (v : specTest k K ⟶ V.X) : pointCoords e v = 0 ↔ v = 1 := by
  constructor
  · intro h
    apply (e (specTest k K)).injective
    rw [map_one]
    apply Multiplicative.toAdd.injective
    funext l
    apply (sectionValue k K).injective
    rw [toAdd_one, Pi.zero_apply, map_zero]
    exact congrFun h l
  · rintro rfl
    funext l
    simp only [pointCoords, map_one, toAdd_one, Pi.zero_apply, map_zero]

theorem pointCoords_specAut (he : RelativeRoot.IsNaturalVectorCoordinates e) (σ : K ≃ₐ[k] K)
    (v : specTest k K ⟶ V.X) :
    pointCoords e (specAut k K σ ≫ v) = fun l => σ (pointCoords e v l) := by
  funext l
  simp only [pointCoords]
  rw [he _ _ (specAut k K σ) v]
  exact sectionValue_specAut k K σ _

theorem pointCoords_act {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {c : AutomorphicAction S.toGrp V} {a : characterLattice S}
    (he : RelativeRoot.IsWeightVectorCoordinates c a e) (s : specTest k K ⟶ S.X)
    (v : specTest k K ⟶ V.X) :
    pointCoords e (c.act s v) = (Lie.characterValue a s : K) • pointCoords e v := by
  funext l
  simp only [pointCoords, Pi.smul_apply, smul_eq_mul]
  rw [he.2 _ s v, Pi.smul_apply, smul_eq_mul, map_mul]
  rfl

end Coordinates

section Lifts

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G U : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

open Classical in
/-- Coordinates of a `K`-point of `G` read through `jU : U → G`: the coordinates of a lift,
and `0` off the image. -/
def liftCoords (jU : U ⟶ G) (F : (specTest k K ⟶ U.X) → Fin n → K)
    (g : specTest k K ⟶ G.X) : Fin n → K :=
  if h : ∃ y : specTest k K ⟶ U.X, y ≫ jU.hom.hom = g then F h.choose else 0

theorem liftCoords_comp (jU : U ⟶ G) [Mono jU.hom.hom] (F : (specTest k K ⟶ U.X) → Fin n → K)
    (y : specTest k K ⟶ U.X) : liftCoords jU F (y ≫ jU.hom.hom) = F y := by
  have h : ∃ y' : specTest k K ⟶ U.X, y' ≫ jU.hom.hom = y ≫ jU.hom.hom := ⟨y, rfl⟩
  simp only [liftCoords, h, ↓reduceDIte]
  congr 1
  exact (cancel_mono jU.hom.hom).mp h.choose_spec

end Lifts

section Membership

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

/-- A `K`-point of `G_K` lies in `U_{a_K}(K)` exactly when, as a `k`-scheme point
`Spec K → G`, it lies in the root functor of `a`. -/
theorem mem_rootGroupPoints_baseChange_iff (i : S.toGrp ⟶ G) (a : characterLattice S)
    (x : rationalPoints G_K) :
    x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a) ↔
      baseChangeCoeffEquiv k K G x ∈ (RelativeRoot.subgroup i a).carrier (specTest k K) := by
  change x ∈ (RelativeRoot.subgroup (S := S_K) (i_K i) (a_K a)).carrier _ ↔ _
  rw [RelativeRoot.subgroup_baseChange, SubgroupFunctor.mem_baseChange]
  let e : specTest k K ≅ (Over.map b).obj (Over.mk (𝟙 _)) :=
    Over.isoMk (Iso.refl _) (by simp)
  have hx : baseChangeCoeffEquiv k K G x =
      e.hom ≫ baseChangePointsEquiv b G (Over.mk (𝟙 _)) x := rfl
  constructor
  · intro h
    rw [hx]
    exact (RelativeRoot.subgroup i a).comp_mem e.hom h
  · intro h
    have h' := (RelativeRoot.subgroup i a).comp_mem e.inv h
    rwa [hx, Iso.inv_hom_id_assoc] at h'

/-- Through a representative `jU` of the root functor of `a`, a `K`-point of `G_K` lies in
`U_{a_K}(K)` exactly when it lifts to `U`. -/
theorem mem_rootGroupPoints_baseChange_iff_exists (i : S.toGrp ⟶ G) (a : characterLattice S)
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hjU : (RelativeRoot.subgroup i a).IsRepresentedBy jU) (x : rationalPoints G_K) :
    x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a) ↔
      ∃ y : specTest k K ⟶ U.X, y ≫ jU.hom.hom = baseChangeCoeffEquiv k K G x := by
  rw [mem_rootGroupPoints_baseChange_iff, ← hjU.2]
  exact SubgroupFunctor.mem_range

end Membership

section RationalCoordinates

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {G U : GroupScheme (Spec (CommRingCat.of k))}
  {n : ℕ}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

/-- The coordinates of a `K`-point of `G_K`, read through `jU` at `Spec K`. -/
def rationalCoords (jU : U ⟶ G) (F : (specTest k K ⟶ U.X) → Fin n → K) :
    rationalPoints G_K → Fin n → K :=
  fun x => liftCoords jU F (baseChangeCoeffEquiv k K G x)

variable (i : S.toGrp ⟶ G) (a : characterLattice S) {jU : U ⟶ G}
  (hjU : (RelativeRoot.subgroup i a).IsRepresentedBy jU) (F : (specTest k K ⟶ U.X) → Fin n → K)

include hjU

theorem rationalCoords_mul (hF : ∀ y₁ y₂, F (y₁ * y₂) = F y₁ + F y₂)
    {x : rationalPoints G_K} (hx : x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a))
    {x' : rationalPoints G_K} (hx' : x' ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a)) :
    rationalCoords jU F (x * x') = rationalCoords jU F x + rationalCoords jU F x' := by
  have : Mono jU.hom.hom := hjU.1
  obtain ⟨y, hy⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x).mp hx
  obtain ⟨y', hy'⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x').mp hx'
  have hxx : baseChangeCoeffEquiv k K G (x * x') = (y * y') ≫ jU.hom.hom := by
    rw [map_mul, MonObj.mul_comp, hy, hy']
  simp only [rationalCoords]
  rw [hxx, ← hy, ← hy', liftCoords_comp, liftCoords_comp, liftCoords_comp, hF]

theorem rationalCoords_eq_zero_iff (D : SubgroupFunctor G)
    (hF : ∀ y, F y = 0 ↔ y ≫ jU.hom.hom ∈ D.carrier (specTest k K))
    {x : rationalPoints G_K} (hx : x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a)) :
    rationalCoords jU F x = 0 ↔ baseChangeCoeffEquiv k K G x ∈ D.carrier (specTest k K) := by
  have : Mono jU.hom.hom := hjU.1
  obtain ⟨y, hy⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x).mp hx
  simp only [rationalCoords]
  rw [← hy, liftCoords_comp]
  exact hF y

theorem rationalConjugate_mem (σ : K ≃ₐ[k] K) {x : rationalPoints G_K}
    (hx : x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a)) :
    rationalConjugate k K G σ x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a) := by
  obtain ⟨y, hy⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x).mp hx
  refine (mem_rootGroupPoints_baseChange_iff_exists i a hjU _).mpr ⟨specAut k K σ ≫ y, ?_⟩
  rw [baseChangeCoeffEquiv_rationalConjugate, conjugate_eq, Category.assoc, hy]

theorem rationalCoords_rationalConjugate
    (hF : ∀ σ : K ≃ₐ[k] K, ∀ y, F (specAut k K σ ≫ y) = fun l => σ (F y l))
    (σ : K ≃ₐ[k] K) {x : rationalPoints G_K}
    (hx : x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a)) :
    rationalCoords jU F (rationalConjugate k K G σ x) = fun l => σ (rationalCoords jU F x l) := by
  have : Mono jU.hom.hom := hjU.1
  obtain ⟨y, hy⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x).mp hx
  have hσ : baseChangeCoeffEquiv k K G (rationalConjugate k K G σ x) =
      (specAut k K σ ≫ y) ≫ jU.hom.hom := by
    rw [baseChangeCoeffEquiv_rationalConjugate, conjugate_eq, Category.assoc, hy]
  simp only [rationalCoords]
  rw [hσ, ← hy, liftCoords_comp, liftCoords_comp, hF]

theorem rationalCoords_conj
    (hF : ∀ (s : specTest k K ⟶ S.X) y,
      F ((RelativeRoot.subgroupAction i a jU hjU).act s y) =
        (Lie.characterValue a s : K) • F y)
    {T : rationalPoints G_K} {s : specTest k K ⟶ S.X}
    (hT : baseChangeCoeffEquiv k K G T = s ≫ i.hom.hom)
    {x : rationalPoints G_K} (hx : x ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a)) :
    T * x * T⁻¹ ∈ rootGroupPoints (S := S_K) (i_K i) (a_K a) ∧
      rationalCoords jU F (T * x * T⁻¹) =
        (Lie.characterValue a s : K) • rationalCoords jU F x := by
  have : Mono jU.hom.hom := hjU.1
  obtain ⟨y, hy⟩ := (mem_rootGroupPoints_baseChange_iff_exists i a hjU x).mp hx
  have hc : baseChangeCoeffEquiv k K G (T * x * T⁻¹) =
      (RelativeRoot.subgroupAction i a jU hjU).act s y ≫ jU.hom.hom := by
    rw [RelativeRoot.subgroupAction_act_comp, map_mul, map_mul, map_inv, hT, hy]
  refine ⟨(mem_rootGroupPoints_baseChange_iff_exists i a hjU _).mpr ⟨_, hc.symm⟩, ?_⟩
  simp only [rationalCoords]
  rw [hc, ← hy, liftCoords_comp, liftCoords_comp, hF]

end RationalCoordinates

end RootGroupLinearizationProof

open RootGroupLinearizationProof

section Main

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- The torus point `ν(c)`: in the character-valuation kernel, fixed by every `σ` fixing `c`,
and its image in `G(K)` is the `k`-scheme point `s ≫ iS` with `s = ν(c) : Spec K → S`. -/
theorem exists_unitCocharacterPoint (iS : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) {c : Kˣ}
    (hc : v (c : K) = 1) :
    ∃ t ∈ characterValuationKernel v (S_K).toGrp,
      (∀ σ : K ≃ₐ[k] K, σ (c : K) = c →
        rationalConjugate k K G σ (rationalPoints.map ((GroupScheme.baseChange b).map iS) t) =
          rationalPoints.map ((GroupScheme.baseChange b).map iS) t) ∧
      baseChangeCoeffEquiv k K G (rationalPoints.map ((GroupScheme.baseChange b).map iS) t) =
        (((Gm.affinePointsEquiv _).symm c :
            Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) ≫
          (CommGroupScheme.groupHom ν).hom.hom) ≫ iS.hom.hom := by
  obtain ⟨t, ht, hΨ⟩ := exists_mem_characterValuationKernel_baseChangeCoeffEquiv_eq iS ν v hc
  have hΨ' : baseChangeCoeffEquiv k K G (rationalPoints.map ((GroupScheme.baseChange b).map iS) t) =
      (((Gm.affinePointsEquiv _).symm c :
          Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) ≫
        (CommGroupScheme.groupHom ν).hom.hom) ≫ iS.hom.hom := by
    rw [hΨ, Grp.comp_hom_hom, Category.assoc]
  refine ⟨t, ht, fun σ hσ => ?_, hΨ'⟩
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate, conjugate_eq, hΨ', ← Category.assoc,
    ← Category.assoc, specAut_comp_gm_symm k K σ c hσ]

/-- The character value of `ν(c)` at a character `a` is `c ^ ⟨a, ν⟩`. -/
theorem characterValue_unitCocharacterPoint (a : characterLattice S) (ν : cocharacterLattice S)
    (c : Kˣ) :
    Lie.characterValue a (((Gm.affinePointsEquiv _).symm c :
        Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp K) ≫
      (CommGroupScheme.groupHom ν).hom.hom) = c ^ latticePairing S a ν := by
  rw [CoordinateWeights.characterValue_cocharacter, MulEquiv.apply_symm_apply]

/-- **Semilinear coordinates on rational root-group points.** For a smooth affine group `G`
over `k` with a split torus `iS : S → G` that has opposite factor pairs, a relative root `α`,
a field extension `K/k` and any valuation `v` on `K`, the root group `U_{α_K}(K)` has the
semilinear coordinates of `RootGroupLinearization`. -/
theorem rootGroupLinearization (iS : S.toGrp ⟶ G) [Mono iS.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs iS)
    {α : characterLattice S} (hα : α ∈ relativeRoots iS)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    RootGroupLinearization iS α v := by
  have hα0 : α ≠ 0 := hα.1
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • α ∉ relativeRoots iS := fun n hn hroot => by
    have := RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two iS hS hE hα
      (by omega) hroot
    omega
  by_cases h2 : 2 • α ∈ relativeRoots iS
  · -- `α` is multipliable: `q` on `U_α / U_{2α}`, `e` on `U_{2α}`, `ν` the coroot of `2α`.
    have h2K : 2 • (a_K α) ∈ relativeRoots (i_K iS) := by
      rw [← map_nsmul]
      exact (mem_roots_baseChange_iff (K := K) G S hS iS _).mpr h2
    have hdbl : doubleRootGroupPoints (i_K iS) (a_K α) = rootGroupPoints (i_K iS) (a_K (2 • α)) := by
      unfold doubleRootGroupPoints
      simp only [h2K, ↓reduceIte]
      rw [map_nsmul]
    obtain ⟨U, jU, hjU, hjUc, -, -⟩ :=
      RelativeRoot.subgroup_has_smooth_closed_representative hS iS α hα0
    have : IsAffineHom U.X.hom := hjUc.isAffineHom
    obtain ⟨U₂, j₂, hj₂, -, -, -⟩ :=
      RelativeRoot.subgroup_has_smooth_closed_representative hS iS (2 • α) h2.1
    obtain ⟨C⟩ := RelativeRoot.nonempty_doubleRootCommutatorPairing hS iS hα0 hhigh hjU hj₂
    obtain ⟨n, m, eV, e₂, heV, he₂, -⟩ := C.exists_bilinear_coordinates hS hα0 hhigh
    have : Mono jU.hom.hom := hjU.1
    have : Mono j₂.hom.hom := hj₂.1
    let ν := hE.rootCoroot iS hS ⟨2 • α, h2⟩
    have hν : latticePairing S α ν = 1 := by
      have h := hE.rootCoroot_pairing iS hS ⟨2 • α, h2⟩
      change latticePairing S (2 • α) ν = 2 at h
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h
      push_cast at h
      omega
    have hν2 : latticePairing S (2 • α) ν = 2 := hE.rootCoroot_pairing iS hS ⟨2 • α, h2⟩
    let F₁ : (specTest k K ⟶ U.X) → Fin n → K := fun y => pointCoords eV (y ≫ C.q.hom.hom)
    let F₂ : (specTest k K ⟶ U₂.X) → Fin m → K := pointCoords e₂
    have hF₁mul : ∀ y₁ y₂, F₁ (y₁ * y₂) = F₁ y₁ + F₁ y₂ := fun y₁ y₂ => by
      simp only [F₁, MonObj.mul_comp, pointCoords_mul]
    have hF₂mul : ∀ y₁ y₂, F₂ (y₁ * y₂) = F₂ y₁ + F₂ y₂ := fun y₁ y₂ => pointCoords_mul e₂ y₁ y₂
    have hF₁0 : ∀ y, F₁ y = 0 ↔
        y ≫ jU.hom.hom ∈ (RelativeRoot.subgroup iS (2 • α)).carrier (specTest k K) := fun y => by
      simp only [F₁, pointCoords_eq_zero_iff]
      rw [← mem_range_kernelι_iff C.q y, C.isFppfQuotient.2.2.2]
      rfl
    have hF₂0 : ∀ y, F₂ y = 0 ↔ y ≫ j₂.hom.hom ∈ (⊥ : SubgroupFunctor G).carrier (specTest k K) :=
      fun y => by
        simp only [F₂, pointCoords_eq_zero_iff, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
        constructor
        · rintro rfl
          exact MonObj.one_comp _
        · intro h
          apply (cancel_mono j₂.hom.hom).mp
          rw [h, MonObj.one_comp]
    have hF₁σ : ∀ σ : K ≃ₐ[k] K, ∀ y, F₁ (specAut k K σ ≫ y) = fun l => σ (F₁ y l) :=
      fun σ y => by
        simp only [F₁, Category.assoc]
        exact pointCoords_specAut eV heV.1 σ _
    have hF₂σ : ∀ σ : K ≃ₐ[k] K, ∀ y, F₂ (specAut k K σ ≫ y) = fun l => σ (F₂ y l) :=
      fun σ y => pointCoords_specAut e₂ he₂.1 σ y
    have hF₁t : ∀ (s : specTest k K ⟶ S.X) y,
        F₁ ((RelativeRoot.subgroupAction iS α jU hjU).act s y) =
          (Lie.characterValue α s : K) • F₁ y := fun s y => by
      simp only [F₁]
      rw [← C.act_comp, pointCoords_act eV heV]
    have hF₂t : ∀ (s : specTest k K ⟶ S.X) y,
        F₂ ((RelativeRoot.subgroupAction iS (2 • α) j₂ hj₂).act s y) =
          (Lie.characterValue (2 • α) s : K) • F₂ y := fun s y => pointCoords_act e₂ he₂ s y
    have hmem₂ : ∀ x, x ∈ doubleRootGroupPoints (i_K iS) (a_K α) ↔
        baseChangeCoeffEquiv k K G x ∈ (RelativeRoot.subgroup iS (2 • α)).carrier (specTest k K) :=
      fun x => by rw [hdbl, mem_rootGroupPoints_baseChange_iff]
    refine ⟨n, m, 1, rationalCoords jU F₁, rationalCoords j₂ F₂, Or.inl rfl,
      fun x hx y hy => rationalCoords_mul iS α hjU F₁ hF₁mul hx hy,
      fun x hx => (rationalCoords_eq_zero_iff iS α hjU F₁ _ hF₁0 hx).trans (hmem₂ x).symm,
      fun x hx y hy => ?_, fun x hx h0 => ?_,
      fun σ x hx => rationalConjugate_mem iS α hjU σ hx,
      fun σ x hx => rationalCoords_rationalConjugate iS α hjU F₁ hF₁σ σ hx,
      fun σ x hx => ?_, fun c hc => ?_⟩
    · rw [hdbl] at hx hy
      exact rationalCoords_mul iS (2 • α) hj₂ F₂ hF₂mul hx hy
    · rw [hdbl] at hx
      have h := (rationalCoords_eq_zero_iff iS (2 • α) hj₂ F₂ ⊥ hF₂0 hx).mp h0
      rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h
      exact (baseChangeCoeffEquiv k K G).injective (h.trans (map_one _).symm)
    · rw [hdbl] at hx
      exact rationalCoords_rationalConjugate iS (2 • α) hj₂ F₂ hF₂σ σ hx
    · obtain ⟨t, ht, hσ, hΨ⟩ := exists_unitCocharacterPoint (k := k) iS ν v hc
      refine ⟨t, ht, hσ, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨hmem, hval⟩ := rationalCoords_conj iS α hjU F₁ hF₁t hΨ hx
        refine ⟨hmem, ?_⟩
        rw [hval, characterValue_unitCocharacterPoint, hν, zpow_one, pow_one]
      · rw [hdbl] at hx
        obtain ⟨-, hval⟩ := rationalCoords_conj iS (2 • α) hj₂ F₂ hF₂t hΨ hx
        rw [hval, characterValue_unitCocharacterPoint, hν2]
        norm_cast
  · -- `α` is not multipliable: `q` on `U_α` itself, no `e`, `ν` the coroot of `α`.
    have h2K : 2 • (a_K α) ∉ relativeRoots (i_K iS) := by
      rw [← map_nsmul]
      exact fun h => h2 ((mem_roots_baseChange_iff (K := K) G S hS iS _).mp h)
    have hdbl : doubleRootGroupPoints (i_K iS) (a_K α) = ⊥ := by
      unfold doubleRootGroupPoints
      simp only [h2K, ↓reduceIte]
    have hno : RelativeRoot.HasNoHigherRoots iS α := fun n hn => by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · obtain rfl : n = 2 := by omega
        exact h2
      · exact hhigh n hn3
    obtain ⟨U, jU, hjU, -, -, -⟩ :=
      RelativeRoot.subgroup_has_smooth_closed_representative hS iS α hα0
    obtain ⟨n, eU, heU⟩ :=
      RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots hS iS hα0 hno hjU
    have : Mono jU.hom.hom := hjU.1
    let ν := hE.rootCoroot iS hS ⟨α, hα⟩
    have hν : latticePairing S α ν = 2 := hE.rootCoroot_pairing iS hS ⟨α, hα⟩
    let F₁ : (specTest k K ⟶ U.X) → Fin n → K := pointCoords eU
    have hF₁mul : ∀ y₁ y₂, F₁ (y₁ * y₂) = F₁ y₁ + F₁ y₂ := fun y₁ y₂ => pointCoords_mul eU y₁ y₂
    have hF₁0 : ∀ y, F₁ y = 0 ↔ y ≫ jU.hom.hom ∈ (⊥ : SubgroupFunctor G).carrier (specTest k K) :=
      fun y => by
        simp only [F₁, pointCoords_eq_zero_iff, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
        constructor
        · rintro rfl
          exact MonObj.one_comp _
        · intro h
          apply (cancel_mono jU.hom.hom).mp
          rw [h, MonObj.one_comp]
    have hF₁σ : ∀ σ : K ≃ₐ[k] K, ∀ y, F₁ (specAut k K σ ≫ y) = fun l => σ (F₁ y l) :=
      fun σ y => pointCoords_specAut eU heU.1 σ y
    have hF₁t : ∀ (s : specTest k K ⟶ S.X) y,
        F₁ ((RelativeRoot.subgroupAction iS α jU hjU).act s y) =
          (Lie.characterValue α s : K) • F₁ y := fun s y => pointCoords_act eU heU s y
    refine ⟨n, 0, 2, rationalCoords jU F₁, fun _ => 0, Or.inr rfl,
      fun x hx y hy => rationalCoords_mul iS α hjU F₁ hF₁mul hx hy,
      fun x hx => ?_, fun x _ y _ => Subsingleton.elim _ _, fun x hx _ => ?_,
      fun σ x hx => rationalConjugate_mem iS α hjU σ hx,
      fun σ x hx => rationalCoords_rationalConjugate iS α hjU F₁ hF₁σ σ hx,
      fun σ x _ => Subsingleton.elim _ _, fun c hc => ?_⟩
    · rw [rationalCoords_eq_zero_iff iS α hjU F₁ ⊥ hF₁0 hx, hdbl, SubgroupFunctor.bot_carrier,
        Subgroup.mem_bot, Subgroup.mem_bot]
      constructor
      · intro h
        exact (baseChangeCoeffEquiv k K G).injective (h.trans (map_one _).symm)
      · rintro rfl
        exact map_one _
    · rw [hdbl] at hx
      exact (Subgroup.mem_bot).mp hx
    · obtain ⟨t, ht, hσ, hΨ⟩ := exists_unitCocharacterPoint (k := k) iS ν v hc
      refine ⟨t, ht, hσ, fun x hx => ?_, fun x _ => Subsingleton.elim _ _⟩
      obtain ⟨hmem, hval⟩ := rationalCoords_conj iS α hjU F₁ hF₁t hΨ hx
      refine ⟨hmem, ?_⟩
      rw [hval, characterValue_unitCocharacterPoint, hν]
      norm_cast

end Main

end Langlands.Geometry.Building
