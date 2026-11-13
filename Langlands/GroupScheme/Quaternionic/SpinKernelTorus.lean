import Langlands.GroupScheme.CentralIsogeny.IndexTwoKernel
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Reductive.RootDatum

/-! # The kernel of a torus map with even cocharacter image

If `t : T ⟶ 𝔾_m^l` maps the cocharacters of a split torus `T` isomorphically onto the
even-sum lattice, and the cocharacter `c` maps to `2 e_{i₀}`, then on every test object
the points of `T` killed by `t` are exactly the images `u ≫ c` of the square roots of
unity `u`, and `u ↦ u ≫ c` is injective. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernelTorus

variable {k : Type u} [Field k] {l : Type} [Fintype l] [DecidableEq l]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- The hypotheses on a torus map `t : T ⟶ 𝔻` into the split diagonal torus: on
cocharacters it is injective with even coordinate sums, every vector `eᵢ - e_{i₀}` is
in its image, and the cocharacter `c` maps to `2 e_{i₀}`. -/
structure EvenImage (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ 𝔻)
    (c : cocharacterLattice T) (i₀ : l) : Prop where
  injective : Function.Injective fun ν : cocharacterLattice T => ν ≫ t
  even : ∀ ν : cocharacterLattice T,
    Even (∑ i, GeneralLinear.cocharacterCoordEquiv l k (ν ≫ t) i)
  exists_single_sub : ∀ i : l, ∃ ν : cocharacterLattice T,
    GeneralLinear.cocharacterCoordEquiv l k (ν ≫ t) = Pi.single i 1 - Pi.single i₀ 1
  coord_c : GeneralLinear.cocharacterCoordEquiv l k (c ≫ t) = Pi.single i₀ 2

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {t : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} l)}
  {c : cocharacterLattice T} {i₀ : l}

/-- Half of an integral linear form all of whose values are even. -/
def halfForm {M : Type*} [AddCommGroup M] (f : M →ₗ[ℤ] ℤ) (h : ∀ x, (2 : ℤ) ∣ f x) :
    M →ₗ[ℤ] ℤ := IndexTwoKernel.halfForm f h

theorem two_mul_halfForm {M : Type*} [AddCommGroup M] (f : M →ₗ[ℤ] ℤ)
    (h : ∀ x, (2 : ℤ) ∣ f x) (x : M) : 2 * halfForm f h x = f x :=
  IndexTwoKernel.two_mul_halfForm f h x

/-- An even-sum integer vector in the basis `eᵢ - e_{i₀}`, `2 e_{i₀}`. -/
theorem vector_decomp (v : l → ℤ) (s : ℤ) (i₀ : l) (hs : 2 * s = ∑ i, v i) :
    ∑ i, v i • (Pi.single i 1 - Pi.single i₀ 1 : l → ℤ) + s • Pi.single i₀ 2 = v := by
  funext j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  by_cases hj : j = i₀
  · subst hj
    simp only [ite_true]
    linarith
  · simp [hj]

omit [DecidableEq l] in
/-- The coordinate sum of the image of a cocharacter, as a linear form. -/
def coordSum (t : T ⟶ 𝔻) : cocharacterLattice T →ₗ[ℤ] ℤ where
  toFun ν := ∑ i, GeneralLinear.cocharacterCoordEquiv l k (ν ≫ t) i
  map_add' ν ν' := by
    rw [Preadditive.add_comp, map_add, ← Finset.sum_add_distrib]
    rfl
  map_smul' m ν := by
    rw [Preadditive.zsmul_comp, map_zsmul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    rfl

omit [DecidableEq l] in
theorem coordSum_apply (t : T ⟶ 𝔻) (ν : cocharacterLattice T) :
    coordSum t ν = ∑ i, GeneralLinear.cocharacterCoordEquiv l k (ν ≫ t) i := rfl

namespace EvenImage

variable (h : EvenImage T t c i₀)
include h

theorem two_dvd_coordSum (ν : cocharacterLattice T) : (2 : ℤ) ∣ coordSum t ν := by
  rw [coordSum_apply]
  exact even_iff_two_dvd.mp (h.even ν)

/-- Half the coordinate sum, a linear form since every coordinate sum is even. -/
def halfSum : cocharacterLattice T →ₗ[ℤ] ℤ :=
  halfForm (coordSum t) h.two_dvd_coordSum

theorem halfSum_apply (ν : cocharacterLattice T) : h.halfSum ν = coordSum t ν / 2 := rfl

theorem two_mul_halfSum (ν : cocharacterLattice T) :
    2 * h.halfSum ν = coordSum t ν :=
  two_mul_halfForm _ _ ν

theorem halfSum_c : h.halfSum c = 1 := by
  rw [halfSum_apply, coordSum_apply, h.coord_c]
  simp

/-! ### The half-sum character -/

variable (hT : IsSplitTorus T.toGrp)
include hT

/-- The character pairing to half the coordinate sum, from the perfect pairing. -/
def halfChar : characterLattice T :=
  (hT.isPerfPair_latticePairing.bijective_left.2 h.halfSum).choose

theorem latticePairing_halfChar (ν : cocharacterLattice T) :
    latticePairing T (h.halfChar hT) ν = h.halfSum ν :=
  LinearMap.congr_fun (hT.isPerfPair_latticePairing.bijective_left.2 h.halfSum).choose_spec ν

omit [DecidableEq l] h hT in
theorem latticePairing_comp (φ : characterLattice 𝔻) (ν : cocharacterLattice T) :
    latticePairing T (t ≫ φ) ν = ∑ i, GeneralLinear.characterCoordEquiv l k φ i *
      GeneralLinear.cocharacterCoordEquiv l k (ν ≫ t) i := by
  rw [← GeneralLinear.latticePairing_coord, latticePairing_apply, latticePairing_apply,
    Category.assoc]

omit h in
theorem character_ext {ψ ψ' : characterLattice T}
    (hψ : ∀ ν : cocharacterLattice T, latticePairing T ψ ν = latticePairing T ψ' ν) :
    ψ = ψ' :=
  hT.isPerfPair_latticePairing.bijective_left.1 (LinearMap.ext hψ)

/-- The half-sum character takes the value one on `c`. -/
theorem c_comp_halfChar : c ≫ h.halfChar hT = 𝟙 (Gm (Spec (CommRingCat.of k))) := by
  apply (gmEndEquiv k).injective
  rw [gmEndEquiv_id, ← latticePairing_apply, latticePairing_halfChar, halfSum_c]

/-- Twice the half-sum character is pulled back from the coordinate sum character. -/
theorem two_smul_halfChar :
    (2 : ℤ) • h.halfChar hT =
      t ≫ (GeneralLinear.characterCoordEquiv l k).symm (fun _ => 1) := by
  apply character_ext hT
  intro ν
  rw [map_zsmul, LinearMap.smul_apply, latticePairing_halfChar, smul_eq_mul, two_mul_halfSum,
    latticePairing_comp, coordSum_apply]
  simp

/-- Every character is a pullback from the diagonal torus plus a multiple of the
half-sum character. -/
theorem exists_eq_comp_add (ψ : characterLattice T) :
    ∃ φ : characterLattice 𝔻, ψ = t ≫ φ + latticePairing T ψ c • h.halfChar hT := by
  choose ν hν using h.exists_single_sub
  refine ⟨(GeneralLinear.characterCoordEquiv l k).symm fun i => latticePairing T ψ (ν i), ?_⟩
  apply character_ext hT
  intro w
  set v := GeneralLinear.cocharacterCoordEquiv l k (w ≫ t) with hv
  have hw : w = ∑ i, v i • ν i + h.halfSum w • c := by
    apply h.injective
    apply (GeneralLinear.cocharacterCoordEquiv l k).injective
    simp only [Preadditive.add_comp, Preadditive.sum_comp, Preadditive.zsmul_comp, map_add,
      map_sum, map_zsmul, hν, h.coord_c]
    rw [← hv]
    exact (vector_decomp v (h.halfSum w) i₀ (by rw [two_mul_halfSum, coordSum_apply])).symm
  rw [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, latticePairing_halfChar,
    latticePairing_comp, LinearEquiv.apply_symm_apply, ← hv, smul_eq_mul]
  conv_lhs => rw [hw]
  rw [map_add, map_sum, map_zsmul]
  simp only [map_zsmul, smul_eq_mul, mul_comm (v _)]
  ring

/-! ### Points of the kernel -/

/-- Every point killed by `t` is the image under `c` of a square root of unity. -/
theorem exists_comp_eq {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ T.X)
    (hx : x ≫ (CommGroupScheme.groupHom t).hom.hom = 1) :
    ∃ u : U ⟶ (Gm (Spec (CommRingCat.of k))).X,
      u * u = 1 ∧ u ≫ (CommGroupScheme.groupHom c).hom.hom = x := by
  have hone : ∀ φ : characterLattice 𝔻, x ≫ (CommGroupScheme.groupHom (t ≫ φ)).hom.hom = 1 := by
    intro φ
    rw [comp_groupHom_comp, hx, MonObj.one_comp]
  refine ⟨x ≫ (CommGroupScheme.groupHom (h.halfChar hT)).hom.hom, ?_, ?_⟩
  · have h2 := hone ((GeneralLinear.characterCoordEquiv l k).symm (fun _ => 1))
    rw [← h.two_smul_halfChar hT, comp_groupHom_zsmul] at h2
    rw [← h2, zpow_two]
  · apply hT.point_ext_characters
    intro ψ
    obtain ⟨φ, hφ⟩ := h.exists_eq_comp_add hT ψ
    rw [← comp_groupHom_comp, eq_gmEndEquiv_zsmul k (c ≫ ψ), Gm.comp_zsmul_id,
      ← latticePairing_apply]
    conv_rhs => rw [hφ, comp_groupHom_add, hone, one_mul, comp_groupHom_zsmul]

/-- A point of `𝔾_m` is recovered from its image under `c`. -/
theorem comp_injective {U : Over (Spec (CommRingCat.of k))} :
    Function.Injective fun u : U ⟶ (Gm (Spec (CommRingCat.of k))).X =>
      u ≫ (CommGroupScheme.groupHom c).hom.hom := by
  intro u u' huu
  have key : ∀ w : U ⟶ (Gm (Spec (CommRingCat.of k))).X,
      w = (w ≫ (CommGroupScheme.groupHom c).hom.hom) ≫
        (CommGroupScheme.groupHom (h.halfChar hT)).hom.hom := by
    intro w
    rw [← comp_groupHom_comp, h.c_comp_halfChar hT]
    rfl
  rw [key u, key u']
  exact congrArg (· ≫ (CommGroupScheme.groupHom (h.halfChar hT)).hom.hom) huu

end EvenImage

end Langlands.GroupScheme.Quaternionic.SpinKernelTorus
