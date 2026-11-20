import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy

/-! # Heights, twists and character lattices for the constant-term formula

* `IsIwasawaCompact.continuous_height`: the Iwasawa height `H_P` is continuous. The map
  `P(𝔸) × K → G(𝔸)`, `(q, k) ↦ p(q) k` is a continuous closed surjection (as `K` is compact and
  `p` a closed embedding), hence a quotient map, and `H_P` composed with it is `log_P ∘ pr₁`.
* `IsIwasawaCompact.heightPower_restrict`: for `f : P' → P` and `K` Iwasawa for both `P` and
  `P'`, `m_{P'}(g)^{λ ∘ f} = m_P(g)^λ` (Bernstein–Lapid §6.10 regard `X_P ⊆ X_{P'}`).
* `rationalCharacters_free_finite`: the rational characters of a smooth connected affine group
  over a field form a free `ℤ`-module of finite rank. The proof is the Library's proof of
  `rationalCharacterLattice` (`CharacterLatticeProof`), which uses only these hypotheses.
* `exists_complexParameterEquiv`: for a parabolic `P` of a connected reductive `G`, the space
  `X^*(P) ⊗ ℂ` has linear coordinates `ℂⁿ ≃ X^*(P) ⊗ ℂ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
variable {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
variable {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The multiplication map `P(𝔸) × K → G(𝔸)` is a closed map. -/
theorem IsIwasawaCompact.isClosedMap_mul (hK : IsIwasawaCompact p K) :
    IsClosedMap (fun x : AdelicGroupPoints F P × K => map F P G p x.1 * (x.2 : AdelicGroupPoints F G)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have he : IsClosedMap (fun x : AdelicGroupPoints F P × K => (map F P G p x.1, x.2)) :=
    ((isClosedEmbedding_map F P G p).prodMap Topology.IsClosedEmbedding.id).isClosedMap
  let s : AdelicGroupPoints F G × K ≃ₜ AdelicGroupPoints F G × K :=
    { toFun := fun x => (x.1 * (x.2 : AdelicGroupPoints F G), x.2)
      invFun := fun x => (x.1 * (x.2 : AdelicGroupPoints F G)⁻¹, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk
        continuous_snd
      continuous_invFun := (continuous_fst.mul
        (continuous_subtype_val.comp continuous_snd).inv).prodMk continuous_snd }
  have hfst : IsClosedMap (Prod.fst : AdelicGroupPoints F G × K → AdelicGroupPoints F G) :=
    isClosedMap_fst_of_compactSpace
  have := hfst.comp (s.isClosedMap.comp he)
  exact this

omit [NumberField F] [IsAffine P.X.left] in
/-- The pairing `H ↦ ⟨λ, H⟩` is continuous on `Hom(X^*(P), ℝ)`. -/
theorem continuous_complexParameterPairing (lam : ComplexCharacterParameter F P) :
    Continuous (complexParameterPairing F P lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    have : (complexParameterPairing F P (s ⊗ₜ[ℤ] χ) : RealCharacterDual F P → ℂ) =
        fun H => s * ((dualEval F P χ H : ℝ) : ℂ) := by
      funext H
      rfl
    rw [this]
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dualEval F P χ))
  | add x y hx hy =>
    rw [map_add, LinearMap.coe_add]
    exact hx.add hy

/-- The factor `g ↦ m_P(g)^λ` is continuous. -/
theorem IsIwasawaCompact.continuous_heightPower (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) : Continuous (hK.heightPower lam) :=
  Complex.continuous_exp.comp ((continuous_complexParameterPairing lam).comp hK.continuous_height)

/-- The twist of a continuous function is continuous. -/
theorem IsIwasawaCompact.continuous_parameterTwist (hK : IsIwasawaCompact p K)
    {φ : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ) (lam : ComplexCharacterParameter F P) :
    Continuous (hK.parameterTwist φ lam) :=
  hφ.mul (hK.continuous_heightPower lam)

omit [NumberField F] [IsAffine P.X.left] in
/-- Restriction of parameters is adjoint to the covariant map of real character duals. -/
theorem complexParameterPairing_parameterRestrict {P' : GroupScheme (Spec (CommRingCat.of F))}
    (f : P' ⟶ P) (lam : ComplexCharacterParameter F P) (H : RealCharacterDual F P') :
    complexParameterPairing F P' (parameterRestrict f lam) H =
      complexParameterPairing F P lam (realCharacterDualMap F P' P f H) := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- For `f : P' → P` and `K` an Iwasawa subgroup for `P'` (and `P`), the heights satisfy
`H_P = f_*(H_{P'})`. -/
theorem IsIwasawaCompact.height_eq_realCharacterDualMap (hK : IsIwasawaCompact p K)
    {P' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P'.X.left] (f : P' ⟶ P)
    [IsClosedImmersion (f ≫ p).hom.hom.left] (hK' : IsIwasawaCompact (f ≫ p) K)
    (g : AdelicGroupPoints F G) :
    hK.height g = realCharacterDualMap F P' P f (hK'.height g) := by
  obtain ⟨q, k, hk, rfl⟩ := hK'.exists_eq g
  rw [hK'.height_eq hk rfl, map_comp_apply_of_hom, hK.height_eq hk rfl, characterLog_map]

/-- Twist matching: `m_{P'}(g)^{λ ∘ f} = m_P(g)^λ`. -/
theorem IsIwasawaCompact.heightPower_restrict (hK : IsIwasawaCompact p K)
    {P' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P'.X.left] (f : P' ⟶ P)
    [IsClosedImmersion (f ≫ p).hom.hom.left] (hK' : IsIwasawaCompact (f ≫ p) K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.heightPower (parameterRestrict f lam) g = hK.heightPower lam g := by
  rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower,
    complexParameterPairing_parameterRestrict, ← hK.height_eq_realCharacterDualMap f hK' g]

/-- Left translation by adelic points of a unipotent subgroup of `P` does not change
`m_P(g)^λ`. -/
theorem IsIwasawaCompact.heightPower_unipotent_mul (hK : IsIwasawaCompact p K)
    {U : GroupScheme (Spec (CommRingCat.of F))} (hU : IsUnipotent U) (iU : U ⟶ P)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F U) (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F U G (iU ≫ p) x * g) = hK.heightPower lam g := by
  rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, map_comp_apply_of_hom,
    hK.height_unipotent_mul hU]

/-- Left translation by rational points of `P` does not change `m_P(g)^λ`. -/
theorem IsIwasawaCompact.heightPower_rational_mul (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (q₀ : RationalGroupPoints F P)
    (g : AdelicGroupPoints F G) :
    hK.heightPower lam (map F P G p (rational F P q₀) * g) = hK.heightPower lam g := by
  rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, hK.height_rational_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.GroupScheme

open CharacterLatticeProof CharacterUnits CharacterLattice in
/-- Over a field, the rational characters of a smooth connected affine group form a free
`ℤ`-module of finite rank. This is the proof of `rationalCharacterLattice`, which uses only
smoothness, affineness and connectedness. -/
theorem rationalCharacters_free_finite {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] :
    Module.Free ℤ (rationalCharacters G) ∧ Module.Finite ℤ (rationalCharacters G) := by
  classical
  have := isDomain_coord G
  let K : Type u := CommRingCat.of k
  let _ : Field K := inferInstanceAs (Field k)
  set D := Coord G
  set L := FractionRing D
  let w : Multiplicative (rationalCharacters G) →* L :=
    { toFun := fun χ => algebraMap D L (unit χ.toAdd : D)
      map_one' := by simp [unit_zero]
      map_mul' := fun a b => by simp [toAdd_mul, unit_add] }
  have hw : LinearIndependent K (wa w) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K D L) :=
      IsFractionRing.injective D L
    exact (linearIndependent_unit (G := G)).map' (IsScalarTower.toAlgHom K D L).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨s, hs⟩ := (Lie.coordinateAlgebraFiniteType G).out
  refine free_and_finite (k := K) w hw (s.image (algebraMap D L)) fun χ => ?_
  change algebraMap D L (unit χ : D) ∈ _
  rw [Finset.coe_image, ← IsScalarTower.coe_toAlgHom' K D L, Algebra.adjoin_image]
  exact Subalgebra.mem_map.mpr ⟨_, hs ▸ Algebra.mem_top, rfl⟩

/-- The rational characters of a parabolic subgroup of a connected reductive group form a
finitely generated `ℤ`-module. -/
theorem IsParabolicSubgroup.finite_rationalCharacters {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    [IsAffine P.X.left] {p : P ⟶ G} (hp : IsParabolicSubgroup p) :
    Module.Finite ℤ (rationalCharacters P) := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : Smooth P.X.hom := hp.smooth
  have : ConnectedSpace P.X.left := hp.connectedSpace
  have : IsAffineHom P.X.hom := inferInstance
  exact (rationalCharacters_free_finite P).2

end Langlands.GroupScheme

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- Linear coordinates `ℂⁿ ≃ X^*(P) ⊗ ℂ` for a parabolic `P` of a connected reductive `G`. -/
theorem exists_complexParameterEquiv {F : Type u} [Field F] [NumberField F]
    {G P : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    [IsAffine P.X.left] {p : P ⟶ G} (hp : IsParabolicSubgroup p) :
    ∃ n : ℕ, Nonempty ((Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) := by
  have := hp.finite_rationalCharacters hG
  exact ⟨_, ⟨(Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm⟩⟩

end Langlands.Global.AdelicGroupPoints
