import Langlands.Shimura.PEL.HarrisTaylorCMScaledLevels
import Langlands.Shimura.RestrictedLevelColimit
import Mathlib.CategoryTheory.Linear.Basic

/-! # Descent from scaled levels to levels

A presheaf `G` on scaled CM levels with values in a linear category over a field `Λ`, together
with isomorphisms `ψ_X : G(X) ≅ O(X.level)` to objects attached to the levels alone, gives maps
`T(f) = ψ_Y⁻¹ ≫ G(f) ≫ ψ_X : O(Y.level) ⟶ O(X.level)` for morphisms `f : X ⟶ Y` of scaled
levels. If raising an exponent from `n` to `n'` acts on `T` by `ℓ ^ (n' - n)` and shifting both
exponents does not change `T`, the rescaled maps `(ℓ ^ e_b)⁻¹ • T(f_b)` form a presheaf on small
CM levels, where `e_b` is the least admissible exponent of the transporter `b` and
`f_b : ⟨V, 0⟩ ⟶ ⟨U, e_b⟩` is `b` with these exponents. If moreover `T(f) = 𝟙` for every
self-morphism of a scaled level by an element of the level, this presheaf is level-trivial.
See `HarrisTaylorCMScaledDescent.md`.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.Global Langlands.Shimura.Coefficients
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {d : ℕ} (D : CentralSimpleUnitaryData E F A d)

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ)

/-! ## Least admissible exponents -/

open Classical in
/-- The least admissible exponent of a transporter `b : V ⟶ U` of small CM levels: the least
`e` such that `x ↦ ℓ^e ρ(ι b) x` maps Harris's lattice of `U` into that of `V`. -/
def cmHarrisLatticeExponent {V U : SmallCMLevel D} (b : V ⟶ U) : ℕ :=
  Nat.find (exists_cmHarrisLatticeScaled D ρ p b)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
open Classical in
theorem cmHarrisLatticeScaled_exponent {V U : SmallCMLevel D} (b : V ⟶ U) :
    CMHarrisLatticeScaled D ρ p b (cmHarrisLatticeExponent D ρ p b) :=
  Nat.find_spec (exists_cmHarrisLatticeScaled D ρ p b)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
open Classical in
theorem cmHarrisLatticeExponent_le {V U : SmallCMLevel D} (b : V ⟶ U) {e : ℕ}
    (he : CMHarrisLatticeScaled D ρ p b e) : cmHarrisLatticeExponent D ρ p b ≤ e :=
  Nat.find_min' (exists_cmHarrisLatticeScaled D ρ p b) he

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- A transporter `U ⟶ U` by an element of `U` preserves Harris's lattice of `U`: the exponent
`0` is admissible. -/
theorem cmHarrisLatticeScaled_zero_of_mem {U : SmallCMLevel D} (b : U ⟶ U)
    (hb : b.hom.element ∈ U.obj.subgroup) : CMHarrisLatticeScaled D ρ p b 0 := by
  intro x hx
  rw [pow_zero, one_smul]
  have hmem : smallCMArrowElement D b ∈ (inverseOpposite U.obj).subgroup := by
    rw [mem_inverseOpposite]
    simpa [smallCMArrowElement] using hb
  exact harrisLattice_stable ρ p (inverseOpposite U.obj) ⟨_, hmem⟩ x hx

/-- The morphism `⟨V, 0⟩ ⟶ ⟨U, e_b⟩` of scaled levels given by a transporter `b : V ⟶ U` and its
least admissible exponent `e_b`. -/
def cmScaledLevelLeast {V U : SmallCMLevel D} (b : V ⟶ U) :
    (⟨V, 0⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, cmHarrisLatticeExponent D ρ p b⟩ :=
  ⟨b, Nat.zero_le _, cmHarrisLatticeScaled_exponent D ρ p b⟩

/-! ## Transport through identifications with the levels -/

section Descent

variable {C : Type*} [Category C] {Λ : Type*} [Field Λ]
  (G : (CMScaledLevel D ρ p)ᵒᵖ ⥤ C) (O : SmallCMLevel D → C)
  (ψ : ∀ X : CMScaledLevel D ρ p, G.obj (op X) ≅ O X.level)

/-- The map `ψ_Y⁻¹ ≫ G(f) ≫ ψ_X : O(Y.level) ⟶ O(X.level)` of a morphism `f : X ⟶ Y` of scaled
levels. -/
def cmScaledTransport {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) : O Y.level ⟶ O X.level :=
  (ψ Y).inv ≫ G.map f.op ≫ (ψ X).hom

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
theorem cmScaledTransport_id (X : CMScaledLevel D ρ p) :
    cmScaledTransport D ρ p G O ψ (𝟙 X) = 𝟙 _ := by
  simp [cmScaledTransport]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
theorem cmScaledTransport_comp {X Y Z : CMScaledLevel D ρ p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cmScaledTransport D ρ p G O ψ (f ≫ g) =
      cmScaledTransport D ρ p G O ψ g ≫ cmScaledTransport D ρ p G O ψ f := by
  simp [cmScaledTransport]

/-- Shifting both exponents of a morphism of scaled levels does not change its map. -/
def CMScaledTransportShift : Prop :=
  ∀ {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k : ℕ),
    cmScaledTransport D ρ p G O ψ (CMScaledLevel.Hom.shift D ρ p f k) =
      cmScaledTransport D ρ p G O ψ f

/-- Self-morphisms of scaled levels by elements of the level act trivially. -/
def CMScaledTransportLevelTrivial : Prop :=
  ∀ (Y : CMScaledLevel D ρ p) (f : Y ⟶ Y),
    (CMScaledLevel.Hom.hom f).hom.element ∈ Y.level.obj.subgroup →
      cmScaledTransport D ρ p G O ψ f = 𝟙 _

variable [Preadditive C] [Linear Λ C]

variable (Λ) in
/-- Raising the exponent of a level from `n` to `n'` acts by `ℓ ^ (n' - n)`. -/
def CMScaledTransportRaise : Prop :=
  ∀ (U : SmallCMLevel D) {n n' : ℕ} (h : n ≤ n'),
    cmScaledTransport D ρ p G O ψ (CMScaledLevel.raise D ρ p U h) =
      ((harrisCoefficientPrime p : Λ) ^ (n' - n)) • 𝟙 (O U)

variable (Λ) in
/-- The rescaled map `(ℓ ^ e_b)⁻¹ • T(f_b)` of a transporter `b : V ⟶ U` of small CM levels. -/
def cmScaledDescentMap {V U : SmallCMLevel D} (b : V ⟶ U) : O U ⟶ O V :=
  ((harrisCoefficientPrime p : Λ) ^ cmHarrisLatticeExponent D ρ p b)⁻¹ •
    cmScaledTransport D ρ p G O ψ (cmScaledLevelLeast D ρ p b)

variable {G O ψ}
variable (hℓ : (harrisCoefficientPrime p : Λ) ≠ 0)
  (hraise : CMScaledTransportRaise D ρ p Λ G O ψ) (hshift : CMScaledTransportShift D ρ p G O ψ)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
include hℓ hraise hshift in
/-- The rescaled map of `b` may be computed with any morphism `g : ⟨V, n⟩ ⟶ ⟨U, n'⟩` of scaled
levels with transporter `b`: it is `(ℓ ^ (n' - n))⁻¹ • T(g)`. -/
theorem cmScaledDescentMap_eq {V U : SmallCMLevel D} (b : V ⟶ U) {n n' : ℕ}
    (g : (⟨V, n⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, n'⟩) (hg : CMScaledLevel.Hom.hom g = b) :
    cmScaledDescentMap D ρ p Λ G O ψ b =
      ((harrisCoefficientPrime p : Λ) ^ (n' - n))⁻¹ • cmScaledTransport D ρ p G O ψ g := by
  subst hg
  set e := cmHarrisLatticeExponent D ρ p (CMScaledLevel.Hom.hom g) with he_def
  have hle : e ≤ n' - n := cmHarrisLatticeExponent_le D ρ p _ (CMScaledLevel.Hom.scaled g)
  have hn : n ≤ n' := CMScaledLevel.Hom.le g
  have hfac : g = CMScaledLevel.Hom.shift D ρ p (cmScaledLevelLeast D ρ p
      (CMScaledLevel.Hom.hom g)) n ≫ CMScaledLevel.raise D ρ p U (by omega : n + e ≤ n') := by
    apply CMScaledLevel.Hom.ext
    exact (Category.comp_id _).symm
  have hT : cmScaledTransport D ρ p G O ψ g =
      ((harrisCoefficientPrime p : Λ) ^ (n' - (n + e))) •
        cmScaledTransport D ρ p G O ψ (cmScaledLevelLeast D ρ p (CMScaledLevel.Hom.hom g)) := by
    conv_lhs => rw [hfac]
    rw [cmScaledTransport_comp, hraise, hshift, Linear.smul_comp, Category.id_comp]
  rw [hT, smul_smul, cmScaledDescentMap]
  congr 1
  have hsplit : n' - n = (n' - (n + e)) + e := by omega
  rw [hsplit, pow_add, mul_inv, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ hℓ), one_mul]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
include hℓ hraise hshift in
theorem cmScaledDescentMap_id (U : SmallCMLevel D) :
    cmScaledDescentMap D ρ p Λ G O ψ (𝟙 U) = 𝟙 _ := by
  rw [cmScaledDescentMap_eq D ρ p hℓ hraise hshift (𝟙 U) (𝟙 (⟨U, 0⟩ : CMScaledLevel D ρ p)) rfl,
    cmScaledTransport_id]
  simp

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
include hℓ hraise hshift in
theorem cmScaledDescentMap_comp {W' V U : SmallCMLevel D} (c : W' ⟶ V) (b : V ⟶ U) :
    cmScaledDescentMap D ρ p Λ G O ψ (c ≫ b) =
      cmScaledDescentMap D ρ p Λ G O ψ b ≫
        cmScaledDescentMap D ρ p Λ G O ψ c := by
  rw [cmScaledDescentMap_eq D ρ p hℓ hraise hshift (c ≫ b)
    (cmScaledLevelLeast D ρ p c ≫ CMScaledLevel.Hom.shift D ρ p (cmScaledLevelLeast D ρ p b)
      (cmHarrisLatticeExponent D ρ p c)) rfl,
    cmScaledTransport_comp, hshift, cmScaledDescentMap, cmScaledDescentMap, Linear.smul_comp,
    Linear.comp_smul, smul_smul, Nat.sub_zero, pow_add, mul_inv, mul_comm]

/-- The presheaf on small CM levels obtained from `G` and the identifications `ψ` by rescaling
the maps of least admissible exponents. Its value at `U` is `O U`. -/
@[simps!]
def cmScaledDescent : (SmallCMLevel D)ᵒᵖ ⥤ C where
  obj U := O U.unop
  map b := cmScaledDescentMap D ρ p Λ G O ψ b.unop
  map_id U := cmScaledDescentMap_id D ρ p hℓ hraise hshift U.unop
  map_comp b c := cmScaledDescentMap_comp D ρ p hℓ hraise hshift c.unop b.unop

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
include hℓ hraise hshift in
/-- If self-morphisms of scaled levels by elements of the level act trivially, the descended
presheaf is level-trivial. -/
theorem isLevelTrivial_cmScaledDescent (htriv : CMScaledTransportLevelTrivial D ρ p G O ψ) :
    IsLevelTrivial (cmScaledDescent D ρ p hℓ hraise hshift) := by
  intro U k hk
  change cmScaledDescentMap D ρ p Λ G O ψ (restrictedSelfArrow _ U k hk) = _
  rw [cmScaledDescentMap_eq D ρ p hℓ hraise hshift (restrictedSelfArrow _ U k hk)
    (⟨restrictedSelfArrow _ U k hk, le_rfl,
      cmHarrisLatticeScaled_zero_of_mem D ρ p _ hk⟩ :
        (⟨U, 0⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, 0⟩) rfl,
    htriv _ _ hk]
  simp
  rfl

end Descent

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
